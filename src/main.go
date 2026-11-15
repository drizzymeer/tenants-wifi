package main

import (
	"context"
	"crypto/rand"
	"crypto/sha256"
	"crypto/subtle"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"html/template"
	"log"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
)

const (
	lanDev = "br-lan"
	ifbDev = "ifb0"
)

type Voucher struct {
	Key       string `json:"key"`
	Name      string `json:"name"`
	Minutes   int    `json:"minutes"`
	DownKbps  int    `json:"down_kbps"`
	UpKbps    int    `json:"up_kbps"`
	MAC       string `json:"mac"`
	IP        string `json:"ip"`
	Started   int64  `json:"started"`
	Expires   int64  `json:"expires"`
	Remaining int64  `json:"remaining"`
	Paused    bool   `json:"paused"`
	Disabled  bool   `json:"disabled"`
}

type TrustedDevice struct {
	MAC      string `json:"mac"`
	Name     string `json:"name"`
	UpKbps   int    `json:"up_kbps"`
	DownKbps int    `json:"down_kbps"`
}

type Store struct {
	Vouchers map[string]*Voucher `json:"vouchers"`
	Trusted  []*TrustedDevice    `json:"trusted,omitempty"`
}

var mu sync.Mutex
var db Store
var dataPath string
var ndsctl string
var adminPass string
var fasKey string
var gatewayPort string
var fasSessions = map[string]fasSession{}

type fasSession struct {
	IP, MAC, HID, Gateway, Authdir string
	Until                          time.Time
}

var keyRx = regexp.MustCompile(`^[A-Za-z0-9_-]{4,64}$`)
var macRx = regexp.MustCompile(`(?i)^[0-9a-f]{2}(:[0-9a-f]{2}){5}$`)
var hidRx = regexp.MustCompile(`^[a-fA-F0-9]{64}$`)
var authdirRx = regexp.MustCompile(`^[a-zA-Z0-9_-]{1,48}$`)

func save() error {
	b, e := json.MarshalIndent(db, "", "  ")
	if e != nil {
		return e
	}
	dir := filepath.Dir(dataPath)
	if e = os.MkdirAll(dir, 0700); e != nil {
		return e
	}
	tmp := dataPath + ".tmp"
	if e = os.WriteFile(tmp, b, 0600); e != nil {
		return e
	}
	return os.Rename(tmp, dataPath)
}

func load() {
	db.Vouchers = map[string]*Voucher{}
	b, e := os.ReadFile(dataPath)
	if e == nil {
		if e = json.Unmarshal(b, &db); e != nil {
			log.Fatalf("invalid database: %v", e)
		}
	}
	if db.Vouchers == nil {
		db.Vouchers = map[string]*Voucher{}
	}
}

func respond(w http.ResponseWriter, status int, obj any) {
	w.Header().Set("Content-Type", "application/json")
	w.Header().Set("Cache-Control", "no-store")
	w.WriteHeader(status)
	_ = json.NewEncoder(w).Encode(obj)
}

func fail(w http.ResponseWriter, status int, msg string) {
	respond(w, status, map[string]string{"error": msg})
}

func basicAuth(r *http.Request) bool {
	u, p, ok := r.BasicAuth()
	return ok && subtle.ConstantTimeCompare([]byte(u), []byte("admin")) == 1 && subtle.ConstantTimeCompare([]byte(p), []byte(adminPass)) == 1
}

func admin(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if !basicAuth(r) {
			w.Header().Set("WWW-Authenticate", `Basic realm="Tenants WiFi Admin"`)
			http.Error(w, "Authentication required", 401)
			return
		}
		if r.Method != "GET" && r.Header.Get("X-Tenants-Admin") != "1" {
			fail(w, 403, "missing admin request header")
			return
		}
		next(w, r)
	}
}

func ipOf(r *http.Request) string {
	host, _, e := net.SplitHostPort(r.RemoteAddr)
	if e != nil {
		return ""
	}
	ip := net.ParseIP(host)
	if ip == nil || ip.To4() == nil {
		return ""
	}
	return ip.String()
}

func nds(args ...string) error {
	ctx, cancel := context.WithTimeout(context.Background(), 4*time.Second)
	defer cancel()
	cmd := exec.CommandContext(ctx, ndsctl, args...)
	out, e := cmd.CombinedOutput()
	if e != nil {
		return fmt.Errorf("ndsctl: %v: %s", e, strings.TrimSpace(string(out)))
	}
	return nil
}

func isAuthenticated(mac string) bool {
	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Second)
	defer cancel()
	out, err := exec.CommandContext(ctx, ndsctl, "json", mac).CombinedOutput()
	if err != nil {
		return false
	}
	var obj map[string]any
	if json.Unmarshal(out, &obj) != nil {
		return false
	}
	if s, ok := obj["state"].(string); ok && s == "Authenticated" {
		return true
	}
	return false
}

func macFor(ip string) (string, error) {
	if net.ParseIP(ip) == nil {
		return "", errors.New("invalid IP")
	}
	ctx, cancel := context.WithTimeout(context.Background(), 4*time.Second)
	defer cancel()
	b, e := exec.CommandContext(ctx, ndsctl, "json", ip).CombinedOutput()
	if e != nil {
		return "", fmt.Errorf("OpenNDS does not recognize this client: %s", strings.TrimSpace(string(b)))
	}
	var obj any
	if json.Unmarshal(b, &obj) != nil {
		return "", errors.New("cannot parse OpenNDS client record")
	}
	var walk func(any) string
	walk = func(v any) string {
		switch x := v.(type) {
		case map[string]any:
			for k, val := range x {
				if strings.EqualFold(k, "mac") || strings.EqualFold(k, "macaddress") {
					if s, ok := val.(string); ok && macRx.MatchString(s) {
						return strings.ToLower(s)
					}
				}
			}
			for _, val := range x {
				if s := walk(val); s != "" {
					return s
				}
			}
		case []any:
			for _, val := range x {
				if s := walk(val); s != "" {
					return s
				}
			}
		}
		return ""
	}
	m := walk(obj)
	if m == "" {
		return "", errors.New("client MAC not found in OpenNDS record")
	}
	return m, nil
}

func findTrusted(mac string) *TrustedDevice {
	for _, t := range db.Trusted {
		if strings.EqualFold(t.MAC, mac) {
			return t
		}
	}
	return nil
}

func sh(cmd string, args ...string) (string, error) {
	out, err := exec.Command(cmd, args...).CombinedOutput()
	return string(out), err
}

func ensureIFB() {
	if _, err := sh("ip", "link", "show", ifbDev); err != nil {
		sh("modprobe", "ifb")
		sh("ip", "link", "add", ifbDev, "type", "ifb")
	}
	sh("ip", "link", "set", ifbDev, "up")
	for _, dev := range []string{lanDev, ifbDev} {
		sh("tc", "qdisc", "replace", "dev", dev, "root", "handle", "1:", "htb", "default", "1")
	}
	sh("tc", "qdisc", "replace", "dev", lanDev, "handle", "ffff:", "ingress")
	sh("tc", "filter", "replace", "dev", lanDev, "parent", "ffff:", "protocol", "all",
		"u32", "match", "u32", "0", "0", "action", "mirred", "egress", "redirect", "dev", ifbDev)
}

func clsID(mac string) string {
	clean := strings.ReplaceAll(strings.ReplaceAll(mac, ":", ""), "-", "")
	if len(clean) >= 4 {
		return "1:" + clean[len(clean)-4:]
	}
	return "1:1"
}

func tcApply(mac string, upKbps, downKbps int) {
	id := clsID(mac)
	if downKbps > 0 {
		sh("tc", "class", "replace", "dev", lanDev, "parent", "1:", "classid", id,
			"htb", "rate", fmt.Sprintf("%dkbit", downKbps), "ceil", fmt.Sprintf("%dkbit", downKbps))
		sh("tc", "filter", "replace", "dev", lanDev, "parent", "1:", "protocol", "ip", "flower",
			"dst_mac", mac, "flowid", id)
	}
	if upKbps > 0 {
		sh("tc", "class", "replace", "dev", ifbDev, "parent", "1:", "classid", id,
			"htb", "rate", fmt.Sprintf("%dkbit", upKbps), "ceil", fmt.Sprintf("%dkbit", upKbps))
		sh("tc", "filter", "replace", "dev", ifbDev, "parent", "1:", "protocol", "ip", "flower",
			"src_mac", mac, "flowid", id)
	}
}

func tcRemove(mac string) {
	id := clsID(mac)
	sh("tc", "filter", "del", "dev", lanDev, "parent", "1:", "protocol", "ip", "flower", "dst_mac", mac)
	sh("tc", "class", "del", "dev", lanDev, "classid", id)
	sh("tc", "filter", "del", "dev", ifbDev, "parent", "1:", "protocol", "ip", "flower", "src_mac", mac)
	sh("tc", "class", "del", "dev", ifbDev, "classid", id)
}

func list(w http.ResponseWriter, r *http.Request) {
	mu.Lock()
	defer mu.Unlock()
	arr := make([]Voucher, 0, len(db.Vouchers))
	for _, v := range db.Vouchers {
		arr = append(arr, *v)
	}
	sort.Slice(arr, func(i, j int) bool { return arr[i].Key < arr[j].Key })
	respond(w, 200, arr)
}

func create(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		fail(w, 405, "POST required")
		return
	}
	var v Voucher
	if json.NewDecoder(http.MaxBytesReader(w, r.Body, 8192)).Decode(&v) != nil {
		fail(w, 400, "invalid JSON")
		return
	}
	v.Key = strings.TrimSpace(v.Key)
	v.Name = strings.TrimSpace(v.Name)
	if !keyRx.MatchString(v.Key) || v.Minutes < 1 || v.Minutes > 525600 || v.DownKbps < 0 || v.UpKbps < 0 || v.DownKbps > 10000000 || v.UpKbps > 10000000 || len(v.Name) > 80 {
		fail(w, 400, "invalid key, duration or speed")
		return
	}
	v.MAC = ""
	v.IP = ""
	v.Started = 0
	v.Expires = 0
	v.Remaining = 0
	v.Paused = false
	v.Disabled = false
	mu.Lock()
	defer mu.Unlock()
	if _, ok := db.Vouchers[v.Key]; ok {
		fail(w, 409, "voucher key already exists")
		return
	}
	db.Vouchers[v.Key] = &v
	if e := save(); e != nil {
		delete(db.Vouchers, v.Key)
		fail(w, 500, e.Error())
		return
	}
	respond(w, 201, v)
}

func action(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		fail(w, 405, "POST required")
		return
	}
	var q struct {
		Key     string `json:"key"`
		Action  string `json:"action"`
		Minutes int    `json:"minutes"`
	}
	if json.NewDecoder(http.MaxBytesReader(w, r.Body, 4096)).Decode(&q) != nil {
		fail(w, 400, "invalid JSON")
		return
	}
	mu.Lock()
	defer mu.Unlock()
	v, ok := db.Vouchers[q.Key]
	if !ok {
		fail(w, 404, "voucher not found")
		return
	}
	now := time.Now().Unix()
	switch q.Action {
	case "pause":
		if !v.Paused {
			if v.Started != 0 {
				v.Remaining = v.Expires - now
				if v.Remaining < 0 {
					v.Remaining = 0
				}
				if v.MAC != "" {
					_ = nds("deauth", v.MAC)
					tcRemove(v.MAC)
				}
			}
			v.Paused = true
		}
	case "resume":
		if v.Paused {
			v.Paused = false
			if v.Started != 0 {
				v.Expires = now + v.Remaining
			}
		}
	case "disable":
		v.Disabled = true
		if v.MAC != "" {
			_ = nds("deauth", v.MAC)
			tcRemove(v.MAC)
		}
	case "enable":
		v.Disabled = false
	case "extend":
		if q.Minutes < 1 || q.Minutes > 525600 {
			fail(w, 400, "invalid extension")
			return
		}
		if v.Started == 0 {
			v.Minutes += q.Minutes
		} else if v.Paused {
			v.Remaining += int64(q.Minutes) * 60
		} else if v.Expires < now {
			v.Expires = now + int64(q.Minutes)*60
		} else {
			v.Expires += int64(q.Minutes) * 60
		}
	case "delete":
		if v.MAC != "" {
			_ = nds("deauth", v.MAC)
			tcRemove(v.MAC)
		}
		delete(db.Vouchers, q.Key)
		if e := save(); e != nil {
			fail(w, 500, e.Error())
			return
		}
		respond(w, 200, map[string]string{"status": "deleted"})
		return
	default:
		fail(w, 400, "unknown action")
		return
	}
	if e := save(); e != nil {
		fail(w, 500, e.Error())
		return
	}
	respond(w, 200, v)
}

func trustedList(w http.ResponseWriter, r *http.Request) {
	mu.Lock()
	defer mu.Unlock()
	arr := make([]TrustedDevice, 0, len(db.Trusted))
	for _, t := range db.Trusted {
		arr = append(arr, *t)
	}
	respond(w, 200, arr)
}

func trustedAdd(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		fail(w, 405, "POST required")
		return
	}
	var t TrustedDevice
	if json.NewDecoder(http.MaxBytesReader(w, r.Body, 4096)).Decode(&t) != nil {
		fail(w, 400, "invalid JSON")
		return
	}
	t.MAC = strings.ToLower(strings.TrimSpace(t.MAC))
	if !macRx.MatchString(t.MAC) || t.UpKbps < 0 || t.DownKbps < 0 || len(t.Name) > 80 {
		fail(w, 400, "invalid MAC, speed or name")
		return
	}
	mu.Lock()
	defer mu.Unlock()
	if findTrusted(t.MAC) != nil {
		fail(w, 409, "device already trusted")
		return
	}
	db.Trusted = append(db.Trusted, &t)
	if e := save(); e != nil {
		fail(w, 500, e.Error())
		return
	}
	respond(w, 201, t)
}

func trustedRemove(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		fail(w, 405, "POST required")
		return
	}
	var q struct {
		MAC string `json:"mac"`
	}
	if json.NewDecoder(http.MaxBytesReader(w, r.Body, 1024)).Decode(&q) != nil {
		fail(w, 400, "invalid JSON")
		return
	}
	mu.Lock()
	defer mu.Unlock()
	for i, t := range db.Trusted {
		if strings.EqualFold(t.MAC, q.MAC) {
			tcRemove(t.MAC)
			db.Trusted = append(db.Trusted[:i], db.Trusted[i+1:]...)
			if e := save(); e != nil {
				fail(w, 500, e.Error())
				return
			}
			respond(w, 200, map[string]string{"status": "removed"})
			return
		}
	}
	fail(w, 404, "not found")
}

func decodeFAS(encoded string) (map[string]string, error) {
	raw, err := base64.StdEncoding.DecodeString(encoded)
	if err != nil {
		raw, err = base64.RawStdEncoding.DecodeString(encoded)
	}
	if err != nil || len(raw) > 8192 {
		return nil, errors.New("invalid FAS payload")
	}
	fields := map[string]string{}
	for _, part := range strings.Split(string(raw), ", ") {
		pair := strings.SplitN(part, "=", 2)
		if len(pair) == 2 {
			fields[strings.TrimSpace(pair[0])] = strings.TrimSpace(pair[1])
		}
	}
	if fields["hid"] == "" {
		fields["hid"] = fields["client_hid"]
	}
	if !hidRx.MatchString(fields["hid"]) {
		return nil, errors.New("invalid FAS hash")
	}
	if net.ParseIP(fields["clientip"]) == nil || !macRx.MatchString(fields["clientmac"]) {
		return nil, errors.New("invalid client identity")
	}
	if fields["gatewayaddress"] != "192.168.2.1" {
		return nil, errors.New("invalid gateway")
	}
	if !authdirRx.MatchString(fields["authdir"]) {
		return nil, errors.New("invalid auth directory")
	}
	return fields, nil
}

func newSession(fields map[string]string) (string, error) {
	buf := make([]byte, 32)
	if _, err := rand.Read(buf); err != nil {
		return "", err
	}
	id := hex.EncodeToString(buf)
	fasSessions[id] = fasSession{
		IP:      fields["clientip"],
		MAC:     strings.ToLower(fields["clientmac"]),
		HID:     fields["hid"],
		Gateway: fields["gatewayaddress"],
		Authdir: fields["authdir"],
		Until:   time.Now().Add(5 * time.Minute),
	}
	return id, nil
}

func authRedirect(fields map[string]string) string {
	digest := sha256.Sum256([]byte(fields["hid"] + fasKey))
	authURL := url.URL{
		Scheme: "http",
		Host:   net.JoinHostPort(fields["gatewayaddress"], gatewayPort),
		Path:   "/" + fields["authdir"] + "/",
	}
	params := url.Values{}
	params.Set("tok", hex.EncodeToString(digest[:]))
	params.Set("redir", "http://192.168.2.1:2080/status")
	authURL.RawQuery = params.Encode()
	return authURL.String()
}

func portal(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Cache-Control", "no-store")
	w.Header().Set("X-Content-Type-Options", "nosniff")
	w.Header().Set("Referrer-Policy", "no-referrer")
	ip := ipOf(r)
	if ip == "" {
		http.Error(w, "IPv4 client required", 400)
		return
	}
	message := ""
	if r.Method == "GET" {
		fields, err := decodeFAS(r.URL.Query().Get("fas"))
		if err != nil || fields["clientip"] != ip {
			http.Error(w, "OpenNDS session missing or invalid. Reconnect to Wi-Fi.", 403)
			return
		}
		verifiedMAC, checkErr := macFor(ip)
		if checkErr != nil || verifiedMAC != strings.ToLower(fields["clientmac"]) {
			http.Error(w, "OpenNDS client verification failed", 403)
			return
		}
		mu.Lock()
		t := findTrusted(verifiedMAC)
		mu.Unlock()
		if t != nil {
			tcApply(t.MAC, t.UpKbps, t.DownKbps)
			http.Redirect(w, r, authRedirect(fields), http.StatusSeeOther)
			return
		}
		mu.Lock()
		id, e := newSession(fields)
		mu.Unlock()
		if e != nil {
			http.Error(w, "Session error", 500)
			return
		}
		http.SetCookie(w, &http.Cookie{
			Name: "twfas", Value: id, Path: "/portal",
			HttpOnly: true, SameSite: http.SameSiteStrictMode, MaxAge: 300,
		})
	} else if r.Method == "POST" {
		if origin := r.Header.Get("Origin"); origin != "" {
			u, err := url.Parse(origin)
			if err != nil || !strings.EqualFold(u.Host, r.Host) {
				http.Error(w, "Invalid request origin", 403)
				return
			}
		}
		if err := r.ParseForm(); err != nil {
			http.Error(w, "Invalid form", 400)
			return
		}
		key := strings.TrimSpace(r.FormValue("key"))
		cookie, err := r.Cookie("twfas")
		if err != nil {
			http.Error(w, "Session expired. Reconnect to Wi-Fi.", 403)
			return
		}
		mu.Lock()
		session, ok := fasSessions[cookie.Value]
		if !ok || session.IP != ip || time.Now().After(session.Until) {
			mu.Unlock()
			http.Error(w, "Session expired. Reconnect to Wi-Fi.", 403)
			return
		}
		v, found := db.Vouchers[key]
		now := time.Now().Unix()
		if !found || v.Disabled || v.Paused {
			message = "Voucher unavailable"
		} else if v.Started != 0 && v.Expires <= now {
			message = "Voucher expired"
		} else {
			mac, e := macFor(ip)
			if e != nil || mac != session.MAC {
				message = "OpenNDS device verification failed"
			} else if v.MAC != "" && v.MAC != mac {
				message = "Voucher belongs to another device"
			} else {
				old := *v
				if v.Started == 0 {
					v.Started = now
					v.Expires = now + int64(v.Minutes)*60
					v.MAC = mac
				}
				v.IP = ip
				if e = save(); e != nil {
					*v = old
					message = "Could not save voucher activation"
				} else {
					delete(fasSessions, cookie.Value)
					up, down := v.UpKbps, v.DownKbps
					target := authRedirect(map[string]string{
						"hid":            session.HID,
						"gatewayaddress": session.Gateway,
						"authdir":        session.Authdir,
					})
					mu.Unlock()
					tcApply(mac, up, down)
					http.Redirect(w, r, target, http.StatusSeeOther)
					return
				}
			}
		}
		mu.Unlock()
	} else {
		http.Error(w, "Method not allowed", 405)
		return
	}
	_ = portalT.Execute(w, map[string]string{"Message": message, "IP": ip})
}

func statusHandler(w http.ResponseWriter, r *http.Request) {
	ip := ipOf(r)
	if ip == "" {
		http.Error(w, "IPv4 client required", 400)
		return
	}
	mac, err := macFor(ip)
	if err != nil {
		http.Error(w, "Not connected to the WiFi", 403)
		return
	}
	mu.Lock()
	var v *Voucher
	for _, x := range db.Vouchers {
		if strings.EqualFold(x.MAC, mac) {
			c := *x
			v = &c
			break
		}
	}
	var t *TrustedDevice
	if v == nil {
		if td := findTrusted(mac); td != nil {
			c := *td
			t = &c
		}
	}
	mu.Unlock()

	if v == nil && t == nil {
		http.Error(w, "No active plan for this device", 404)
		return
	}
	now := time.Now().Unix()
	data := map[string]any{"MAC": mac, "IP": ip}
	if v != nil {
		left := v.Expires - now
		if left < 0 {
			left = 0
		}
		data["Kind"] = "Voucher"
		data["Name"] = v.Name
		data["Left"] = fmt.Sprintf("%dh %dm", left/3600, (left%3600)/60)
		data["Expires"] = time.Unix(v.Expires, 0).Format("2006-01-02 15:04")
		data["Up"] = v.UpKbps
		data["Down"] = v.DownKbps
	} else {
		data["Kind"] = "Trusted device"
		data["Name"] = t.Name
		data["Left"] = "Unlimited"
		data["Expires"] = "-"
		data["Up"] = t.UpKbps
		data["Down"] = t.DownKbps
	}
	w.Header().Set("Content-Type", "text/html; charset=utf-8")
	_ = statusT.Execute(w, data)
}

func sweep() {
	for range time.Tick(5 * time.Second) {
		now := time.Now().Unix()
		mu.Lock()
		for id, ss := range fasSessions {
			if time.Now().After(ss.Until) {
				delete(fasSessions, id)
			}
		}
		var toDeauth []string
		for _, v := range db.Vouchers {
			if v.Started != 0 && !v.Paused && (v.Disabled || v.Expires <= now) && v.MAC != "" {
				toDeauth = append(toDeauth, v.MAC)
			}
		}
		trusted := make([]TrustedDevice, 0, len(db.Trusted))
		for _, t := range db.Trusted {
			trusted = append(trusted, *t)
		}
		mu.Unlock()

		for _, mac := range toDeauth {
			_ = nds("deauth", mac)
			tcRemove(mac)
		}
		for _, t := range trusted {
			if isAuthenticated(t.MAC) {
				tcApply(t.MAC, t.UpKbps, t.DownKbps)
			}
		}
	}
}

var portalT = template.Must(template.New("portal").Parse(`<!doctype html><html><head><meta name="viewport" content="width=device-width,initial-scale=1"><title>Tenants WiFi</title><style>body{font:16px system-ui;background:#eef2f8;display:grid;place-items:center;min-height:90vh}.card{background:white;padding:30px;border-radius:18px;max-width:360px;width:85%;box-shadow:0 12px 45px #17253d22}h1{color:#203e7a}input,button{box-sizing:border-box;width:100%;padding:14px;margin:8px 0;border-radius:9px;border:1px solid #bbb}button{background:#305fe0;color:white;border:0}p{overflow-wrap:anywhere}</style></head><body><main class="card"><h1>Tenants WiFi</h1><p>Enter your voucher to connect.</p><form method="post"><input name="key" placeholder="Voucher key" required autocomplete="off" maxlength="64"><button>Connect</button></form><p>{{.Message}}</p></main></body></html>`))

var statusT = template.Must(template.New("status").Parse(`<!doctype html><html><head><meta name="viewport" content="width=device-width,initial-scale=1"><title>Tenants WiFi</title><style>body{font:16px system-ui;background:#eef2f8;display:grid;place-items:center;min-height:90vh}.card{background:white;padding:30px;border-radius:18px;max-width:400px;width:85%;box-shadow:0 12px 45px #17253d22}h1{color:#203e7a}table{width:100%;border-collapse:collapse}td{padding:6px 0;border-bottom:1px solid #eef}td:first-child{color:#667}</style></head><body><main class="card"><h1>Tenants WiFi</h1><p>{{.Kind}}: <b>{{.Name}}</b></p><table><tr><td>Time remaining</td><td>{{.Left}}</td></tr><tr><td>Expires</td><td>{{.Expires}}</td></tr><tr><td>Download cap</td><td>{{.Down}} kbps</td></tr><tr><td>Upload cap</td><td>{{.Up}} kbps</td></tr><tr><td>Device MAC</td><td>{{.MAC}}</td></tr><tr><td>Device IP</td><td>{{.IP}}</td></tr></table></main></body></html>`))

func main() {
	adminPass = os.Getenv("TENANTS_ADMIN_PASSWORD")
	fasKey = os.Getenv("TENANTS_FAS_KEY")
	gatewayPort = os.Getenv("TENANTS_GATEWAY_PORT")
	if gatewayPort == "" {
		gatewayPort = "2050"
	}
	if n, e := strconv.Atoi(gatewayPort); e != nil || n < 1 || n > 65535 {
		log.Fatal("Invalid gateway port")
	}
	if len(fasKey) < 32 {
		log.Fatal("TENANTS_FAS_KEY must match the OpenNDS FAS key and be at least 32 characters")
	}
	if len(adminPass) < 12 {
		log.Fatal("Set TENANTS_ADMIN_PASSWORD to a strong password of at least 12 characters")
	}
	dataPath = os.Getenv("TENANTS_DB")
	if dataPath == "" {
		dataPath = "/etc/tenants-wifi/vouchers.json"
	}
	ndsctl = os.Getenv("TENANTS_NDSCTL")
	if ndsctl == "" {
		ndsctl = "/usr/bin/ndsctl"
	}
	load()
	ensureIFB()

	mux := http.NewServeMux()
	mux.HandleFunc("/", admin(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/" {
			http.NotFound(w, r)
			return
		}
		w.Header().Set("Content-Type", "text/html; charset=utf-8")
		w.Write([]byte(adminHTML))
	}))
	mux.HandleFunc("/api/vouchers", admin(list))
	mux.HandleFunc("/api/create", admin(create))
	mux.HandleFunc("/api/action", admin(action))
	mux.HandleFunc("/api/trusted", admin(trustedList))
	mux.HandleFunc("/api/trusted/add", admin(trustedAdd))
	mux.HandleFunc("/api/trusted/remove", admin(trustedRemove))

	portalMux := http.NewServeMux()
	portalMux.HandleFunc("/portal", portal)
	portalMux.HandleFunc("/status", statusHandler)

	go sweep()

	portalAddr := os.Getenv("TENANTS_PORTAL_ADDR")
	if portalAddr == "" {
		portalAddr = "192.168.2.1:2080"
	}
	adminAddr := os.Getenv("TENANTS_ADMIN_ADDR")
	if adminAddr == "" {
		adminAddr = "192.168.2.1:2088"
	}
	go func() {
		log.Printf("portal listening on %s", portalAddr)
		log.Fatal(http.ListenAndServe(portalAddr, portalMux))
	}()
	log.Printf("admin listening on %s", adminAddr)
	log.Fatal(http.ListenAndServe(adminAddr, mux))
}

var adminHTML = `<!doctype html><html><head><meta name="viewport" content="width=device-width,initial-scale=1"><title>Tenants WiFi Admin</title><style>body{font:15px system-ui;background:#f3f6fb;color:#24344d;margin:0}header{background:#18376f;color:white;padding:22px 5%}main{max-width:1100px;margin:24px auto;padding:0 18px}section{background:white;padding:22px;border-radius:14px;margin:18px 0;box-shadow:0 3px 18px #20305013}input{padding:11px;border:1px solid #c9d2df;border-radius:7px;margin:5px;max-width:180px}button{border:0;border-radius:7px;background:#2d5be3;color:white;padding:10px;margin:3px;cursor:pointer}button.alt{background:#60718c}button.danger{background:#bd3b4a}table{width:100%;border-collapse:collapse}th,td{text-align:left;border-bottom:1px solid #e5eaf0;padding:10px}small{color:#667} .scroll{overflow:auto}#message{color:#ad3d45}</style></head><body><header><h1>Tenants WiFi</h1>Voucher administration</header><main>
<section><h2>Create voucher</h2><form id="new"><input name="key" placeholder="Voucher key" required minlength="4"><input name="name" placeholder="Tenant name"><input name="minutes" type="number" placeholder="Minutes" min="1" value="1440" required><input name="down_kbps" type="number" placeholder="Download kbps" min="0" value="0"><input name="up_kbps" type="number" placeholder="Upload kbps" min="0" value="0"><button>Create voucher</button></form><small>Speed values are enforced now via tc. 0 = unlimited.</small></section>
<section><h2>Trusted devices (skip voucher)</h2><form id="trust"><input name="mac" placeholder="aa:bb:cc:dd:ee:ff" required><input name="name" placeholder="Name"><input name="up_kbps" type="number" placeholder="Up kbps" min="0" value="0"><input name="down_kbps" type="number" placeholder="Down kbps" min="0" value="0"><button>Add trusted</button></form><div class="scroll"><table><thead><tr><th>MAC</th><th>Name</th><th>Up</th><th>Down</th><th></th></tr></thead><tbody id="trustRows"></tbody></table></div></section>
<section><h2>Vouchers</h2><p id="message"></p><div class="scroll"><table><thead><tr><th>Key / tenant</th><th>Device</th><th>Time left</th><th>State</th><th>Actions</th></tr></thead><tbody id="rows"></tbody></table></div></section>
</main><script>
async function api(url,data){let opts=data?{method:'POST',headers:{'Content-Type':'application/json','X-Tenants-Admin':'1'},body:JSON.stringify(data)}:{};let r=await fetch(url,opts);let j=await r.json();if(!r.ok)throw Error(j.error||r.status);return j}
function elt(tag,text){let x=document.createElement(tag);x.textContent=text;return x}function btn(label,act,cls){let x=elt('button',label);x.className=cls||'';x.onclick=act;return x}
async function act(key,action,minutes){try{await api('/api/action',{key,action,minutes});load()}catch(e){document.querySelector('#message').textContent=e.message}}
async function load(){try{let vs=await api('/api/vouchers');let tbody=document.querySelector('#rows');tbody.replaceChildren();for(let v of vs){let tr=document.createElement('tr');let now=Math.floor(Date.now()/1000);let left=v.started?(v.paused?v.remaining:Math.max(0,v.expires-now)):v.minutes*60;let state=v.disabled?'Disabled':v.paused?'Paused':v.started?(left?'Active':'Expired'):'Unused';for(let s of [v.key+' / '+v.name,v.mac||'Not bound',Math.floor(left/3600)+'h '+Math.floor(left%3600/60)+'m',state])tr.appendChild(elt('td',s));let td=elt('td','');td.append(btn('Extend +1 day',()=>act(v.key,'extend',1440)));td.append(btn(v.paused?'Resume':'Pause',()=>act(v.key,v.paused?'resume':'pause'),'alt'));td.append(btn(v.disabled?'Enable':'Disable',()=>act(v.key,v.disabled?'enable':'disable'),'alt'));td.append(btn('Delete',()=>{if(confirm('Delete '+v.key+'?'))act(v.key,'delete')},'danger'));tr.appendChild(td);tbody.appendChild(tr)}}catch(e){document.querySelector('#message').textContent=e.message}}
async function loadTrust(){try{let ts=await api('/api/trusted');let tb=document.querySelector('#trustRows');tb.replaceChildren();for(let t of ts){let tr=document.createElement('tr');for(let s of [t.mac||'',t.name||'',String(t.up_kbps||0),String(t.down_kbps||0)])tr.appendChild(elt('td',s));let td=elt('td','');td.append(btn('Remove',()=>removeTrust(t.mac),'danger'));tr.appendChild(td);tb.appendChild(tr)}}catch(e){document.querySelector('#message').textContent=e.message}}
async function removeTrust(mac){if(!confirm('Remove '+mac+'?'))return;try{await api('/api/trusted/remove',{mac});loadTrust()}catch(e){document.querySelector('#message').textContent=e.message}}
document.querySelector('#new').onsubmit=async e=>{e.preventDefault();let f=new FormData(e.target);try{await api('/api/create',{key:f.get('key'),name:f.get('name'),minutes:Number(f.get('minutes')),down_kbps:Number(f.get('down_kbps')),up_kbps:Number(f.get('up_kbps'))});e.target.reset();load()}catch(err){document.querySelector('#message').textContent=err.message}};
document.querySelector('#trust').onsubmit=async e=>{e.preventDefault();let f=new FormData(e.target);try{await api('/api/trusted/add',{mac:f.get('mac'),name:f.get('name'),up_kbps:Number(f.get('up_kbps')),down_kbps:Number(f.get('down_kbps'))});e.target.reset();loadTrust()}catch(err){document.querySelector('#message').textContent=err.message}};
load();loadTrust();setInterval(load,15000);
</script></body></html>`

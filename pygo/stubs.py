from typing import Callable, Dict


def _add_using(self, name: str) -> bool:
    self._usings.add(f'"{name}"')
    return True


def visit_str_join(self, node, vargs):
    value = self.visit(node.func.value)
    _add_using(self, "strings")
    if value == '""' and len(vargs) == 1:
        return f'strings.Join({vargs[0]}, "")'
    return f"strings.Join({vargs[0]}, {value})"


def visit_str_capitalize(self, node, vargs):
    value = self.visit(node.func.value)
    _add_using(self, "strings")
    return f"(strings.ToUpper({value}[:1]) + strings.ToLower({value}[1:]))"


def visit_strftime(self, node, vargs):
    value = self.visit(node.func.value)
    return f"{value}.Format({vargs[0]})"


def visit_os_environ_get(self, node, vargs):
    _add_using(self, "os")
    if len(vargs) > 1:
        return (
            f"func() string {{ value, ok := os.LookupEnv({vargs[0]}); "
            f"if ok {{ return value }}; return {vargs[1]} }}()"
        )
    return f"os.Getenv({vargs[0]})"


def visit_os_listdir(self, node, vargs):
    _add_using(self, "os")
    path = vargs[0] if vargs else '"."'
    return (
        f"func() []string {{ entries, err := os.ReadDir({path}); "
        "if err != nil { panic(err) }; "
        "names := make([]string, len(entries)); "
        "for i, entry := range entries { names[i] = entry.Name() }; "
        "return names }()"
    )


def visit_decimal_decimal(self, node, vargs):
    _add_using(self, "math/big")
    return (
        f"func() *big.Float {{ v, _, err := big.ParseFloat({vargs[0]}, 10, 0, big.ToNearestEven); "
        "if err != nil { panic(err) }; return v }()"
    )


STDLIB_DISPATCH_TABLE: Dict[str, Callable] = {
    "str.lower": lambda self, node, vargs: (_add_using(self, "strings"))
    and f"strings.ToLower({self.visit(node.func.value)})",
    "str.upper": lambda self, node, vargs: (_add_using(self, "strings"))
    and f"strings.ToUpper({self.visit(node.func.value)})",
    "str.capitalize": visit_str_capitalize,
    "str.title": lambda self, node, vargs: (_add_using(self, "strings"))
    and f"strings.Title({self.visit(node.func.value)})",
    "str.strip": lambda self, node, vargs: (_add_using(self, "strings"))
    and f"strings.TrimSpace({self.visit(node.func.value)})",
    "str.lstrip": lambda self, node, vargs: (
        _add_using(self, "strings") and _add_using(self, "unicode")
    )
    and f"strings.TrimLeftFunc({self.visit(node.func.value)}, unicode.IsSpace)",
    "str.rstrip": lambda self, node, vargs: (
        _add_using(self, "strings") and _add_using(self, "unicode")
    )
    and f"strings.TrimRightFunc({self.visit(node.func.value)}, unicode.IsSpace)",
    "str.find": lambda self, node, vargs: (_add_using(self, "strings"))
    and f"strings.Index({self.visit(node.func.value)}, {vargs[0]})",
    "str.replace": lambda self, node, vargs: (_add_using(self, "strings"))
    and f"strings.ReplaceAll({self.visit(node.func.value)}, {vargs[0]}, {vargs[1]})",
    "str.split": lambda self, node, vargs: (_add_using(self, "strings"))
    and (
        f"strings.Split({self.visit(node.func.value)}, {vargs[0]})"
        if vargs
        else f"strings.Fields({self.visit(node.func.value)})"
    ),
    "str.join": visit_str_join,
    "str.isalpha": lambda self, node, vargs: (_add_using(self, "regexp"))
    and f"regexp.MustCompile(`^[A-Za-z]+$`).MatchString({self.visit(node.func.value)})",
    "str.isdigit": lambda self, node, vargs: (_add_using(self, "regexp"))
    and f"regexp.MustCompile(`^\\d+$`).MatchString({self.visit(node.func.value)})",
    "str.isspace": lambda self, node, vargs: (_add_using(self, "regexp"))
    and f"regexp.MustCompile(`^\\s+$`).MatchString({self.visit(node.func.value)})",
    "str.exists": lambda self, node, vargs: (_add_using(self, "os"))
    and f"func() bool {{ _, err := os.Stat({self.visit(node.func.value)}); return err == nil }}()",
    "str.is_dir": lambda self, node, vargs: (_add_using(self, "os"))
    and f"func() bool {{ info, err := os.Stat({self.visit(node.func.value)}); return err == nil && info.IsDir() }}()",
    "str.is_file": lambda self, node, vargs: (_add_using(self, "os"))
    and f"func() bool {{ info, err := os.Stat({self.visit(node.func.value)}); return err == nil && !info.IsDir() }}()",
    "str.read_text": lambda self, node, vargs: (_add_using(self, "os"))
    and f"func() string {{ b, err := os.ReadFile({self.visit(node.func.value)}); if err != nil {{ panic(err) }}; return string(b) }}()",
    "str.write_text": lambda self, node, vargs: (_add_using(self, "os"))
    and f"os.WriteFile({self.visit(node.func.value)}, []byte({vargs[0]}), 0644)",
    "str.strftime": visit_strftime,
    # re module
    "re.search": lambda self, node, vargs: (_add_using(self, "regexp"))
    and f"regexp.MustCompile({vargs[0]}).FindStringIndex({vargs[1]}) != nil",
    "re.match": lambda self, node, vargs: (_add_using(self, "regexp"))
    and f'regexp.MustCompile("^"+{vargs[0]}).FindStringIndex({vargs[1]}) != nil',
    "re.findall": lambda self, node, vargs: (_add_using(self, "regexp"))
    and f"regexp.MustCompile({vargs[0]}).FindAllString({vargs[1]}, -1)",
    "re.sub": lambda self, node, vargs: (_add_using(self, "regexp"))
    and f"regexp.MustCompile({vargs[0]}).ReplaceAllString({vargs[2]}, {vargs[1]})",
    "re.split": lambda self, node, vargs: (_add_using(self, "regexp"))
    and f"regexp.MustCompile({vargs[0]}).Split({vargs[1]}, -1)",
    "re.compile": lambda self, node, vargs: (_add_using(self, "regexp"))
    and f"regexp.MustCompile({vargs[0]})",
    # math module
    "math.ceil": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Ceil({', '.join(vargs)})",
    "math.floor": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Floor({', '.join(vargs)})",
    "math.pow": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Pow({', '.join(vargs)})",
    "math.sqrt": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Sqrt({', '.join(vargs)})",
    "math.log": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Log({', '.join(vargs)})",
    "math.log10": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Log10({', '.join(vargs)})",
    "math.gcd": lambda self, node, vargs: f"gcd({', '.join(vargs)})",
    "math.factorial": lambda self, node, vargs: f"factorial({', '.join(vargs)})",
    "math.sin": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Sin({', '.join(vargs)})",
    "math.cos": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Cos({', '.join(vargs)})",
    "math.tan": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Tan({', '.join(vargs)})",
    "math.asin": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Asin({', '.join(vargs)})",
    "math.acos": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Acos({', '.join(vargs)})",
    "math.atan": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Atan({', '.join(vargs)})",
    "math.degrees": lambda self, node, vargs: (_add_using(self, "math"))
    and f"(({vargs[0]}) * 180 / math.Pi)",
    "math.radians": lambda self, node, vargs: (_add_using(self, "math"))
    and f"(({vargs[0]}) * math.Pi / 180)",
    "math.cosh": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Cosh({', '.join(vargs)})",
    "math.tanh": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Tanh({', '.join(vargs)})",
    "math.erf": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Erf({', '.join(vargs)})",
    "math.erfc": lambda self, node, vargs: (_add_using(self, "math"))
    and f"math.Erfc({', '.join(vargs)})",
    # os module
    "os.listdir": visit_os_listdir,
    "os.mkdir": lambda self, node, vargs: (_add_using(self, "os"))
    and f"os.Mkdir({vargs[0]}, 0755)",
    "os.getcwd": lambda self, node, vargs: (_add_using(self, "os"))
    and "func() string { cwd, err := os.Getwd(); if err != nil { panic(err) }; return cwd }()",
    "os.environ.get": visit_os_environ_get,
    "os.remove": lambda self, node, vargs: (_add_using(self, "os"))
    and f"os.Remove({vargs[0]})",
    "os.path.join": lambda self, node, vargs: (_add_using(self, "path/filepath"))
    and f"filepath.Join({', '.join(vargs)})",
    "os.path.exists": lambda self, node, vargs: (_add_using(self, "os"))
    and f"func() bool {{ _, err := os.Stat({vargs[0]}); return err == nil }}()",
    "os.path.isdir": lambda self, node, vargs: (_add_using(self, "os"))
    and f"func() bool {{ info, err := os.Stat({vargs[0]}); return err == nil && info.IsDir() }}()",
    "os.path.isfile": lambda self, node, vargs: (_add_using(self, "os"))
    and f"func() bool {{ info, err := os.Stat({vargs[0]}); return err == nil && !info.IsDir() }}()",
    "os.path.basename": lambda self, node, vargs: (_add_using(self, "path/filepath"))
    and f"filepath.Base({vargs[0]})",
    "os.path.dirname": lambda self, node, vargs: (_add_using(self, "path/filepath"))
    and f"filepath.Dir({vargs[0]})",
    # sys module
    "sys.exit": lambda self, node, vargs: (_add_using(self, "os"))
    and f"os.Exit({vargs[0] if vargs else '0'})",
    # json module
    "json.loads": lambda self, node, vargs: (_add_using(self, "encoding/json"))
    and f"func() any {{ var v any; if err := json.Unmarshal([]byte({vargs[0]}), &v); err != nil {{ panic(err) }}; return v }}()",
    "json.dumps": lambda self, node, vargs: (_add_using(self, "encoding/json"))
    and f"func() string {{ b, err := json.Marshal({vargs[0]}); if err != nil {{ panic(err) }}; return string(b) }}()",
    # time module
    "time.time": lambda self, node, vargs: (_add_using(self, "time"))
    and "float64(time.Now().UnixNano()) / 1e9",
    "time.sleep": lambda self, node, vargs: (_add_using(self, "time"))
    and f"time.Sleep(time.Duration({vargs[0]}) * time.Second)",
    # random module
    "random.random": lambda self, node, vargs: (_add_using(self, "math/rand"))
    and "rand.Float64()",
    "random.randint": lambda self, node, vargs: (_add_using(self, "math/rand"))
    and f"rand.Intn(({vargs[1]})-({vargs[0]})+1) + ({vargs[0]})",
    "random.choice": lambda self, node, vargs: (_add_using(self, "math/rand"))
    and f"{vargs[0]}[rand.Intn(len({vargs[0]}))]",
    # datetime module
    "datetime.datetime.now": lambda self, node, vargs: (_add_using(self, "time"))
    and "time.Now()",
    "datetime.datetime.utcnow": lambda self, node, vargs: (_add_using(self, "time"))
    and "time.Now().UTC()",
    "datetime.datetime.strftime": lambda self, node, vargs: f"{vargs[0]}.Format({vargs[1]})",
    # pathlib module
    "pathlib.Path": lambda self, node, vargs: vargs[0],
    # shutil module
    "shutil.copy": lambda self, node, vargs: (_add_using(self, "os"))
    and f"copyFile({vargs[0]}, {vargs[1]})",
    "shutil.rmtree": lambda self, node, vargs: (_add_using(self, "os"))
    and f"os.RemoveAll({vargs[0]})",
    "shutil.move": lambda self, node, vargs: (_add_using(self, "os"))
    and f"os.Rename({vargs[0]}, {vargs[1]})",
    # logging module
    "logging.info": lambda self, node, vargs: (_add_using(self, "log"))
    and f"log.Print({vargs[0]})",
    "logging.warning": lambda self, node, vargs: (_add_using(self, "log"))
    and f"log.Print({vargs[0]})",
    "logging.error": lambda self, node, vargs: (_add_using(self, "log"))
    and f"log.Print({vargs[0]})",
    "logging.debug": lambda self, node, vargs: (_add_using(self, "log"))
    and f"log.Print({vargs[0]})",
    # base64 module
    "base64.b64encode": lambda self, node, vargs: (_add_using(self, "encoding/base64"))
    and f"[]byte(base64.StdEncoding.EncodeToString({vargs[0]}))",
    "base64.b64decode": lambda self, node, vargs: (_add_using(self, "encoding/base64"))
    and f"func() []byte {{ b, err := base64.StdEncoding.DecodeString({vargs[0]}); if err != nil {{ panic(err) }}; return b }}()",
    # subprocess module
    "subprocess.run": lambda self, node, vargs: (_add_using(self, "os/exec"))
    and f"exec.Command({vargs[0]}).Run()",
    "subprocess.check_output": lambda self, node, vargs: (_add_using(self, "os/exec"))
    and f"func() []byte {{ out, err := exec.Command({vargs[0]}).Output(); if err != nil {{ panic(err) }}; return out }}()",
    "subprocess.call": lambda self, node, vargs: (_add_using(self, "os/exec"))
    and f"func() int {{ err := exec.Command({vargs[0]}).Run(); if err != nil {{ return 1 }}; return 0 }}()",
    # hashlib module
    "hashlib.sha256": lambda self, node, vargs: (_add_using(self, "crypto/sha256"))
    and "sha256.New()",
    "hashlib.md5": lambda self, node, vargs: (_add_using(self, "crypto/md5"))
    and "md5.New()",
    "str.hexdigest": lambda self, node, vargs: (_add_using(self, "encoding/hex"))
    and f"hex.EncodeToString({self.visit(node.func.value)}.Sum(nil))",
    # csv module
    "csv.reader": lambda self, node, vargs: (_add_using(self, "encoding/csv"))
    and f"csv.NewReader({vargs[0]})",
    "csv.writer": lambda self, node, vargs: (_add_using(self, "encoding/csv"))
    and f"csv.NewWriter({vargs[0]})",
    # collections module
    "collections.OrderedDict": lambda self, node, vargs: "map[string]string{}",
    "collections.defaultdict": lambda self, node, vargs: "map[string]string{}",
    "collections.deque": lambda self, node, vargs: f"append([]any{{}}, {vargs[0]}...)",
    "collections.Counter": lambda self, node, vargs: "map[string]int{}",
    # itertools module
    "itertools.product": lambda self, node, vargs: f"product({', '.join(vargs)})",
    "itertools.chain": lambda self, node, vargs: f"append({vargs[0]}, {', '.join(vargs[1:])}...)",
    # urllib/requests module
    "urllib.parse.urlparse": lambda self, node, vargs: (_add_using(self, "net/url"))
    and f"func() *url.URL {{ u, err := url.Parse({vargs[0]}); if err != nil {{ panic(err) }}; return u }}()",
    "urllib.parse.quote": lambda self, node, vargs: (_add_using(self, "net/url"))
    and f"url.QueryEscape({vargs[0]})",
    "urllib.request.urlopen": lambda self, node, vargs: (_add_using(self, "net/http"))
    and f"http.Get({vargs[0]})",
    "requests.get": lambda self, node, vargs: (_add_using(self, "net/http"))
    and f"http.Get({vargs[0]})",
    # uuid/temp/glob
    "uuid.uuid4": lambda self, node, vargs: (_add_using(self, "github.com/google/uuid"))
    and "uuid.New().String()",
    "tempfile.gettempdir": lambda self, node, vargs: (_add_using(self, "os"))
    and "os.TempDir()",
    "glob.glob": lambda self, node, vargs: (_add_using(self, "path/filepath"))
    and f"func() []string {{ matches, err := filepath.Glob({vargs[0]}); if err != nil {{ panic(err) }}; return matches }}()",
    # binascii/copy/heapq/pickle/warnings/operator
    "binascii.hexlify": lambda self, node, vargs: (_add_using(self, "encoding/hex"))
    and f"[]byte(hex.EncodeToString({vargs[0]}))",
    "binascii.unhexlify": lambda self, node, vargs: (_add_using(self, "encoding/hex"))
    and f"func() []byte {{ b, err := hex.DecodeString({vargs[0]}); if err != nil {{ panic(err) }}; return b }}()",
    "copy.copy": lambda self, node, vargs: vargs[0],
    "copy.deepcopy": lambda self, node, vargs: vargs[0],
    "heapq.heappush": lambda self, node, vargs: (_add_using(self, "container/heap"))
    and f"heap.Push(&{vargs[0]}, {vargs[1]})",
    "heapq.heappop": lambda self, node, vargs: (_add_using(self, "container/heap"))
    and f"heap.Pop(&{vargs[0]})",
    "pickle.dumps": lambda self, node, vargs: STDLIB_DISPATCH_TABLE["json.dumps"](
        self, node, vargs
    ),
    "pickle.loads": lambda self, node, vargs: STDLIB_DISPATCH_TABLE["json.loads"](
        self, node, vargs
    ),
    "warnings.warn": lambda self, node, vargs: (
        _add_using(self, "fmt") and _add_using(self, "os")
    )
    and f"fmt.Fprintln(os.Stderr, {vargs[0]})",
    "platform.system": lambda self, node, vargs: (_add_using(self, "runtime"))
    and "runtime.GOOS",
    "operator.add": lambda self, node, vargs: f"({vargs[0]} + {vargs[1]})",
    "operator.sub": lambda self, node, vargs: f"({vargs[0]} - {vargs[1]})",
    "operator.mul": lambda self, node, vargs: f"({vargs[0]} * {vargs[1]})",
    "operator.truediv": lambda self, node, vargs: f"({vargs[0]} / {vargs[1]})",
    # argparse/unittest/abc/inspect
    "argparse.ArgumentParser": lambda self, node, vargs: (
        _add_using(self, "flag") and _add_using(self, "os")
    )
    and "flag.NewFlagSet(os.Args[0], flag.ExitOnError)",
    "unittest.TestCase": lambda self, node, vargs: "",
    "self.assertEqual": lambda self, node, vargs: f"assertEqual({vargs[0]}, {vargs[1]})",
    "self.assertTrue": lambda self, node, vargs: f"assertTrue({vargs[0]})",
    "self.assertFalse": lambda self, node, vargs: f"assertFalse(!({vargs[0]}))",
    "abc.ABC": lambda self, node, vargs: "",
    "abc.abstractmethod": lambda self, node, vargs: "",
    "inspect.isfunction": lambda self, node, vargs: "true",
    # decimal/fractions/statistics
    "decimal.Decimal": visit_decimal_decimal,
    "statistics.mean": lambda self, node, vargs: f"mean({vargs[0]})",
    # uuid/temp/glob adjacent helpers in V's table
    "bisect.bisect_left": lambda self, node, vargs: (_add_using(self, "sort"))
    and f"sort.Search(len({vargs[0]}), func(i int) bool {{ return {vargs[0]}[i] >= {vargs[1]} }})",
    "zlib.decompress": lambda self, node, vargs: f"zlibDecompress({vargs[0]})",
    "gzip.decompress": lambda self, node, vargs: f"gzipDecompress({vargs[0]})",
    "array.array": lambda self, node, vargs: vargs[1],
    "contextlib.closing": lambda self, node, vargs: f"defer {vargs[0]}.Close()",
    "fnmatch.fnmatch": lambda self, node, vargs: (_add_using(self, "path/filepath"))
    and f"func() bool {{ ok, err := filepath.Match({vargs[1]}, {vargs[0]}); if err != nil {{ return false }}; return ok }}()",
    "locale.setlocale": lambda self, node, vargs: "",
    "locale.format_string": lambda self, node, vargs: (_add_using(self, "fmt"))
    and f"fmt.Sprintf({vargs[0]}, {vargs[1]})",
    "resource.getrlimit": lambda self, node, vargs: "0",
    "signal.signal": lambda self, node, vargs: (_add_using(self, "os/signal"))
    and f"signal.Notify({vargs[1]}, {vargs[0]})",
    "xml.etree.ElementTree.fromstring": lambda self, node, vargs: f"xmlFromString({vargs[0]})",
    "ET.fromstring": lambda self, node, vargs: f"xmlFromString({vargs[0]})",
    "struct.pack": lambda self, node, vargs: f"structPack({', '.join(vargs)})",
    "struct.unpack": lambda self, node, vargs: f"structUnpack({', '.join(vargs)})",
    "queue.Queue": lambda self, node, vargs: "make(chan any)",
    "Queue.put": lambda self, node, vargs: f"{self.visit(node.func.value)} <- {vargs[0]}",
    "Queue.get": lambda self, node, vargs: f"<- {self.visit(node.func.value)}",
    "io.BytesIO": lambda self, node, vargs: (_add_using(self, "bytes"))
    and f"bytes.NewReader({vargs[0]})",
    "io.StringIO": lambda self, node, vargs: (_add_using(self, "strings"))
    and f"strings.NewReader({vargs[0]})",
    "getopt.getopt": lambda self, node, vargs: (_add_using(self, "os"))
    and "os.Args[1:]",
    "pprint.pprint": lambda self, node, vargs: (_add_using(self, "fmt"))
    and f'fmt.Printf("%#v\\n", {vargs[0]})',
    "traceback.print_exc": lambda self, node, vargs: (_add_using(self, "fmt"))
    and 'fmt.Println("Exception occurred")',
    "timeit.default_timer": lambda self, node, vargs: STDLIB_DISPATCH_TABLE[
        "time.time"
    ](self, node, vargs),
    "textwrap.fill": lambda self, node, vargs: vargs[0],
    "zipfile.ZipFile": lambda self, node, vargs: (_add_using(self, "archive/zip"))
    and f"zip.OpenReader({vargs[0]})",
    "tarfile.open": lambda self, node, vargs: f"tarOpen({', '.join(vargs)})",
    "html.escape": lambda self, node, vargs: (_add_using(self, "html"))
    and f"html.EscapeString({vargs[0]})",
    "html.unescape": lambda self, node, vargs: (_add_using(self, "html"))
    and f"html.UnescapeString({vargs[0]})",
    "secrets.token_bytes": lambda self, node, vargs: f"tokenBytes({vargs[0] if vargs else '32'})",
    "secrets.token_hex": lambda self, node, vargs: f"tokenHex({vargs[0] if vargs else '32'})",
    "difflib.SequenceMatcher": lambda self, node, vargs: "SequenceMatcher{}",
    "calendar.monthrange": lambda self, node, vargs: f"monthRange({vargs[0]}, {vargs[1]})",
    "colorsys.rgb_to_hls": lambda self, node, vargs: f"rgbToHls({', '.join(vargs)})",
    "functools.reduce": lambda self, node, vargs: f"reduce({vargs[0]}, {vargs[1]})",
    "http.client.HTTPConnection": lambda self, node, vargs: (
        _add_using(self, "net/http")
    )
    and f"http.Get({vargs[0]})",
    "smtplib.SMTP": lambda self, node, vargs: f"smtpClient({vargs[0] if vargs else '\"localhost\"'})",
    "poplib.POP3": lambda self, node, vargs: "0",
    "imaplib.IMAP4": lambda self, node, vargs: "0",
    "xmlrpc.client.ServerProxy": lambda self, node, vargs: f"0 /* RPC placeholder for {vargs[0]} */",
    "concurrent.futures.ThreadPoolExecutor": lambda self, node, vargs: "0",
    "concurrent.futures.ProcessPoolExecutor": lambda self, node, vargs: "0",
    "ThreadPoolExecutor.submit": lambda self, node, vargs: f"go {vargs[0]}({', '.join(vargs[1:])})",
    "threading.Thread": lambda self, node, vargs: f"go {vargs[0]}" if vargs else "go",
    "hmac.new": lambda self, node, vargs: (_add_using(self, "crypto/hmac"))
    and f"hmac.New({vargs[2]}, {vargs[0]})",
    "sqlite3.connect": lambda self, node, vargs: (_add_using(self, "database/sql"))
    and f'sql.Open("sqlite3", {vargs[0]})',
    "str.appendleft": lambda self, node, vargs: f"append([]any{{{vargs[0]}}}, {self.visit(node.func.value)}...)",
    "str.popleft": lambda self, node, vargs: f"{self.visit(node.func.value)}[0]",
}


STDLIB_ATTR_DISPATCH_TABLE: Dict[str, Callable] = {
    "math.pi": lambda self, node: (_add_using(self, "math")) and "math.Pi",
    "math.e": lambda self, node: (_add_using(self, "math")) and "math.E",
    "math.tau": lambda self, node: (_add_using(self, "math")) and "(math.Pi * 2.0)",
    "math.inf": lambda self, node: (_add_using(self, "math")) and "math.Inf(1)",
    "math.nan": lambda self, node: (_add_using(self, "math")) and "math.NaN()",
    "sys.argv": lambda self, node: (_add_using(self, "os")) and "os.Args",
    "sys.stdin": lambda self, node: (_add_using(self, "os")) and "os.Stdin",
    "sys.stdout": lambda self, node: (_add_using(self, "os")) and "os.Stdout",
    "sys.stderr": lambda self, node: (_add_using(self, "os")) and "os.Stderr",
    "os.environ": lambda self, node: (_add_using(self, "os")) and "os.Environ()",
}

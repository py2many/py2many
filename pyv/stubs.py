from typing import Callable, Dict


def visit_str_join(self, node, vargs):
    return f"{vargs[0]}.join({self.visit(node.func.value)})"


def visit_strftime(self, node, vargs):
    self._usings.add("time")
    fmt = (
        vargs[0]
        .replace("%Y", "YYYY")
        .replace("%m", "MM")
        .replace("%d", "DD")
        .replace("%H", "HH")
        .replace("%M", "mm")
        .replace("%S", "ss")
    )
    return f"{self.visit(node.func.value)}.custom_format({fmt})"


STDLIB_DISPATCH_TABLE: Dict[str, Callable] = {
    "str.lower": lambda self, node, vargs: f"{self.visit(node.func.value)}.to_lower()",
    "str.upper": lambda self, node, vargs: f"{self.visit(node.func.value)}.to_upper()",
    "str.capitalize": lambda self, node, vargs: f"{self.visit(node.func.value)}.capitalize()",
    "str.title": lambda self, node, vargs: f"{self.visit(node.func.value)}.title()",
    "str.strip": lambda self, node, vargs: f"{self.visit(node.func.value)}.trim_space()",
    "str.lstrip": lambda self, node, vargs: f"{self.visit(node.func.value)}.trim_left(' ')",
    "str.rstrip": lambda self, node, vargs: f"{self.visit(node.func.value)}.trim_right(' ')",
    "str.find": lambda self, node, vargs: f"({self.visit(node.func.value)}.index({vargs[0]}) or {{ -1 }})",
    "str.replace": lambda self, node, vargs: f"{self.visit(node.func.value)}.replace({', '.join(vargs)})",
    "str.split": lambda self, node, vargs: (
        f"{self.visit(node.func.value)}.split({vargs[0]})"
        if vargs
        else f"{self.visit(node.func.value)}.fields()"
    ),
    "str.join": visit_str_join,
    "str.isalpha": lambda self, node, vargs: f"{self.visit(node.func.value)}.bytes().all(it.is_letter())",
    "str.isspace": lambda self, node, vargs: f"({self.visit(node.func.value)}.trim_space() == '')",
    # Pathlib-style method calls on strings
    "str.exists": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.exists({self.visit(node.func.value)})",
    "str.is_dir": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.is_dir({self.visit(node.func.value)})",
    "str.is_file": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.is_file({self.visit(node.func.value)})",
    "str.read_text": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.read_file({self.visit(node.func.value)}) or {{ panic(err) }}",
    "str.write_text": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.write_file({self.visit(node.func.value)}, {vargs[0]}) or {{ panic(err) }}",
    "str.strftime": visit_strftime,
    # re module
    "re.search": lambda self, node, vargs: (self._usings.add("regex") or True)
    and (
        f"(fn(p string, s string) bool {{ mut re := regex.regex_opt(p) or {{ panic(err) }}; "
        f"return re.find_all_str(s).len > 0 }}({vargs[0]}, {vargs[1]}))"
    ),
    "re.match": lambda self, node, vargs: (self._usings.add("regex") or True)
    and (
        f"(fn(p string, s string) bool {{ mut re := regex.regex_opt('^' + p) or {{ panic(err) }}; "
        f"return re.find_all_str(s).len > 0 }}({vargs[0]}, {vargs[1]}))"
    ),
    "re.findall": lambda self, node, vargs: (self._usings.add("regex") or True)
    and (
        f"(fn(p string, s string) []string {{ mut re := regex.regex_opt(p) or {{ panic(err) }}; "
        f"return re.find_all_str(s) }}({vargs[0]}, {vargs[1]}))"
    ),
    "re.sub": lambda self, node, vargs: (self._usings.add("regex") or True)
    and (
        f"(fn(p string, r string, s string) string {{ mut re := regex.regex_opt(p) or {{ panic(err) }}; "
        f"return re.replace(s, r) }}({vargs[0]}, {vargs[1]}, {vargs[2]}))"
    ),
    "re.split": lambda self, node, vargs: (self._usings.add("regex") or True)
    and (
        f"(fn(p string, s string) []string {{ mut re := regex.regex_opt(p) or {{ panic(err) }}; "
        f"return re.split(s) }}({vargs[0]}, {vargs[1]}))"
    ),
    "re.compile": lambda self, node, vargs: (self._usings.add("regex") or True)
    and f"regex.regex_opt({vargs[0]}) or {{ panic(err) }}",
    # math module
    "math.ceil": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.ceil({', '.join(vargs)})",
    "math.floor": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.floor({', '.join(vargs)})",
    "math.pow": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.pow({', '.join(vargs)})",
    "math.sqrt": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.sqrt({', '.join(vargs)})",
    "math.log": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.log({', '.join(vargs)})",
    "math.log10": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.log10({', '.join(vargs)})",
    "math.gcd": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.gcd({', '.join(vargs)})",
    "math.factorial": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.factorial({', '.join(vargs)})",
    "math.sin": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.sin({', '.join(vargs)})",
    "math.cos": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.cos({', '.join(vargs)})",
    "math.tan": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.tan({', '.join(vargs)})",
    "math.asin": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.asin({', '.join(vargs)})",
    "math.acos": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.acos({', '.join(vargs)})",
    "math.atan": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.atan({', '.join(vargs)})",
    "math.degrees": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.degrees({', '.join(vargs)})",
    "math.radians": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.radians({', '.join(vargs)})",
    "math.cosh": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.cosh({', '.join(vargs)})",
    "math.tanh": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.tanh({', '.join(vargs)})",
    "math.erf": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.erf({', '.join(vargs)})",
    "math.erfc": lambda self, node, vargs: (self._usings.add("math") or True)
    and f"math.erfc({', '.join(vargs)})",
    # os module
    "os.listdir": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.ls({vargs[0] if vargs else "'.'"}) or {{ panic(err) }}",
    "os.mkdir": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.mkdir({vargs[0]}) or {{ panic(err) }}",
    "os.getcwd": lambda self, node, vargs: (self._usings.add("os") or True)
    and "os.getwd()",
    "os.environ.get": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.getenv({vargs[0]})",
    "os.path.join": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.join_path({', '.join(vargs)})",
    "os.path.exists": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.exists({vargs[0]})",
    "os.path.isdir": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.is_dir({vargs[0]})",
    "os.path.isfile": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.is_file({vargs[0]})",
    "os.path.basename": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.base({vargs[0]})",
    "os.path.dirname": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.dir({vargs[0]})",
    # sys module
    "sys.exit": lambda self, node, vargs: f"exit({vargs[0] if vargs else '0'})",
    # json module
    "json.loads": lambda self, node, vargs: (self._usings.add("json") or True)
    and f"json.decode(Any, {vargs[0]}) or {{ panic(err) }}",
    "json.dumps": lambda self, node, vargs: (self._usings.add("json") or True)
    and f"json.encode({vargs[0]})",
    # time module
    "time.time": lambda self, node, vargs: (self._usings.add("time") or True)
    and "time.now().unix()",
    "time.sleep": lambda self, node, vargs: (self._usings.add("time") or True)
    and f"time.sleep({vargs[0]} * time.second)",
    # random module
    "random.random": lambda self, node, vargs: (self._usings.add("rand") or True)
    and "rand.f64()",
    "random.randint": lambda self, node, vargs: (self._usings.add("rand") or True)
    and f"rand.int_in_range({vargs[0]}, {vargs[1]} + 1) or {{ panic(err) }}",
    "random.choice": lambda self, node, vargs: (self._usings.add("rand") or True)
    and f"rand.element({vargs[0]}) or {{ panic(err) }}",
    # datetime module
    "datetime.datetime.now": lambda self, node, vargs: (
        self._usings.add("time") or True
    )
    and "time.now()",
    "datetime.datetime.utcnow": lambda self, node, vargs: (
        self._usings.add("time") or True
    )
    and "time.utc()",
    "datetime.datetime.strftime": lambda self, node, vargs: (
        self._usings.add("time") or True
    )
    and f"{vargs[0]}.custom_format({vargs[1]})",
    # pathlib module (mapped to os where possible)
    "pathlib.Path": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"{vargs[0]}",
    # shutil module
    "shutil.copy": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.cp({vargs[0]}, {vargs[1]}) or {{ panic(err) }}",
    "shutil.rmtree": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.rmdir_all({vargs[0]}) or {{ panic(err) }}",
    "shutil.move": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.mv({vargs[0]}, {vargs[1]}) or {{ panic(err) }}",
    # logging module
    "logging.info": lambda self, node, vargs: (self._usings.add("log") or True)
    and f"log.info({vargs[0]})",
    "logging.warning": lambda self, node, vargs: (self._usings.add("log") or True)
    and f"log.warn({vargs[0]})",
    "logging.error": lambda self, node, vargs: (self._usings.add("log") or True)
    and f"log.error({vargs[0]})",
    "logging.debug": lambda self, node, vargs: (self._usings.add("log") or True)
    and f"log.debug({vargs[0]})",
    # base64 module
    "base64.b64encode": lambda self, node, vargs: (
        self._usings.add("encoding.base64") or True
    )
    and f"base64.encode({vargs[0]}.bytes())",
    "base64.b64decode": lambda self, node, vargs: (
        self._usings.add("encoding.base64") or True
    )
    and f"base64.decode({vargs[0]}).bytestr()",
    # subprocess module
    "subprocess.run": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.execute({vargs[0]})",
    "subprocess.check_output": lambda self, node, vargs: (
        self._usings.add("os") or True
    )
    and f"os.execute({vargs[0]}).output",
    "subprocess.call": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.system({vargs[0]})",
    # hashlib module
    "hashlib.sha256": lambda self, node, vargs: (
        self._usings.add("crypto.sha256") or True
    )
    and "sha256.new()",
    "hashlib.md5": lambda self, node, vargs: (self._usings.add("crypto.md5") or True)
    and "md5.new()",
    "str.hexdigest": lambda self, node, vargs: f"{self.visit(node.func.value)}.hexhash()",
    # csv module
    "csv.reader": lambda self, node, vargs: (self._usings.add("encoding.csv") or True)
    and f"csv.new_reader({vargs[0]})",
    "csv.writer": lambda self, node, vargs: (self._usings.add("encoding.csv") or True)
    and f"csv.new_writer({vargs[0]})",
    # collections module
    "collections.OrderedDict": lambda self, node, vargs: "map[string]string{}",
    "collections.defaultdict": lambda self, node, vargs: "map[string]string{}",
    # itertools module
    "itertools.product": lambda self, node, vargs: (self._usings.add("iter") or True)
    and f"iter.product({', '.join(vargs)})",
    "itertools.chain": lambda self, node, vargs: (self._usings.add("iter") or True)
    and f"iter.chain({', '.join(vargs)})",
    # urllib module
    "urllib.parse.urlparse": lambda self, node, vargs: (
        self._usings.add("net.urllib") or True
    )
    and f"urllib.parse({vargs[0]}) or {{ panic(err) }}",
    "urllib.parse.quote": lambda self, node, vargs: (
        self._usings.add("net.urllib") or True
    )
    and f"urllib.query_escape({vargs[0]})",
    "urllib.request.urlopen": lambda self, node, vargs: (
        self._usings.add("net.http") or True
    )
    and f"net.http.get({vargs[0]})",
    "requests.get": lambda self, node, vargs: (self._usings.add("net.http") or True)
    and f"net.http.get({vargs[0]})",
    # sqlite3 module
    "sqlite3.connect": lambda self, node, vargs: (self._usings.add("db.sqlite") or True)
    and f"sqlite.connect({vargs[0]})",
    # threading module
    "threading.Thread": lambda self, node, vargs: "spawn /* thread target should follow */",
    # hmac module
    "hmac.new": lambda self, node, vargs: (self._usings.add("crypto.hmac") or True)
    and f"hmac.new({vargs[0]}, {vargs[1]}, {vargs[2]})",
    # decimal/fractions
    "decimal.Decimal": lambda self, node, vargs: (self._usings.add("math.big") or True)
    and f"big.from_string({vargs[0]})",
    # statistics
    "statistics.mean": lambda self, node, vargs: (self._usings.add("arrays") or True)
    and f"(arrays.sum({vargs[0]}) or {{ 0.0 }}) / {vargs[0]}.len",
    # argparse
    "argparse.ArgumentParser": lambda self, node, vargs: (
        self._usings.add("flag") or self._usings.add("os") or True
    )
    and "flag.new_flag_parser(os.args)",
    # uuid module
    "uuid.uuid4": lambda self, node, vargs: (self._usings.add("rand") or True)
    and "rand.uuid_v4()",
    # tempfile module
    "tempfile.gettempdir": lambda self, node, vargs: (self._usings.add("os") or True)
    and "os.vtmp_dir()",
    # glob module
    "glob.glob": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.ls({vargs[0]}) or {{ []string{{}} }}",
    # binascii module
    "binascii.hexlify": lambda self, node, vargs: (
        self._usings.add("encoding.hex") or True
    )
    and f"hex.encode({vargs[0]})",
    "binascii.unhexlify": lambda self, node, vargs: (
        self._usings.add("encoding.hex") or True
    )
    and f"hex.decode({vargs[0]}) or {{ []u8{{}} }}",
    # bisect module
    "bisect.bisect_left": lambda self, node, vargs: (self._usings.add("arrays") or True)
    and f"arrays.binary_search({vargs[0]}, {vargs[1]})",
    # copy module
    "copy.copy": lambda self, node, vargs: f"{vargs[0]}.clone()",
    "copy.deepcopy": lambda self, node, vargs: f"{vargs[0]}.clone()",
    # compression modules
    "zlib.decompress": lambda self, node, vargs: (
        self._usings.add("compress.zlib") or True
    )
    and f"zlib.decompress({vargs[0]}) or {{ []u8{{}} }}",
    "gzip.decompress": lambda self, node, vargs: (
        self._usings.add("compress.gzip") or True
    )
    and f"gzip.decompress({vargs[0]}) or {{ []u8{{}} }}",
    # unittest module
    "unittest.TestCase": lambda self, node, vargs: "",
    "self.assertEqual": lambda self, node, vargs: f"assert {vargs[0]} == {vargs[1]}",
    "self.assertTrue": lambda self, node, vargs: f"assert {vargs[0]}",
    "self.assertFalse": lambda self, node, vargs: f"assert !({vargs[0]})",
    # heapq module
    "heapq.heappush": lambda self, node, vargs: f"{vargs[0]} << {vargs[1]}; {vargs[0]}.sort()",
    "heapq.heappop": lambda self, node, vargs: f"{vargs[0]}.pop()",
    # collections module
    "collections.deque": lambda self, node, vargs: f"{vargs[0]}.clone()",
    "str.appendleft": lambda self, node, vargs: f"{self.visit(node.func.value)}.insert(0, {vargs[0]})",
    "str.popleft": lambda self, node, vargs: f"{self.visit(node.func.value)}.delete(0)",
    "collections.Counter": lambda self, node, vargs: "map[string]int{}",
    # pickle module (mapped to json as V's primary serialization)
    "pickle.dumps": lambda self, node, vargs: (self._usings.add("json") or True)
    and f"json.encode({vargs[0]})",
    "pickle.loads": lambda self, node, vargs: (self._usings.add("json") or True)
    and f"json.decode(T, {vargs[0]}) or {{ panic(err) }}",
    # platform module
    "platform.system": lambda self, node, vargs: "/* $if windows { 'Windows' } $else { 'Linux' } */ 'Windows'",
    # warnings module
    "warnings.warn": lambda self, node, vargs: f"eprintln('Warning: ' + {vargs[0]})",
    # abc module/inspect
    "abc.ABC": lambda self, node, vargs: "",
    "abc.abstractmethod": lambda self, node, vargs: "",
    "inspect.isfunction": lambda self, node, vargs: "true",
    # array module (mapped to V native arrays)
    "array.array": lambda self, node, vargs: f"{vargs[1]}.clone()",
    # contextlib module
    "contextlib.closing": lambda self, node, vargs: f"defer {{ {vargs[0]}.close() }}",
    # fnmatch module
    "fnmatch.fnmatch": lambda self, node, vargs: f"{vargs[0]}.match_glob({vargs[1]})",
    # locale module
    "locale.setlocale": lambda self, node, vargs: "",
    "locale.format_string": lambda self, node, vargs: f"{vargs[0]} % {vargs[1]}",
    # resource module
    "resource.getrlimit": lambda self, node, vargs: "0",
    # signal module
    "signal.signal": lambda self, node, vargs: (self._usings.add("os") or True)
    and f"os.signal_opt({vargs[0]}, {vargs[1]})",
    # xml module
    "xml.etree.ElementTree.fromstring": lambda self, node, vargs: (
        self._usings.add("encoding.xml") or True
    )
    and f"/* xml.parse_string({vargs[0]}) */ ''",
    "ET.fromstring": lambda self, node, vargs: (
        self._usings.add("encoding.xml") or True
    )
    and f"/* xml.parse_string({vargs[0]}) */ ''",
    # struct module
    "struct.pack": lambda self, node, vargs: (
        self._usings.add("encoding.binary") or True
    )
    and f"binary.pack({', '.join(vargs)})",
    "struct.unpack": lambda self, node, vargs: (
        self._usings.add("encoding.binary") or True
    )
    and f"binary.unpack({', '.join(vargs)})",
    # queue module (mapped to V channels)
    "queue.Queue": lambda self, node, vargs: "chan int{}",  # Defaulting to int for placeholder
    "Queue.put": lambda self, node, vargs: f"{self.visit(node.func.value)} <- {vargs[0]}",
    "Queue.get": lambda self, node, vargs: f"<- {self.visit(node.func.value)}",
    # io module
    "io.BytesIO": lambda self, node, vargs: (self._usings.add("io") or True)
    and f"io.new_bytes_reader({vargs[0]})",
    "io.StringIO": lambda self, node, vargs: (self._usings.add("io") or True)
    and f"io.new_string_reader({vargs[0]})",
    # getopt module
    "getopt.getopt": lambda self, node, vargs: (self._usings.add("os") or True)
    and "os.args[1..]",
    # pprint module
    "pprint.pprint": lambda self, node, vargs: f"dump({vargs[0]})",
    # traceback module
    "traceback.print_exc": lambda self, node, vargs: "eprintln('Exception occurred')",
    # timeit module
    "timeit.default_timer": lambda self, node, vargs: (self._usings.add("time") or True)
    and "time.now().unix()",
    # textwrap module
    "textwrap.fill": lambda self, node, vargs: f"/* {vargs[0]}.wrap({vargs[1]}) */ {vargs[0]}",
    # zipfile module
    "zipfile.ZipFile": lambda self, node, vargs: (self._usings.add("szip") or True)
    and f"szip.open({vargs[0]})",
    # tarfile module
    "tarfile.open": lambda self, node, vargs: (self._usings.add("archive.tar") or True)
    and f"tar.open({vargs[0]}, {vargs[1]})",
    # html module
    "html.escape": lambda self, node, vargs: (self._usings.add("encoding.html") or True)
    and f"html.escape({vargs[0]})",
    "html.unescape": lambda self, node, vargs: (
        self._usings.add("encoding.html") or True
    )
    and f"html.unescape({vargs[0]})",
    # operator module
    "operator.add": lambda self, node, vargs: f"({vargs[0]} + {vargs[1]})",
    "operator.sub": lambda self, node, vargs: f"({vargs[0]} - {vargs[1]})",
    "operator.mul": lambda self, node, vargs: f"({vargs[0]} * {vargs[1]})",
    "operator.truediv": lambda self, node, vargs: f"({vargs[0]} / {vargs[1]})",
    # secrets module
    "secrets.token_bytes": lambda self, node, vargs: (
        self._usings.add("crypto.rand") or True
    )
    and f"rand.bytes({vargs[0]} or 32)",
    "secrets.token_hex": lambda self, node, vargs: (
        self._usings.add("crypto.rand") or True
    )
    and f"rand.bytes({vargs[0]} or 32).hex()",
    # difflib module
    "difflib.SequenceMatcher": lambda self, node, vargs: "/* Comparison placeholder */ diff.SequenceMatcher{}",
    # calendar module
    "calendar.monthrange": lambda self, node, vargs: (self._usings.add("time") or True)
    and f"[0, time.days_in_month({vargs[1]}, {vargs[0]}) or {{ 0 }}]",
    # colorsys module
    "colorsys.rgb_to_hls": lambda self, node, vargs: f"/* Color math placeholder */ {vargs[0]}",
    # functools module
    "functools.reduce": lambda self, node, vargs: (self._usings.add("arrays") or True)
    and f"arrays.reduce({vargs[1]}, {vargs[0]})",
    # http.client module
    "http.client.HTTPConnection": lambda self, node, vargs: (
        self._usings.add("net.http") or True
    )
    and f"net.http.get({vargs[0]})",
    # smtplib module
    "smtplib.SMTP": lambda self, node, vargs: (self._usings.add("net.smtp") or True)
    and (
        f"smtp.Client{{server: {vargs[0]}}}"
        if vargs
        else "smtp.Client{server: 'localhost'}"
    ),
    # poplib / imaplib modules
    "poplib.POP3": lambda self, node, vargs: "/* Email retrieval placeholder */ 0",
    "imaplib.IMAP4": lambda self, node, vargs: "/* Email retrieval placeholder */ 0",
    # xmlrpc module
    "xmlrpc.client.ServerProxy": lambda self, node, vargs: f"/* RPC placeholder for {vargs[0]} */ 0",
    # concurrent.futures module
    "concurrent.futures.ThreadPoolExecutor": lambda self, node, vargs: "/* Concurrency pool placeholder */ 0",
    "concurrent.futures.ProcessPoolExecutor": lambda self, node, vargs: "/* Concurrency pool placeholder */ 0",
    "ThreadPoolExecutor.submit": lambda self, node, vargs: f"spawn {vargs[0]}({', '.join(vargs[1:])})",
}

STDLIB_ATTR_DISPATCH_TABLE: Dict[str, Callable] = {
    "math.pi": lambda self, node: (self._usings.add("math") or True) and "math.pi",
    "math.e": lambda self, node: (self._usings.add("math") or True) and "math.e",
    "math.tau": lambda self, node: (self._usings.add("math") or True)
    and "(math.pi * 2.0)",
    "math.inf": lambda self, node: (self._usings.add("math") or True) and "math.inf(1)",
    "math.nan": lambda self, node: (self._usings.add("math") or True) and "math.nan()",
    # sys
    "sys.argv": lambda self, node: (self._usings.add("os") or True) and "os.args",
    "sys.stdin": lambda self, node: (self._usings.add("os") or True) and "os.stdin",
    "sys.stdout": lambda self, node: (self._usings.add("os") or True) and "os.stdout",
    "sys.stderr": lambda self, node: (self._usings.add("os") or True) and "os.stderr",
    # os
    "os.environ": lambda self, node: (self._usings.add("os") or True)
    and "os.environ()",
}

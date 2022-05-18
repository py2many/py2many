import string


abstract type AbstractParser end
C_NONE, C_BACKSLASH, C_STRING, C_BRACKET = collect(0:3)
if false
function dump()
write(sys.__stdout__, join(map(str, stuff), " ") + "\n")
end

end
_synchre = compile(re, "\n    ^\n    [ \\t]*\n    (?: if\n    |   for\n    |   while\n    |   else\n    |   def\n    |   return\n    |   assert\n    |   break\n    |   class\n    |   continue\n    |   elif\n    |   try\n    |   except\n    |   raise\n    |   import\n    )\n    \\b\n", re.VERBOSE | re.MULTILINE).search
_junkre = compile(re, "\n    [ \\t]*\n    (?: \\# \\S .* )?\n    \\n\n", re.VERBOSE).match
_match_stringre = compile(re, "\n    \\\"\"\" [^\"\\\\]* (?:\n                     (?: \\\\. | \"(?!\"\") )\n                     [^\"\\\\]*\n                 )*\n    (?: \\\"\"\" )?\n\n|   \" [^\"\\\\\\n]* (?: \\\\. [^\"\\\\\\n]* )* \"?\n\n|   \'\'\' [^\'\\\\]* (?:\n                   (?: \\\\. | \'(?!\'\') )\n                   [^\'\\\\]*\n                )*\n    (?: \'\'\' )?\n\n|   \' [^\'\\\\\\n]* (?: \\\\. [^\'\\\\\\n]* )* \'?\n", re.VERBOSE | re.DOTALL).match
_itemre = compile(re, "\n    [ \\t]*\n    [^\\s#\\\\]    # if we match, m.end()-1 is the interesting char\n", re.VERBOSE).match
_closere = compile(re, "\n    \\s*\n    (?: return\n    |   break\n    |   continue\n    |   raise\n    |   pass\n    )\n    \\b\n", re.VERBOSE).match
_chew_ordinaryre = compile(re, "\n    [^[\\](){}#\'\"\\\\]+\n", re.VERBOSE).match
_tran = repeat(["x"],256)
for ch in "({["
_tran[Int(codepoint(ch)) + 1] = "("
end
for ch in ")}]"
_tran[Int(codepoint(ch)) + 1] = ")"
end
for ch in "\"\'\\\n#"
_tran[Int(codepoint(ch)) + 1] = ch
end
_tran = join(_tran, "")
#Delete Unsupported
del(ch)
mutable struct Parser <: AbstractParser
indentwidth
tabwidth
str
study_level::Int64
goodlines::Vector{Int64}
continuation
lastch::String
lastopenbracketpos::Vector
stmt_start
end
function set_str(self::Parser, str)
@assert(length(str) == 0 || str[end] == "\n")
self.str = str
self.study_level = 0
end

function find_good_parse_start(self::Parser, use_ps1, is_char_in_string = nothing)
str, pos = (self.str, nothing)
if use_ps1
ps1 = "\n" + sys.ps1
i = rfind(str, ps1)
if i >= 0
pos = i + length(ps1)
self.str = (str[begin:pos - 1] + "\n") + str[pos + 1:end]
end
return pos
end
if !(is_char_in_string)
return nothing
end
limit = length(str)
for tries in 0:4
i = rfind(str, ":\n", 0, limit)
if i < 0
has_break = true
break;
end
i = rfind(str, "\n", 0, i) + 1
m = _synchre(str, i, limit)
if m && !is_char_in_string(start(m))
pos = start(m)
has_break = true
break;
end
limit = i
end
if pos === nothing
m = _synchre(str)
if m && !is_char_in_string(start(m))
pos = start(m)
end
return pos
end
i = pos + 1
while true
m = _synchre(str, i)
if m
s, i = span(m)
if !is_char_in_string(s)
pos = s
end
else
break;
end
end
return pos
end

function set_lo(self::Parser, lo)
@assert(lo == 0 || self.str[lo] == "\n")
if lo > 0
self.str = self.str[lo + 1:end]
end
end

function _study1(self::Parser)
if self.study_level >= 1
return
end
self.study_level = 1
str = self.str
str = translate(str, _tran)
str = replace(str, "xxxxxxxx", "x")
str = replace(str, "xxxx", "x")
str = replace(str, "xx", "x")
str = replace(str, "xx", "x")
str = replace(str, "\nx", "\n")
continuation = C_NONE
level = 0
lno = 0
self.goodlines = [0]
goodlines = [0]
push_good = goodlines.append
i, n = (0, length(str))
while i < n
ch = str[i + 1]
i = i + 1
if ch == "x"
continue;
end
if ch == "\n"
lno = lno + 1
if level == 0
push_good(lno)
end
continue;
end
if ch == "("
level = level + 1
continue;
end
if ch == ")"
if level
level = level - 1
end
continue;
end
if ch == "\"" || ch == "\'"
quote_ = ch
if str[i:i + 2] == (quote_*3)
quote_ = quote_*3
end
w = length(quote_) - 1
i = i + w
while i < n
ch = str[i + 1]
i = i + 1
if ch == "x"
continue;
end
if str[i:i + w] == quote_
i = i + w
has_break = true
break;
end
if ch == "\n"
lno = lno + 1
if w == 0
if level == 0
push_good(lno)
end
has_break = true
break;
end
continue;
end
if ch == "\\"
@assert(i < n)
if str[i + 1] == "\n"
lno = lno + 1
end
i = i + 1
continue;
end
end
continue;
end
if ch == "#"
i = find(str, "\n", i)
@assert(i >= 0)
continue;
end
@assert(ch == "\\")
@assert(i < n)
if str[i + 1] == "\n"
lno = lno + 1
if (i + 1) === n
continuation = C_BACKSLASH
end
end
i = i + 1
end
if continuation != C_STRING && level > 0
continuation = C_BRACKET
end
self.continuation = continuation
@assert(continuation == C_NONE == goodlines[end] === lno)
if goodlines[end] != lno
push_good(lno)
end
end

function get_continuation_type(self::Parser)
_study1(self)
return self.continuation
end

function _study2(self::Parser)
_ws = string.whitespace
if self.study_level >= 2
return
end
_study1(self)
self.study_level = 2
str, goodlines = (self.str, self.goodlines)
i = length(goodlines) - 1
p = length(str)
while i != 0
@assert(p)
q = p
for nothing in goodlines[i]:goodlines[i + 1] - 1
p = rfind(str, "\n", 0, p - 1) + 1
end
if _junkre(str, p)
i = i - 1
else
break;
end
end
if i == 0
@assert(p == 0)
q = p
end
self.stmt_start, self.stmt_end = (p, q)
lastch = ""
stack = []
push_stack = stack.append
while p < q
m = _chew_ordinaryre(str, p, q)
if m
newp = end_(m)
i = newp - 1
while i >= p && str[i + 1] ∈ " \t\n"
i = i - 1
end
if i >= p
lastch = str[i + 1]
end
p = newp
if p >= q
has_break = true
break;
end
end
ch = str[p + 1]
if ch ∈ "([{"
push_stack(p)
lastch = ch
p = p + 1
continue;
end
if ch ∈ ")]}"
if stack
#Delete Unsupported
del(stack)
end
lastch = ch
p = p + 1
continue;
end
if ch == "\"" || ch == "\'"
lastch = ch
p = end_(_match_stringre(str, p, q))
continue;
end
if ch == "#"
p = find(str, "\n", p, q) + 1
@assert(p > 0)
continue;
end
@assert(ch == "\\")
p = p + 1
@assert(p < q)
if str[p + 1] != "\n"
lastch = ch + str[p + 1]
end
p = p + 1
end
self.lastch = lastch
if stack
self.lastopenbracketpos = stack[end]
end
end

function compute_bracket_indent(self::Parser)::Int64
_study2(self)
@assert(self.continuation == C_BRACKET)
j = self.lastopenbracketpos
str = self.str
n = length(str)
origi = rfind(str, "\n", 0, j) + 1
i = rfind(str, "\n", 0, j) + 1
j = j + 1
while j < n
m = _itemre(str, j)
if m
j = end_(m) - 1
extra = 0
has_break = true
break;
else
i = find(str, "\n", j) + 1
j = find(str, "\n", j) + 1
end
end
return length(expandtabs(str[i + 1:j], self.tabwidth)) + extra
end

function get_num_lines_in_stmt(self::Parser)::Int64
_study1(self)
goodlines = self.goodlines
return goodlines[end] - goodlines[end]
end

function compute_backslash_indent(self::Parser)::Int64
_study2(self)
@assert(self.continuation == C_BACKSLASH)
str = self.str
i = self.stmt_start
while str[i + 1] ∈ " \t"
i = i + 1
end
startpos = i
endpos = find(str, "\n", startpos) + 1
found = 0
level = 0
while i < endpos
ch = str[i + 1]
if ch ∈ "([{"
level = level + 1
i = i + 1
elseif ch ∈ ")]}"
if level
level = level - 1
end
i = i + 1
elseif ch == "\"" || ch == "\'"
i = end_(_match_stringre(str, i, endpos))
elseif ch == "#"
has_break = true
break;
elseif level == 0 && ch == "=" && i == 0 || str[i] ∉ "=<>!" && str[i + 2] != "="
found = 1
has_break = true
break;
else
i = i + 1
end
end
if found
i = i + 1
found = match(re, "\\s*\\\\", str[i + 1:endpos]) === nothing
end
if !(found) != 0
i = startpos
while str[i + 1] ∉ " \t\n"
i = i + 1
end
end
return length(expandtabs(str[self.stmt_start + 1:i], self.tabwidth)) + 1
end

function get_base_indent_string(self::Parser)
_study2(self)
i, n = (self.stmt_start, self.stmt_end)
j = i
str = self.str
while j < n && str[j + 1] ∈ " \t"
j = j + 1
end
return str[i + 1:j]
end

function is_block_opener(self::Parser)::Bool
_study2(self)
return self.lastch == ":"
end

function is_block_closer(self::Parser)::Bool
_study2(self)
return _closere(self.str, self.stmt_start) != nothing
end

function get_last_open_bracket_pos(self::Parser)
_study2(self)
return self.lastopenbracketpos
end

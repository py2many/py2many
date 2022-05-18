using StringEncodings

import string
import tokenize
include("PyParse.jl")
using win32com_.gen_py: default_scintilla_encoding
abstract type AbstractAutoIndent end
abstract type AbstractIndentSearcher end
if sys.version_info < (3,)
token_generator = tokenize.generate_tokens
else
token_generator = tokenize.tokenize
end
mutable struct AutoIndent <: AbstractAutoIndent
context_use_ps1
editwin
indentwidth
tabwidth
text
usetabs
auto_indent
keydefs::Dict{String, Vector{String}}
menudefs::Vector{Tuple{Union{String, Vector{Tuple{String}}}}}
num_context_lines::Tuple{Int64}
unix_keydefs::Dict{String, Vector{String}}
windows_keydefs::Dict{String, Vector{String}}

                    AutoIndent(context_use_ps1, editwin, indentwidth, tabwidth, text, usetabs, auto_indent = newline_and_indent_event, keydefs::Dict{String, Vector{String}} = Dict("<<smart-backspace>>" => ["<Key-BackSpace>"], "<<newline-and-indent>>" => ["<Key-Return>", "<KP_Enter>"], "<<smart-indent>>" => ["<Key-Tab>"]), menudefs::Vector{Tuple{Union{String, Vector{Tuple{String}}}}} = [("edit", [nothing, ("_Indent region", "<<indent-region>>"), ("_Dedent region", "<<dedent-region>>"), ("Comment _out region", "<<comment-region>>"), ("U_ncomment region", "<<uncomment-region>>"), ("Tabify region", "<<tabify-region>>"), ("Untabify region", "<<untabify-region>>"), ("Toggle tabs", "<<toggle-tabs>>"), ("New indent width", "<<change-indentwidth>>")])], num_context_lines::Tuple{Int64} = (50, 500, 5000000), unix_keydefs::Dict{String, Vector{String}} = Dict("<<indent-region>>" => ["<Alt-bracketright>", "<Meta-bracketright>", "<Control-bracketright>"], "<<dedent-region>>" => ["<Alt-bracketleft>", "<Meta-bracketleft>", "<Control-bracketleft>"], "<<comment-region>>" => ["<Alt-Key-3>", "<Meta-Key-3>"], "<<uncomment-region>>" => ["<Alt-Key-4>", "<Meta-Key-4>"], "<<tabify-region>>" => ["<Alt-Key-5>", "<Meta-Key-5>"], "<<untabify-region>>" => ["<Alt-Key-6>", "<Meta-Key-6>"], "<<toggle-tabs>>" => ["<Alt-Key-t>"], "<<change-indentwidth>>" => ["<Alt-Key-u>"]), windows_keydefs::Dict{String, Vector{String}} = Dict("<<indent-region>>" => ["<Control-bracketright>"], "<<dedent-region>>" => ["<Control-bracketleft>"], "<<comment-region>>" => ["<Alt-Key-3>"], "<<uncomment-region>>" => ["<Alt-Key-4>"], "<<tabify-region>>" => ["<Alt-Key-5>"], "<<untabify-region>>" => ["<Alt-Key-6>"], "<<toggle-tabs>>" => ["<Alt-Key-t>"], "<<change-indentwidth>>" => ["<Alt-Key-u>"])) =
                        new(context_use_ps1, editwin, indentwidth, tabwidth, text, usetabs, auto_indent, keydefs, menudefs, num_context_lines, unix_keydefs, windows_keydefs)
end
function config(self::AutoIndent)
for (key, value) in items(options)
if key == "usetabs"
self.usetabs = value
elseif key == "indentwidth"
self.indentwidth = value
elseif key == "tabwidth"
self.tabwidth = value
elseif key == "context_use_ps1"
self.context_use_ps1 = value
else
throw(KeyError("bad option name: %s" % repr(key)))
end
end
end

function set_indentation_params(self::AutoIndent, ispythonsource, guess = 1)
if guess && ispythonsource
i = guess_indent(self)
if 2 <= i <= 8
self.indentwidth = i
end
if self.indentwidth != self.tabwidth
self.usetabs = 0
end
end
set_tabwidth(self.editwin, self.tabwidth)
end

function smart_backspace_event(self::AutoIndent, event)::String
text = self.text
first, last = get_selection_indices(self.editwin)
if first && last
delete(text, first, last)
mark_set(text, "insert", first)
return "break"
end
chars = get(text, "insert linestart", "insert")
if chars == ""
if compare(text, "insert", ">", "1.0")
delete(text, "insert-1c")
else
bell(text)
end
return "break"
end
if chars[end] ∉ " \t"
delete(text, "insert-1c")
return "break"
end
have = length(expandtabs(chars, self.tabwidth))
@assert(have > 0)
want = Int((have - 1) / self.indentwidth)*self.indentwidth
ncharsdeleted = 0
while true
chars = chars[begin:-1]
ncharsdeleted = ncharsdeleted + 1
have = length(expandtabs(chars, self.tabwidth))
if have <= want || chars[end] ∉ " \t"
has_break = true
break;
end
end
undo_block_start(text)
delete(text, "insert-%dc" % ncharsdeleted, "insert")
if have < want
insert(text, "insert", repeat(" ",(want - have)))
end
undo_block_stop(text)
return "break"
end

function smart_indent_event(self::AutoIndent, event)::String
text = self.text
first, last = get_selection_indices(self.editwin)
undo_block_start(text)
try
if first && last
if index2line(first) != index2line(last)
return indent_region_event(self, event)
end
delete(text, first, last)
mark_set(text, "insert", first)
end
prefix = get(text, "insert linestart", "insert")
raw, effective = classifyws(prefix, self.tabwidth)
if raw == length(prefix)
reindent_to(self, effective + self.indentwidth)
else
if self.usetabs
pad = "\t"
else
effective = length(expandtabs(prefix, self.tabwidth))
n = self.indentwidth
pad = repeat(" ",(n - (effective % n)))
end
insert(text, "insert", pad)
end
see(text, "insert")
return "break"
finally
undo_block_stop(text)
end
end

function newline_and_indent_event(self::AutoIndent, event)::String
text = self.text
first, last = get_selection_indices(self.editwin)
undo_block_start(text)
try
if first && last
delete(text, first, last)
mark_set(text, "insert", first)
end
line = get(text, "insert linestart", "insert")
i, n = (0, length(line))
while i < n && line[i + 1] ∈ " \t"
i = i + 1
end
if i === n
delete(text, "insert - %d chars" % i, "insert")
insert(text, "insert linestart", "\n")
return "break"
end
indent = line[begin:i]
i = 0
while line && line[end] ∈ " \t"
line = line[begin:-1]
i = i + 1
end
if i != 0
delete(text, "insert - %d chars" % i, "insert")
end
while get(text, "insert") ∈ " \t"
delete(text, "insert")
end
insert(text, "insert", "\n")
lno = index2line(index(text, "insert"))
y = Parser(PyParse, self.indentwidth, self.tabwidth)
for context in self.num_context_lines
startat = max(lno - context, 1)
startatindex = repr(startat) + ".0"
rawtext = get(text, startatindex, "insert")
set_str(y, rawtext)
bod = find_good_parse_start(y, self.context_use_ps1, _build_char_in_string_func(self, startatindex))
if bod != nothing || startat == 1
has_break = true
break;
end
end
set_lo(y, bod || 0)
c = get_continuation_type(y)
if c != PyParse.C_NONE
if c == PyParse.C_STRING
insert(text, "insert", indent)
elseif c == PyParse.C_BRACKET
reindent_to(self, compute_bracket_indent(y))
elseif c == PyParse.C_BACKSLASH
if get_num_lines_in_stmt(y) > 1
insert(text, "insert", indent)
else
reindent_to(self, compute_backslash_indent(y))
end
else
@assert(0)
end
return "break"
end
indent = get_base_indent_string(y)
insert(text, "insert", indent)
if is_block_opener(y)
smart_indent_event(self, event)
elseif indent && is_block_closer(y)
smart_backspace_event(self, event)
end
return "break"
finally
see(text, "insert")
undo_block_stop(text)
end
end

function _build_char_in_string_func(self::AutoIndent, startindex)
function inner(offset, _startindex = startindex, _icis = self.editwin.is_char_in_string)
return _icis(_startindex + ("+%dc" % offset))
end

return inner
end

function indent_region_event(self::AutoIndent, event)::String
head, tail, chars, lines = get_region(self)
for pos in 0:length(lines) - 1
line = lines[pos + 1]
if line
raw, effective = classifyws(line, self.tabwidth)
effective = effective + self.indentwidth
lines[pos + 1] = _make_blanks(self, effective) + line[raw + 1:end]
end
end
set_region(self, head, tail, chars, lines)
return "break"
end

function dedent_region_event(self::AutoIndent, event)::String
head, tail, chars, lines = get_region(self)
for pos in 0:length(lines) - 1
line = lines[pos + 1]
if line
raw, effective = classifyws(line, self.tabwidth)
effective = max(effective - self.indentwidth, 0)
lines[pos + 1] = _make_blanks(self, effective) + line[raw + 1:end]
end
end
set_region(self, head, tail, chars, lines)
return "break"
end

function comment_region_event(self::AutoIndent, event)
head, tail, chars, lines = get_region(self)
for pos in 0:length(lines) - 2
line = lines[pos + 1]
lines[pos + 1] = "##" + line
end
set_region(self, head, tail, chars, lines)
end

function uncomment_region_event(self::AutoIndent, event)
head, tail, chars, lines = get_region(self)
for pos in 0:length(lines) - 1
line = lines[pos + 1]
if !(line)
continue;
end
if line[begin:2] == "##"
line = line[3:end]
elseif line[begin:1] == "#"
line = line[2:end]
end
lines[pos + 1] = line
end
set_region(self, head, tail, chars, lines)
end

function tabify_region_event(self::AutoIndent, event)
head, tail, chars, lines = get_region(self)
tabwidth = _asktabwidth(self)
for pos in 0:length(lines) - 1
line = lines[pos + 1]
if line
raw, effective = classifyws(line, tabwidth)
ntabs, nspaces = div(effective)
lines[pos + 1] = "\t"*ntabs * " "*nspaces + line[raw + 1:end]
end
end
set_region(self, head, tail, chars, lines)
end

function untabify_region_event(self::AutoIndent, event)
head, tail, chars, lines = get_region(self)
tabwidth = _asktabwidth(self)
for pos in 0:length(lines) - 1
lines[pos + 1] = expandtabs(lines[pos + 1], tabwidth)
end
set_region(self, head, tail, chars, lines)
end

function toggle_tabs_event(self::AutoIndent, event)::String
if askyesno(self.editwin, "Toggle tabs", ("Turn tabs " + ("on", "off")[self.usetabs + 1]) * "?", self.text)
self.usetabs = !(self.usetabs)
end
return "break"
end

function change_tabwidth_event(self::AutoIndent, event)::String
new = _asktabwidth(self)
if new != self.tabwidth
self.tabwidth = new
set_indentation_params(self, 0)
end
return "break"
end

function change_indentwidth_event(self::AutoIndent, event)::String
new = askinteger(self.editwin, "Indent width", "New indent width (1-16)", self.text, self.indentwidth, 1, 16)
if new && new != self.indentwidth
self.indentwidth = new
end
return "break"
end

function get_region(self::AutoIndent)::Tuple
text = self.text
first, last = get_selection_indices(self.editwin)
if first && last
head = index(text, first + " linestart")
tail = index(text, last + "-1c lineend +1c")
else
head = index(text, "insert linestart")
tail = index(text, "insert lineend +1c")
end
chars = get(text, head, tail)
lines = split(chars, "\n")
return (head, tail, chars, lines)
end

function set_region(self::AutoIndent, head, tail, chars, lines)
text = self.text
newchars = join(lines, "\n")
if newchars == chars
bell(text)
return
end
tag_remove(text, "sel", "1.0", "end")
mark_set(text, "insert", head)
undo_block_start(text)
delete(text, head, tail)
insert(text, head, newchars)
undo_block_stop(text)
tag_add(text, "sel", head, "insert")
end

function _make_blanks(self::AutoIndent, n)::String
if self.usetabs
ntabs, nspaces = div(n)
return "\t"*ntabs * " "*nspaces
else
return " "*n
end
end

function reindent_to(self::AutoIndent, column)
text = self.text
undo_block_start(text)
if compare(text, "insert linestart", "!=", "insert")
delete(text, "insert linestart", "insert")
end
if column
insert(text, "insert", _make_blanks(self, column))
end
undo_block_stop(text)
end

function _asktabwidth(self::AutoIndent)
return askinteger(self.editwin, "Tab width", "Spaces per tab?", self.text, self.tabwidth, 1, 16) || self.tabwidth
end

function guess_indent(self::AutoIndent)::Any
opener, indented = run(IndentSearcher(self.text, self.tabwidth))
if opener && indented
raw, indentsmall = classifyws(opener, self.tabwidth)
raw, indentlarge = classifyws(indented, self.tabwidth)
else
indentsmall = 0
indentlarge = 0
end
return indentlarge - indentsmall
end

function index2line(index)::Int64
return Int(floor(float(index)))
end

function classifyws(s, tabwidth)
raw = 0
effective = 0
for ch in s
if ch == " "
raw = raw + 1
effective = effective + 1
elseif ch == "\t"
raw = raw + 1
effective = ((effective ÷ tabwidth) + 1)*tabwidth
else
break;
end
end
return (raw, effective)
end

mutable struct IndentSearcher <: AbstractIndentSearcher
text
tabwidth
i::Int64
finished::Int64
blkopenline
indentedline
readline
end
function readline(self::IndentSearcher)
if self.finished != 0
val = ""
else
i = self.i + 1
self.i = self.i + 1
mark = repr(i) + ".0"
if compare(self.text, mark, ">=", "end")
val = ""
else
val = get(self.text, mark, mark * " lineend+1c")
end
end
return encode(val, default_scintilla_encoding)
end

function run(self::IndentSearcher)::Tuple
OPENERS = ("class", "def", "for", "if", "try", "while")
INDENT = tokenize.INDENT
NAME = tokenize.NAME
save_tabsize = tokenize.tabsize
tokenize.tabsize = self.tabwidth
try
try
for (typ, token, start, end_, line) in token_generator(self.readline)
if typ == NAME && token ∈ OPENERS
self.blkopenline = line
elseif typ == INDENT && self.blkopenline
self.indentedline = line
has_break = true
break;
end
end
catch exn
if exn isa (tokenize.TokenError, IndentationError)
#= pass =#
end
end
finally
tokenize.tabsize = save_tabsize
end
return (self.blkopenline, self.indentedline)
end

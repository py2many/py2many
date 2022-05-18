import string

abstract type AbstractFormatParagraph end
mutable struct FormatParagraph <: AbstractFormatParagraph
editwin
keydefs::Dict{String, Vector{String}}
menudefs::Vector{Tuple{Union{String, Vector{Tuple{String}}}}}
unix_keydefs::Dict{String, Vector{String}}

                    FormatParagraph(editwin, keydefs::Dict{String, Vector{String}} = Dict("<<format-paragraph>>" => ["<Alt-q>"]), menudefs::Vector{Tuple{Union{String, Vector{Tuple{String}}}}} = [("edit", [("Format Paragraph", "<<format-paragraph>>")])], unix_keydefs::Dict{String, Vector{String}} = Dict("<<format-paragraph>>" => ["<Meta-q>"])) =
                        new(editwin, keydefs, menudefs, unix_keydefs)
end
function close(self::FormatParagraph)
self.editwin = nothing
end

function format_paragraph_event(self::FormatParagraph, event)
text = self.editwin.text
first, last = get_selection_indices(self.editwin)
if first && last
data = get(text, first, last)
comment_header = ""
else
first, last, comment_header, data = find_paragraph(text, index(text, "insert"))
end
if comment_header
lines = split(data, "\n")
lines = map((st, l) -> st[l + 1:end], lines)
data = join(lines, "\n")
format_width = max(70 - length(comment_header), 20)
newdata = reformat_paragraph(data, format_width)
newdata = split(newdata, "\n")
block_suffix = ""
if !(newdata[end])
block_suffix = "\n"
newdata = newdata[begin:-1]
end
builder = (item, prefix) -> prefix + item
newdata = join([builder(d) for d in newdata], "\n") + block_suffix
else
newdata = reformat_paragraph(data)
end
tag_remove(text, "sel", "1.0", "end")
if newdata != data
mark_set(text, "insert", first)
undo_block_start(text)
delete(text, first, last)
insert(text, first, newdata)
undo_block_stop(text)
else
mark_set(text, "insert", last)
end
see(text, "insert")
end

function find_paragraph(text, mark)::Tuple
lineno, col = collect(map(int, split(mark, ".")))
line = get(text, "%d.0" % lineno, "%d.0 lineend" % lineno)
while compare(text, "%d.0" % lineno, "<", "end") && is_all_white(line)
lineno = lineno + 1
line = get(text, "%d.0" % lineno, "%d.0 lineend" % lineno)
end
first_lineno = lineno
comment_header = get_comment_header(line)
comment_header_len = length(comment_header)
while get_comment_header(line) == comment_header && !is_all_white(line[comment_header_len + 1:end])
lineno = lineno + 1
line = get(text, "%d.0" % lineno, "%d.0 lineend" % lineno)
end
last = "%d.0" % lineno
lineno = first_lineno - 1
line = get(text, "%d.0" % lineno, "%d.0 lineend" % lineno)
while lineno > 0 && get_comment_header(line) == comment_header && !is_all_white(line[comment_header_len + 1:end])
lineno = lineno - 1
line = get(text, "%d.0" % lineno, "%d.0 lineend" % lineno)
end
first = "%d.0" % (lineno + 1)
return (first, last, comment_header, get(text, first, last))
end

function reformat_paragraph(data, limit = 70)
lines = split(data, "\n")
i = 0
n = length(lines)
while i < n && is_all_white(lines[i + 1])
i = i + 1
end
if i >= n
return data
end
indent1 = get_indent(lines[i + 1])
if (i + 1) < n && !is_all_white(lines[i + 2])
indent2 = get_indent(lines[i + 2])
else
indent2 = indent1
end
new = lines[begin:i]
partial = indent1
while i < n && !is_all_white(lines[i + 1])
words = split(re, "(\\s+)", lines[i + 1])
for j in 0:2:length(words) - 1
word = words[j + 1]
if !(word)
continue;
end
if length(expandtabs(partial + word)) > limit && partial != indent1
append(new, rstrip(partial))
partial = indent2
end
partial = (partial + word) * " "
if (j + 1) < length(words) && words[j + 2] != " "
partial = partial * " "
end
end
i = i + 1
end
append(new, rstrip(partial))
extend(new, lines[i + 1:end])
return join(new, "\n")
end

function is_all_white(line)::Bool
return match(re, "^\\s*\$", line) != nothing
end

function get_indent(line)
return group(match(re, "^(\\s*)", line))
end

function get_comment_header(line)::String
m = match(re, "^(\\s*#*)", line)
if m === nothing
return ""
end
return group(m, 1)
end

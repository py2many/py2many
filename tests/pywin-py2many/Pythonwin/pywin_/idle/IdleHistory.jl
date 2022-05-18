import string
abstract type AbstractHistory end
mutable struct History <: AbstractHistory
text
history::Vector
history_prefix
history_pointer
output_sep

            History(text, output_sep = "\n") = begin
                text.bind("<<history-previous>>", history_prev)
text.bind("<<history-next>>", history_next)
                new(text, output_sep )
            end
end
function history_next(self::History, event)::String
history_do(self, 0)
return "break"
end

function history_prev(self::History, event)::String
history_do(self, 1)
return "break"
end

function _get_source(self::History, start, end_)
lines = split(get(self.text, start, end_), self.output_sep)
return join(lines, "\n")
end

function _put_source(self::History, where, source)
output = join(split(source, "\n"), self.output_sep)
insert(self.text, where, output)
end

function history_do(self::History, reverse)
nhist = length(self.history)
pointer = self.history_pointer
prefix = self.history_prefix
if pointer != nothing && prefix != nothing
if compare(self.text, "insert", "!=", "end-1c") || _get_source(self, "iomark", "end-1c") != self.history[pointer + 1]
pointer = nothing
prefix = nothing
end
end
if pointer === nothing || prefix === nothing
prefix = _get_source(self, "iomark", "end-1c")
if reverse
pointer = nhist
else
pointer = -1
end
end
nprefix = length(prefix)
while true
if reverse
pointer = pointer - 1
else
pointer = pointer + 1
end
if pointer < 0 || pointer >= nhist
bell(self.text)
if _get_source(self, "iomark", "end-1c") != prefix
delete(self.text, "iomark", "end-1c")
_put_source(self, "iomark", prefix)
end
pointer = nothing
prefix = nothing
has_break = true
break;
end
item = self.history[pointer + 1]
if item[begin:nprefix] === prefix && length(item) > nprefix
delete(self.text, "iomark", "end-1c")
_put_source(self, "iomark", item)
has_break = true
break;
end
end
mark_set(self.text, "insert", "end-1c")
see(self.text, "insert")
tag_remove(self.text, "sel", "1.0", "end")
self.history_pointer = pointer
self.history_prefix = prefix
end

function history_store(self::History, source)
source = strip(source)
if length(source) > 2
try
remove(self.history, source)
catch exn
if exn isa ValueError
#= pass =#
end
end
append(self.history, source)
end
self.history_pointer = nothing
self.history_prefix = nothing
end

function recall(self::History, s)
s = strip(s)
tag_remove(self.text, "sel", "1.0", "end")
delete(self.text, "iomark", "end-1c")
mark_set(self.text, "insert", "end-1c")
insert(self.text, "insert", s)
see(self.text, "insert")
end

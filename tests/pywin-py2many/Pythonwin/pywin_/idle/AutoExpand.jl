import string

abstract type AbstractAutoExpand end
mutable struct AutoExpand <: AbstractAutoExpand
state
text
keydefs::Dict{String, Vector{String}}
menudefs::Vector{Tuple{Union{String, Vector{Tuple{String}}}}}
unix_keydefs::Dict{String, Vector{String}}
wordchars::String

                    AutoExpand(state, text, keydefs::Dict{String, Vector{String}} = Dict("<<expand-word>>" => ["<Alt-slash>"]), menudefs::Vector{Tuple{Union{String, Vector{Tuple{String}}}}} = [("edit", [("E_xpand word", "<<expand-word>>")])], unix_keydefs::Dict{String, Vector{String}} = Dict("<<expand-word>>" => ["<Meta-slash>"]), wordchars::String = (string.ascii_letters + string.digits) + "_") =
                        new(state, text, keydefs, menudefs, unix_keydefs, wordchars)
end
function expand_word_event(self::AutoExpand, event)::String
curinsert = index(self.text, "insert")
curline = get(self.text, "insert linestart", "insert lineend")
if !(self.state)
words = getwords(self)
index = 0
else
words, index, insert, line = self.state
if insert != curinsert || line != curline
words = getwords(self)
index = 0
end
end
if !(words)
bell(self.text)
return "break"
end
word = getprevword(self)
delete(self.text, "insert - %d chars" % length(word), "insert")
newword = words[index + 1]
index = (index + 1) % length(words)
if index == 0
bell(self.text)
end
insert(self.text, "insert", newword)
curinsert = index(self.text, "insert")
curline = get(self.text, "insert linestart", "insert lineend")
self.state = (words, index, curinsert, curline)
return "break"
end

function getwords(self::AutoExpand)::Vector
word = getprevword(self)
if !(word)
return []
end
before = get(self.text, "1.0", "insert wordstart")
wbefore = collect(eachmatch(Regex(("\\b" + word) * "\\w+\\b"), before))
#Delete Unsupported
del(before)
after = get(self.text, "insert wordend", "end")
wafter = collect(eachmatch(Regex(("\\b" + word) * "\\w+\\b"), after))
#Delete Unsupported
del(after)
if !(wbefore) && !(wafter)
return []
end
words = []
dict = Dict()
reverse(wbefore)
for w in wbefore
if get(dict, w)
continue;
end
push!(words, w)
dict[w] = w
end
for w in wafter
if get(dict, w)
continue;
end
push!(words, w)
dict[w] = w
end
push!(words, word)
return words
end

function getprevword(self::AutoExpand)
line = get(self.text, "insert linestart", "insert")
i = length(line)
while i > 0 && line[i] ∈ self.wordchars
i = i - 1
end
return line[i + 1:end]
end

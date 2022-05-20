#= Provides a class Stdin which can be used to emulate the regular old
sys.stdin for the PythonWin interactive window. Right now it just pops
up a raw_input() dialog. With luck, someone will integrate it into the
actual PythonWin interactive window someday.

WARNING: Importing this file automatically replaces sys.stdin with an
instance of Stdin (below). This is useful because you can just open
Stdin.py in PythonWin and hit the import button to get it set up right
if you don't feel like changing PythonWin's source. To put things back
the way they were, simply use this magic incantation:
    import sys
    sys.stdin = sys.stdin.real_file
 =#

try
get_input_line = raw_input
catch exn
if exn isa NameError
get_input_line = input
end
end
abstract type AbstractStdin end
mutable struct Stdin <: AbstractStdin
real_file
buffer::String
closed::Bool
end
function __getattr__(self::Stdin, name)
#= Forward most functions to the real sys.stdin for absolute realism. =#
if self.real_file === nothing
throw(AttributeError(name))
end
return getfield(self.real_file, :name)
end

function isatty(self::Stdin)::Int64
#= Return 1 if the file is connected to a tty(-like) device, else 0. =#
return 1
end

function read(self::Stdin, size = -1)
#= Read at most size bytes from the file (less if the read
        hits EOF or no more data is immediately available on a pipe,
        tty or similar device). If the size argument is negative or
        omitted, read all data until EOF is reached. The bytes are
        returned as a string object. An empty string is returned when
        EOF is encountered immediately. (For certain files, like ttys,
        it makes sense to continue reading after an EOF is hit.) =#
result_size = __get_lines(self, size)
return __extract_from_buffer(self, result_size)
end

function readline(self::Stdin, size = -1)
#= Read one entire line from the file. A trailing newline
        character is kept in the string2.6 (but may be absent when a file ends
        with an incomplete line). If the size argument is present and
        non-negative, it is a maximum byte count (including the trailing
        newline) and an incomplete line may be returned. An empty string is
        returned when EOF is hit immediately. Note: unlike stdio's fgets(),
        the returned string contains null characters ('\000') if they occurred
        in the input.
         =#
maximum_result_size = __get_lines(self, size, (buffer) -> "\n" ∈ buffer)
if "\n" ∈ self.buffer[begin:maximum_result_size]
result_size = find(self.buffer, "\n", 0, maximum_result_size) + 1
@assert(result_size > 0)
else
result_size = maximum_result_size
end
return __extract_from_buffer(self, result_size)
end

function __extract_from_buffer(self::Stdin, character_count)::String
#= Remove the first character_count characters from the internal buffer and
        return them.
         =#
result = self.buffer[begin:character_count]
self.buffer = self.buffer[character_count + 1:end]
return result
end

function __get_lines(self::Stdin, desired_size, done_reading = (buffer) -> false)::Int64
#= Keep adding lines to our internal buffer until done_reading(self.buffer)
        is true or EOF has been reached or we have desired_size bytes in the buffer.
        If desired_size < 0, we are never satisfied until we reach EOF. If done_reading
        is not supplied, it is not consulted.

        If desired_size < 0, returns the length of the internal buffer. Otherwise,
        returns desired_size.
         =#
while !done_reading(self.buffer) && desired_size < 0 || length(self.buffer) < desired_size
try
__get_line(self)
catch exn
if exn isa (EOFError, KeyboardInterrupt)
desired_size = length(self.buffer)
end
end
end
if desired_size < 0
return length(self.buffer)
else
return desired_size
end
end

function __get_line(self::Stdin)
#= Grab one line from get_input_line() and append it to the buffer. =#
line = get_input_line()
println(">>>$(line)")
self.buffer = (self.buffer + line) * "\n"
end

function readlines(self::Stdin)::Vector
#= Read until EOF using readline() and return a list containing the lines
        thus read. If the optional sizehint argument is present, instead of
        reading up to EOF, whole lines totalling approximately sizehint bytes
        (possibly after rounding up to an internal buffer size) are read.
         =#
result = []
total_read = 0
while sizehint == () || total_read < sizehint[1]
line = readline(self)
if line == ""
has_break = true
break;
end
total_read = total_read + length(line)
push!(result, line)
end
return result
end

if abspath(PROGRAM_FILE) == @__FILE__
test_input = "this is some test\ninput that I am hoping\n~\nwill be very instructive\nand when I am done\nI will have tested everything.\nTwelve and twenty blackbirds\nbaked in a pie. Patty cake\npatty cake so am I.\n~\nThirty-five niggling idiots!\nSell you soul to the devil, baby\n"
function fake_raw_input(prompt = nothing)
#= Replacement for raw_input() which pulls lines out of global test_input.
        For testing only!
         =#
global test_input
if "\n" ∉ test_input
end_of_line_pos = length(test_input)
else
end_of_line_pos = find(test_input, "\n")
end
result = test_input[begin:end_of_line_pos]
test_input = test_input[end_of_line_pos + 2:end]
if length(result) == 0 || result[1] == "~"
throw(EOFError())
end
return result
end

get_input_line = fake_raw_input
try
x = Stdin()
println(read(x))
println(readline(x))
println(read(x, 12))
println(readline(x, 47))
println(readline(x, 3))
println(readlines(x))
finally
get_input_line = raw_input
end
else
sys.stdin = Stdin()
end
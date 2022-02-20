using tempfile: NamedTemporaryFile
function main()
if true
temp_file = NamedTempFile::new()
file_path = name(temp_file)
if true
f = open(file_path, "w")
write(f, "hello");
end
if true
f = open(file_path, "r")
@assert(read(f, 1) == "h")
@assert(read(f) == "ello")
println("OK");
end
end
end

main()

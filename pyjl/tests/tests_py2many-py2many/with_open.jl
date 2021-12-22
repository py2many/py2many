using pylib::FileReadString
using pylib::FileWriteString
using std::fs::File
using std::fs::OpenOptions
using tempfile: NamedTemporaryFile
function main()
if true
temp_file = NamedTempFile::new()
file_path = name(temp_file)
if true
f = OpenOptions::new().write(true).open(file_path)
write(f, "hello");
end
if true
f = OpenOptions::new().read(true).open(file_path)
@assert(read(f, 1) == "h")
@assert(read(f) == "ello")
println("OK");
end
end
end

main()

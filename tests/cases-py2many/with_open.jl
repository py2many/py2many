using tempfile: NamedTemporaryFile
if abspath(PROGRAM_FILE) == @__FILE__
    NamedTempFile::new() do temp_file
        file_path = temp_file.name
        open(file_path, "w") do f
            write(f, "hello")
        end
        open(file_path, "r") do f
            @assert(read(f, 1) == "h")
            @assert(read(f) == "ello")
            println("OK")
        end
    end
end

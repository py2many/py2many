using tempfile: NamedTemporaryFile
function main()
    NamedTempFile::new() do temp_file
        file_path = name(temp_file)
        open(file_path, "w") do f
            write_(f, "hello")
        end
        open(file_path, "r") do f
            @assert(read(f, 1) == "h")
            @assert(read(f) == "ello")
            println("OK")
        end
    end
end

main()

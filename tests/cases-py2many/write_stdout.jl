
function main()
    write_ = x -> write(stdout, x)
    write(stdout, b"Test\n")
    write_(b"P4\n")
    flush(stdout)
end

main()

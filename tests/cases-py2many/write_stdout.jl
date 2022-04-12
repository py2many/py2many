
function main()
    write = x -> write(stdout, x)
    write(stdout, b"Test\n")
    write(b"P4\n")
    flush = flush(stdout)
    flush(stdout)
end

main()

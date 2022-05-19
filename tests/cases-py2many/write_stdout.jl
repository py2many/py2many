
if abspath(PROGRAM_FILE) == @__FILE__
    write = x -> Base.write(stdout, x)
    Base.write(stdout, b"Test\n")
    write(b"P4\n")
    flush = Base.flush(stdout)
    Base.flush(stdout)
end

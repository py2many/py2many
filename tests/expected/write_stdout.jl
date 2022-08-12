
if abspath(PROGRAM_FILE) == @__FILE__
    write_ = x -> write(stdout, x)
    write(stdout, stdout.buffer)
    write_(b"P4\n")
    flush_ = flush(stdout)
    flush(stdout.buffer)
end

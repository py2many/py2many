using ResumableFunctions

using itertools: starmap
reverse_translation = maketrans(
    bytes,
    b"ABCDGHKMNRSTUVWYabcdghkmnrstuvwy",
    b"TVGHCDMKNYSAABWRTVGHCDMKNYSAABWR",
)
function reverse_complement(header, sequence)::Tuple
    t = translate(sequence, reverse_translation, b"\n\r ")
    output = Vector{UInt8}()
    trailing_length = length(t) % 60
    if trailing_length
        output += b"\n" + t[begin:trailing_length]
    end
    for i in (trailing_length:60:length(t)-1)
        output += b"\n" + t[(i+1):i+60]
    end
    return (header, output[begin:end])
end

@resumable function read_sequences(file)
    for line in file
        if line[1] == ord(">")
            header = line
            sequence = Vector{UInt8}()
            for line in file
                if line[1] == ord(">")
                    @yield (header, sequence)
                    header = line
                    sequence = Vector{UInt8}()
                else
                    sequence += line
                end
            end
            @yield (header, sequence)
            break
        end
    end
end

function reverse_and_print_task(q, c, v)
    while true
        i = get(q)
        if i === nothing
            break
        end
        h, r = reverse_complement(data[i]...)
        c do
            while i != value(v)
                wait(c)
            end
        end
        write(h)
        write(r)
        flush()
        c do
            value(v) = i + 1
            notify_all(c)
        end
    end
end

@resumable function main()
    write = write(stdout.buffer)
    flush = flush(stdout.buffer)
    s = read_sequences(stdin.buffer)
    data = next(s)
    @resumable function merge(v, g)
        @yield v
        @yield from g
    end

    for (h, r) in starmap(reverse_complement, merge(data, s))
        write(h)
        write(r)
    end
end

main()

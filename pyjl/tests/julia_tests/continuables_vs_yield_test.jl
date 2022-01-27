function file_reader_channel(file_name::String)
    channel = Channel(1)
    task = @async for file_row in readlines(file_name)
        put!(channel, file_row);
    end
    bind(channel, task)
end

function file_reader_channel_alternative(file_name::String)
    Channel(1) do ch
        for file_row in readlines(file_name)
            put!(ch, file_row);
        end
    end
end

@cont function file_reader_cont(file_name::String)
    for file_row in readlines(file_name)
        cont(file_row)
    end
end
 
function main()
    # Test if all solutions produce the same results
    arr1 = []
    for res in file_reader_channel("C:/Users/Miguel Marcelino/Desktop/test.txt")
        push!(arr1, res);
    end
    @assert(arr1 == ["test", "test", "test"])

    arr2 = []
    for res in file_reader_channel_alternative("C:/Users/Miguel Marcelino/Desktop/test.txt")
        push!(arr2, res);
    end
    @assert(arr2 == ["test", "test", "test"])

    arr3 = []
    for res in collect(file_reader_cont("C:/Users/Miguel Marcelino/Desktop/test.txt"))
        push!(arr3, res);
    end
    @assert(arr3 == ["test", "test", "test"])
end

main()
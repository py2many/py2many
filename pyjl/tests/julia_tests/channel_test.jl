
function test_channel()
    taskref = Ref{Task}();
    channel = Channel(2)
    # task = @async foreach(i->put!(channel, i), 1:4);
    # bind(channel, task)
    put!(channel, 1);
    put!(channel, 2);
    # put!(channel, 2);
    return channel
end

function run_test()
    channel = test_channel()
    take!(channel)
    # for i in channel
        
    # end
end

run_test()

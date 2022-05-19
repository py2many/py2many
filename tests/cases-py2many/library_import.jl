using PyCall
datetime = pyimport("datetime")

import JSON as js
function typing_test()::Int64
    a::Vector{Int64} = [1, 2, 3]
    return a[2]
end

function calendar_test()
    return isoformat(utcnow(dt.datetime))
end

function date_to_json(objDate::dt.datetime)::js
    return Dict(
        "__type__" => "datetime",
        "year" => objDate.year,
        "month" => objDate.month,
        "day" => objDate.day,
        "hour" => objDate.hour,
        "minute" => objDate.minute,
        "second" => objDate.second,
        "microsecond" => objDate.microsecond,
        "tz" => (tzname(objDate.tzinfo, objDate), total_seconds(utcoffset(objDate))),
    )
end

function calendar_json_test()::js
    now = now(dt.datetime, dt.timezone.utc)
    return dumps(js, now, date_to_json)
end

if abspath(PROGRAM_FILE) == @__FILE__
    b = typing_test()
    @assert(b == 2)
    @assert(match(re, "\\d{4}-\\d{2}-\\d{2}T\\d{2}:\\d{2}:\\d{2}.\\d{6}", calendar_test()))
    res = calendar_json_test()
    println(res)
    println("OK")
end

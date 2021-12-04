import DateTime as dt
import JSON
function date_to_json{T0}(objDate::T0)
return Dict("__type__" => "datetime", "year" => objDate.year, "month" => objDate.month, "day" => objDate.day, "hour" => objDate.hour, "minute" => objDate.minute, "second" => objDate.second, "microsecond" => objDate.microsecond, "tz" => (tzname(objDate.tzinfo, objDate), total_seconds(objDate.utcoffset())))
end

function calendar_json_test()
now = now(dt.datetime, dt.timezone.utc)
return dumps(json, now, date_to_json)
end

function main()
res = calendar_json_test()
println(res);
end

main()

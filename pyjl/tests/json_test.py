import datetime as dt
import json

def date_to_json(objDate:dt.datetime) -> json:
    return {
        "__type__": "datetime",
        "year": objDate.year,
        "month" : objDate.month,
        "day" : objDate.day,
        "hour" : objDate.hour,
        "minute" : objDate.minute,
        "second" : objDate.second,
        "microsecond" : objDate.microsecond,
        "tz": (objDate.tzinfo.tzname(objDate), objDate.utcoffset().total_seconds())
    }  

def calendar_json_test() -> json:
    now = dt.datetime.now(dt.timezone.utc) # Another way to import
    return json.dumps(now, default=date_to_json)

if __name__ == "__main__":
    res = calendar_json_test()
    print(res)


# source: https://www.techatbloomberg.com/blog/work-dates-time-python/
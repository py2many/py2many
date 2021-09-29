import datetime as dt

def calendar_test():
    now = dt.datetime.utcnow().isoformat()
    print(now)

if __name__ == "__main__":
    calendar_test()
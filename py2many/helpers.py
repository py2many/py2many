

def parse_path(path: list[str], sep):
    """Parses a path that has been sepparated 
    (e.g using os.sep) and returns the joined 
    path using the given separator"""
    parsed_path = []
    i = 0
    while i < len(path):
        if i+1 < len(path) and path[i+1] == "..":
            i+=2
        else:
            parsed_path.append(path[i])
            i+=1
    return sep.join(parsed_path)
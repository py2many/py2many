import re

def test_re_methods():
    text = "The quick brown fox jumps over the lazy dog"
    
    # re.search
    search_res = re.search(r"fox", text)
    if search_res:
        print("Found fox")
        
    # re.match
    match_res = re.match(r"The", text)
    if match_res:
        print("Matched The")
        
    # re.findall
    findall_res = re.findall(r"\w+", text)
    print(len(findall_res))
    
    # re.sub
    sub_res = re.sub(r"fox", "cat", text)
    print(sub_res)
    
    # re.split
    split_res = re.split(r"\s+", text)
    print(len(split_res))
    
    # re.compile
    pattern = re.compile(r"\d+")
    print("Pattern compiled")

if __name__ == "__main__":
    test_re_methods()

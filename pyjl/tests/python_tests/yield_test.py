# Interesting discussion: https://stackoverflow.com/questions/9708902/in-practice-what-are-the-main-uses-for-the-yield-from-syntax-in-python-3-3
# More material:
# - http://dabeaz.com/coroutines/
# - http://dabeaz.com/coroutines/Coroutines.pdf
# - https://www.geeksforgeeks.org/coroutine-in-python/

##########################################
##########################################
##########################################

# Example from: https://www.geeksforgeeks.org/coroutine-in-python/
def print_name(prefix):
    print("Searching prefix:{}".format(prefix))
    while True:
        name = (yield)
        if prefix in name:
            print(name)
 
# calling coroutine, nothing will happen
corou = print_name("Dear")
 
# This will start execution of coroutine and
# Prints first line "Searching prefix..."
# and advance execution to the first yield expression
corou.__next__()
 
# sending inputs
corou.send("Atul")
corou.send("Dear Atul")
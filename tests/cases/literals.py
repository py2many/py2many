def string_literals():
    l1 = "literals\a" # bell
    l2 = "literals\b" # backspace
    l3 = "literals\f" # Formfeed
    l4 = "literals\n" # Linefeed
    l5 = "literals\r" # Carriage return
    l6 = "literals\v" # Vertical tab
    l7 = "literals\t" # Horizontal tab
    l8 = "\u002B"
    assert l8 == "+"
    l9 = "\U0000002B"
    assert l9 == "+"

    # multi-line String
    m = '''literal
           literal'''
    # single quote
    s = 'literal'
 
    # double quotes
    t = "literal"

def integer_literals():
    # Byte Literals
    l1 = 0b10110
    assert l1 == 22
    
    # Octal Literal
    l2 = 0o333
    assert l2 == 219

    # Decimal Literal
    l3 = 50
    assert l3 == 50 # should be trivial
    
    # Hexadecimal Literal
    l4 = 0x14c
    assert l4 == 332

def floating_point_literals():
    l1 = 25.99999
    l2 = 26.11111

def imaginary():    
    l1 = 5j

def boolean_literals():
    l1 = (1 == True)
    l2 = (1 == False)
    l3 = True + l1
    l4 = False + l2
    assert l1 == 1
    assert l2 == 0
    assert l3 == 2
    assert l4 == 0

if __name__ == "__main__":
    string_literals()
    integer_literals()
    floating_point_literals()
    imaginary()
    boolean_literals()
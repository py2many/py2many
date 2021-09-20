import ast

code ="""
def show_res():
    a: List[int] = []
    for i in range(0, 10):
        a.append(i)

    return 2*a #type=List
"""

if __name__ == "__main__":
    tree = ast.parse(code)
    print(ast.dump(tree, indent=4))
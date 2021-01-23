# please refer to __init__.py file for an explanation


def has_even(numbers):
    for num in numbers:
        if num % 2 == 0:
            return True
    return False


def main():
    vec = [1, 9, 2, 5, 4]
    even_exists = has_even(vec)
    print("Has even number", even_exists)

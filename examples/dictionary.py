if __name__ == "__main__":
    prices = {"apple": 5, "banana": 10}
    my_purchase = {"apple": 1, "banana": 6}
    grocery_bill: int = sum(
        prices[fruit] * my_purchase[fruit] for fruit in my_purchase.keys()
    )
    print("I owe the grocer ", grocery_bill)

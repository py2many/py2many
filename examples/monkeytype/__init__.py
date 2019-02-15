# This file exists as a workaround for monkeytype limitation
# To infer type annotations it needs to operate on a named module
# So this dummy can be used to invoke the "main" module
# To generate type annotations you can put your code in main.py and then invoke:
# $ monkeytype run __init__.py
# $ monkeytype apply main

import main

if __name__ == "__main__":
    main.main()

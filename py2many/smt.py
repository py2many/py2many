# Dummy interfaces
def check_sat(): ...


def get_model(): ...


def get_value(): ...


def default_value(type_):
    try:
        return type_()
    except TypeError:
        return None


# So the pre/post conditions are compiled out
pre = False
post = False

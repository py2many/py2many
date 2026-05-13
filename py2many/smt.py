# Dummy interfaces
def check_sat(): ...


def get_model(*args): ...


def get_value(*args): ...


def default_value(type_):
    try:
        return type_()
    except TypeError:
        return None


class Array:
    def __class_getitem__(cls, _):
        return cls


# So the pre/post conditions are compiled out
pre = False
post = False

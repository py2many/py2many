# Dummy interfaces
def check_sat(): ...


def get_model(): ...


def get_value(): ...


def default_value(type_):
    try:
        return type_()
    except TypeError:
        return None


class Pre:
    pass


pre = Pre()  # Singleton

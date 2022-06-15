from tempfile import NamedTemporaryFile
from textwrap import wrap

# Testing context manager
class FileOp:
    def __init__(self, file_name, method):
        self.file_name = file_name
        self.method = method

    def __enter__(self):
        self.file = open(self.file_name, self.method)
        return self.file

    def __exit__(self, type=None, value=None, traceback=None):
        self.file.close()


if __name__ == "__main__":
    with NamedTemporaryFile(mode="a+", delete=False) as temp_file:
        file_path = temp_file.name
        with FileOp(file_path, "w") as file:
            file.write("test")
        with open(file_path, "r") as f:
            assert f.read() == "test"

import sys
from typing import List


if __name__ == "__main__":
    # TODO: Use variable to help rust
    a: List[str] = sys.argv
    cmd: str = a[0]
    if cmd == "dart":
        pass
    else:
        assert "sys_argv" in cmd
    if len(a) > 1:
        print(a[1])
    else:
        print("OK")

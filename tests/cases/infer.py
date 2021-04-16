#!/usr/bin/env python3

def foo():
  a = 10
  # infer that b is an int
  b = a
  assert b == 10
  print(b)

if __name__ == "__main__":
    foo()

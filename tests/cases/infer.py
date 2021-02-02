#!/usr/bin/env python3

def foo():
  a = 10
  # infer that b is an int
  b = a

if __name__ == '__main__':
    foo()

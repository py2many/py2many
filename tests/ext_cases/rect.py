#!/usr/bin/env python3

"""This file implements a rectangle class """

from dataclasses import dataclass


@dataclass
class Rectangle:
    """Rectangle as a dataclass"""

    height: int
    length: int

    def is_square(self) -> bool:
        """Go likes this to be camel case"""
        return self.height == self.length

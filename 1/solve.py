#!/usr/bin/env python3

import re
import math
import itertools
import numpy as np
import networkx as nx


def solve(parsed):
    breakpoint()


def parse(lines):
    parsed = []

    for line in lines:
        parsed.append(line)  # do something more useful here

    return parsed


def read_file(filename):
    with open(filename, encoding="utf-8") as f_in:
        return f_in.readlines()


def main(filename, expected=None):
    result = solve(parse(read_file(filename)))
    print(result)
    if expected is not None:
        assert result == expected


if __name__ == "__main__":
    main("test_0.txt", None)
    main("input.txt")

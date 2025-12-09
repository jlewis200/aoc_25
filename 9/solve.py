#!/usr/bin/env python3

import itertools

# my data structures package
# https://github.com/jlewis200/aoc_data_structures
# https://pypi.org/project/aoc-data-structures/
from aoc_data_structures import VectorTuple


def solve(coords):
    max_area = 0

    for coord_0, coord_1 in itertools.combinations(coords, r=2):
        delta_y = max(coord_0[0], coord_1[0]) - min(coord_0[0], coord_1[0])
        delta_x = max(coord_0[1], coord_1[1]) - min(coord_0[1], coord_1[1])
        area = (1 + delta_x) * (1 + delta_y)
        max_area = max(area, max_area)

    return max_area


def parse(lines):
    parsed = []

    for line in lines:
        parsed.append(VectorTuple(map(int, line.strip().split(","))))

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
    main("test_0.txt", 50)
    main("input.txt")

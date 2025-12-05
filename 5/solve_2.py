#!/usr/bin/env python3

# my data structures package
# https://github.com/jlewis200/aoc_data_structures
# https://pypi.org/project/aoc-data-structures/
from aoc_data_structures import IntegerSet


def solve(ranges, queries):
    integer_set = IntegerSet().union(*ranges)
    return len(integer_set)


def parse(data):
    ranges = []
    queries = []

    range_data, query_data = data.split("\n\n")

    for line in range_data.strip().split("\n"):
        lower, upper = line.split("-")
        lower, upper = tuple(map(int, (lower, upper)))
        ranges.append(IntegerSet((lower, upper)))

    queries = list(map(int, query_data.strip().split("\n")))

    return ranges, queries


def read_file(filename):
    with open(filename, encoding="utf-8") as f_in:
        return f_in.read()


def main(filename, expected=None):
    result = solve(*parse(read_file(filename)))
    print(result)
    if expected is not None:
        assert result == expected


if __name__ == "__main__":
    main("test_0.txt", 14)
    main("input.txt")

#!/usr/bin/env python3

import itertools
import pandas as pd
from networkx.utils import UnionFind

# my data structures package
# https://github.com/jlewis200/aoc_data_structures
# https://pypi.org/project/aoc-data-structures/
from aoc_data_structures import VectorTuple


def solve(boxes):
    distances = get_distances(boxes)
    union_find = UnionFind(boxes)

    for pair in distances.index:
        union_find.union(*pair)

        if len(list(union_find.to_sets())) == 1:
            box_0, box_1 = pair
            return box_0[0] * box_1[0]


def get_distances(boxes):
    distances = {}

    for box_0, box_1 in itertools.combinations(boxes, 2):  # boxes):
        delta = box_0 - box_1
        distance = (delta[0] ** 2 + delta[1] ** 2 + delta[2] ** 2) ** 0.5
        distances[(box_0, box_1)] = distance

    distances = pd.Series(distances)
    distances = distances.sort_values()
    return distances


def merge(connected):
    for _ in connected:
        set_0 = connected.pop(0)

        for set_1 in connected:
            if len(set_0 & set_1) > 0:
                set_1 |= set_0
                return True

        connected.append(set_0)

    return False


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
    main("test_0.txt", 25272)
    main("input.txt")

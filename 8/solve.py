#!/usr/bin/env python3

import itertools
import numpy as np
import pandas as pd
from networkx.utils import UnionFind

# my data structures package
# https://github.com/jlewis200/aoc_data_structures
# https://pypi.org/project/aoc-data-structures/
from aoc_data_structures import VectorTuple


def solve(boxes, n):
    distances = get_distances(boxes)
    union_find = UnionFind(boxes)

    for pair in distances.index[:n]:
        union_find.union(*pair)

    return np.prod(sorted(map(len, union_find.to_sets()))[-3:])


def get_distances(boxes):
    distances = {}

    for box_0, box_1 in itertools.combinations(boxes, 2):  # boxes):
        delta = box_0 - box_1
        distance = (delta[0] ** 2 + delta[1] ** 2 + delta[2] ** 2) ** 0.5
        distances[(box_0, box_1)] = distance

    distances = pd.Series(distances)
    return distances.sort_values()


def parse(lines):
    parsed = []

    for line in lines:
        parsed.append(VectorTuple(map(int, line.strip().split(","))))

    return parsed


def read_file(filename):
    with open(filename, encoding="utf-8") as f_in:
        return f_in.readlines()


def main(filename, expected=None, n=0):
    result = solve(parse(read_file(filename)), n)
    print(result)
    if expected is not None:
        assert result == expected


if __name__ == "__main__":
    main("test_0.txt", 40, 10)
    main("input.txt", None, 1000)

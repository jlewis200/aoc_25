#!/usr/bin/env python3

import re
import math
import itertools
import numpy as np
import networkx as nx
from functools import cache

# my data structures package
# https://github.com/jlewis200/aoc_data_structures
# https://pypi.org/project/aoc-data-structures/
from aoc_data_structures import VectorTuple, Interval
from aoc_data_structures.grid_helpers import parse, grid_str


def solve(presents, trees):
    valid_trees = 0

    for idx, tree in enumerate(trees):
        if valid_tree(tree, presents):
            valid_trees += 1
        print(idx)
    return valid_trees


def valid_tree(tree, presents):
    presents = get_presents(tree, presents)
    presents = [np.array(present).astype(int) for present in presents]
    tree = np.zeros(tree[0], dtype=int)

    if validate(tree, presents):
        return True

    return False


# @cache
def validate(tree, presents):
    from time import sleep

    print(tree)
    print()
    sleep(0.1)

    if tree.max() > 1:
        return False

    if len(presents) == 0:
        # breakpoint()

        if tree.max() == 1:
            return True

        return False

    presents = presents.copy()
    present = presents.pop(0)

    for permutation in permutations(present):

        for position in positions(present, tree):
            # print(position)
            tree_ = tree.copy()
            y0, x0, y1, x1 = position
            tree_[y0:y1, x0:x1] += permutation

            if validate(tree_, presents):
                return True

    return False


def positions(present, tree):
    for y in range(tree.shape[0] - present.shape[0] + 1):
        for x in range(tree.shape[1] - present.shape[1] + 1):
            yield y, x, y + present.shape[0], x + present.shape[1]


def permutations(present):
    for _ in range(4):
        presents = np.rot90(present)

        for __ in range(2):
            present = np.fliplr(present)
            yield present


def get_presents(tree, presents):
    _, required_presents = tree
    presents_ = []

    for idx, count in enumerate(required_presents):
        jdx = count

        for _ in range(jdx):
            presents_.append(presents[idx])

    return presents_


def parse(data):
    presents = {}
    trees = []

    for section in data.split("\n\n"):
        lines = section.split("\n")

        if "x" not in section:
            index = int(re.match(r"(?P<index>\d+)\:$", lines.pop(0)).group("index"))
            shape = []

            for line in lines:
                shape.append([char == "#" for char in line])

            presents[index] = shape

        if "x" in section:
            for line in section.split("\n"):
                try:
                    shape, presents_ = line.split(":")
                    shape = tuple(map(int, shape.split("x")))
                    presents_ = tuple(map(int, presents_.strip().split()))
                    trees.append((shape, presents_))
                except:
                    print(line)

    return presents, trees


def read_file(filename):
    with open(filename, encoding="utf-8") as f_in:
        return f_in.read()


def main(filename, expected=None):
    result = solve(*parse(read_file(filename)))
    print(result)
    if expected is not None:
        assert result == expected


if __name__ == "__main__":
    main("test_0.txt", 2)
    # main("input.txt")

#!/usr/bin/env python3

import re
import math
import itertools
import numpy as np
import networkx as nx
from functools import cache
import z3
from pprint import pprint
from time import time_ns

# my data structures package
# https://github.com/jlewis200/aoc_data_structures
# https://pypi.org/project/aoc-data-structures/
from aoc_data_structures import VectorTuple, Interval
from aoc_data_structures.grid_helpers import parse, grid_str


def solve(shapes, grids):
    valid_grids = 0

    for idx, grid in enumerate(grids):
        if valid_grid(grid, shapes):
            valid_grids += 1
        print(idx)
    return valid_grids


def valid_grid(grid, shapes):
    shapes = get_shapes(grid, shapes)
    shapes = [np.array(shape).astype(int) for shape in shapes]
    grid = np.zeros(grid[0], dtype=int)

    if validate(grid, shapes):
        return True

    return False


def get_indices(shape):
    return np.argwhere(shape.flatten() == 1).flatten().tolist()


def get_shape_indices(shape, shape_index):
    shape_indices = []

    for jdx in range(shape.sum()):
        bit_size = 8
        y = z3.BitVec(f"shape_{shape_index}_{jdx}_y", bit_size)
        x = z3.BitVec(f"shape_{shape_index}_{jdx}_x", bit_size)

        shape_indices.append((y, x))

    return shape_indices


def validate(grid, shapes):
    solver = z3.Solver()

    all_shape_indices = []
    constraints = []

    for shape_index, shape in enumerate(shapes):
        shape_indices = get_shape_indices(shape, shape_index)
        all_shape_indices.extend(shape_indices)

        constraints.append(get_relative_indices(shape, shape_index, shape_indices))
        constraints.extend(get_range_constraints(shape_indices, grid))

    for (shape_0_y, shape_0_x), (shape_1_y, shape_1_x) in itertools.combinations(
        all_shape_indices, 2
    ):
        constraints.append(z3.Or(shape_0_y != shape_1_y, shape_0_x != shape_1_x))

    constraints = z3.And(constraints)
    constraints = z3.simplify(constraints)
    solver.add(constraints)

    print("solving")
    return str(solver.check()) == "sat"

    while str(solver.check()) == "sat":
        model = solver.model()
        solver.add(all_shape_indices[0] != model[all_shape_indices[0]].as_long())
        print(model)


def get_relative_indices(shape, shape_index, shape_indices):
    candidates = []
    shape_indices = shape_indices.copy()

    for permutation in permutations(shape):
        candidates.append(_get_relative_indices(permutation, shape_index))

    base_y, base_x = shape_indices[0]
    constraints = []

    for candidates_ in candidates:
        candidate_constraints = []

        for (shape_y, shape_x), (delta_y, delta_x) in zip(shape_indices, candidates_):
            candidate_constraints.append(shape_y == base_y + delta_y)
            candidate_constraints.append(shape_x == base_x + delta_x)

        constraints.append(z3.And(candidate_constraints))

    asdf = z3.Or(constraints)
    return asdf


def remove_common(candidates, common):
    new_candidates = []

    for candidate in candidates:
        new_candidates.append(candidate - common)

    return new_candidates


def _get_relative_indices(shape, shape_index):
    rebased_coords = np.argwhere(shape == 1)
    rebased_coords -= rebased_coords[0]
    # return set(tuple(map(int, item)) for item in rebased_coords)
    return list(tuple(map(int, item)) for item in rebased_coords)


def get_range_constraints(relative_indices, grid):
    range_constraints = []

    for shape_y, shape_x in relative_indices:
        range_constraints.append(z3.And(shape_y >= 0, shape_y < grid.shape[0]))
        range_constraints.append(z3.And(shape_x >= 0, shape_x < grid.shape[1]))

    # return z3.And(range_constraints)
    return range_constraints


def permutations(shape):
    shape_dict = {}

    for _ in range(4):
        shape = np.rot90(shape)

        for __ in range(2):
            shape = np.fliplr(shape)
            shape_dict[str(shape)] = shape

    yield from shape_dict.values()


def get_shapes(grid, shapes):
    _, required_shapes = grid
    shapes_ = []

    for idx, count in enumerate(required_shapes):
        jdx = count

        for _ in range(jdx):
            shapes_.append(shapes[idx])

    return shapes_


def parse(data):
    shapes = {}
    grids = []

    for section in data.split("\n\n"):
        lines = section.split("\n")

        if "x" not in section:
            index = int(re.match(r"(?P<index>\d+)\:$", lines.pop(0)).group("index"))
            shape = []

            for line in lines:
                shape.append([char == "#" for char in line])

            shapes[index] = shape

        if "x" in section:
            for line in section.split("\n"):
                try:
                    shape, shapes_ = line.split(":")
                    shape = tuple(map(int, shape.split("x")))
                    shapes_ = tuple(map(int, shapes_.strip().split()))
                    grids.append((shape, shapes_))
                except:
                    print(line)

    return shapes, grids


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

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
from dlx.algorithm_m import AlgorithmM
from dlx.test_algorithm_m import generate_graph

bit_size = 8


def solve(shapes, grids):
    valid_grids = 0

    for idx, (grid_shape, shape_counts) in enumerate(grids):
        if valid_grid(grid_shape, shape_counts, shapes):
            valid_grids += 1
        print(idx)
    return valid_grids


def valid_grid(grid_shape, shape_counts, shapes):
    n_required = (shapes*np.array(shape_counts).reshape(6,1,1)).sum()
    
    if n_required > np.prod(grid_shape):
        return False

    if validate(grid_shape, shape_counts, shapes):
        return True

    return False


def get_indices(shape):
    indices = np.argwhere(shape.flatten() == 1).flatten().tolist()
    return list(map(str, indices))

def get_grid_coords(grid_shape):
    grid_coords = list(range(np.prod(grid_shape)))
    return list(map(str, grid_coords))

def enumerate_shape_positions(shape_name, shape, grid_shape):
    shape = shape.copy()
    options = []

    for permutation in permutations(shape):
        for y, x in itertools.product(range(grid_shape[0]), range(grid_shape[1])):
            grid = np.zeros(grid_shape, dtype=int)
            
            try:
                grid[y:y+permutation.shape[0], x:x+permutation.shape[1]] += permutation
                options.append([shape_name] + get_indices(grid))
            except ValueError:
                pass

    return options

    
def validate(grid_shape, shape_counts, shapes):
    shape_names = [f"shape_{idx}" for idx, _ in enumerate(shape_counts)]
    shape_multiplicities = [(shape_count, shape_count) for shape_count in shape_counts]
    grid_coords = get_grid_coords(grid_shape)
    options = []
    
    for shape_name, shape, shape_count in zip(shape_names, shapes, shape_counts):
        if shape_count > 0:
            options.extend(enumerate_shape_positions(shape_name, shape, grid_shape))
    
    root = generate_graph(
        primary_items=shape_names,
        primary_multiplicities=shape_multiplicities,
        secondary_items=grid_coords,
        options=options,
    )

    try:
        next(AlgorithmM(root).solutions())
        return True
    except StopIteration:
        pass

    return False

def permutations(shape):
    shape_dict = {}

    for _ in range(4):
        shape = np.rot90(shape)

        for __ in range(2):
            shape = np.fliplr(shape)
            shape_dict[str(shape)] = shape

    yield from shape_dict.values()


def parse(data):
    shapes = []
    grids = []

    for section in data.split("\n\n"):
        lines = section.split("\n")

        if "x" not in section:
            lines.pop(0)
            shape = []

            for line in lines:
                shape.append([char == "#" for char in line])

            shapes.append(np.array(shape))

        if "x" in section:
            for line in section.split("\n"):
                try:
                    shape, shapes_ = line.split(":")
                    shape = tuple(map(int, shape.split("x")))
                    shapes_ = tuple(map(int, shapes_.strip().split()))
                    grids.append((shape, shapes_))
                except:
                    print(line)

    return np.array(shapes), grids


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
    main("input.txt")

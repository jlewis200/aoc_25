#!/usr/bin/env python3

from collections import deque
import numpy as np

# my data structures package
# https://github.com/jlewis200/aoc_data_structures
# https://pypi.org/project/aoc-data-structures/
from aoc_data_structures import VectorTuple
from aoc_data_structures.grid_helpers import parse


def solve(grid):
    y, x = np.argwhere(grid == "S")[0]
    queue = deque([VectorTuple(y, x)])
    grid_cache = np.full_like(grid, 0, dtype=int)
    grid_cache[VectorTuple(y, x)] = 1
    visited = set()

    while len(queue) > 0:
        coord = queue.popleft()

        if coord[0] >= grid_cache.shape[0]:
            continue

        path_count = grid_cache[coord]

        if grid[coord] == "^" and coord not in visited:
            queue.append(coord + VectorTuple(1, -1))
            queue.append(coord + VectorTuple(1, 1))

            grid_cache[coord + VectorTuple(1, 1)] += path_count
            grid_cache[coord + VectorTuple(1, -1)] += path_count

        elif coord[0] < grid_cache.shape[0] - 1 and coord not in visited:
            queue.append(coord + VectorTuple(1, 0))
            grid_cache[coord + VectorTuple(1, 0)] += path_count

        visited.add(coord)

    return grid_cache[-1].sum()


def read_file(filename):
    with open(filename, encoding="utf-8") as f_in:
        return f_in.readlines()


def main(filename, expected=None):
    result = solve(parse(read_file(filename)))
    print(result)
    if expected is not None:
        assert result == expected


if __name__ == "__main__":
    main("test_0.txt", 40)
    main("input.txt")

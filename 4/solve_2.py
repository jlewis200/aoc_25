#!/usr/bin/env python3

# my data structures package
# https://github.com/jlewis200/aoc_data_structures
# https://pypi.org/project/aoc-data-structures/
from aoc_data_structures import VectorTuple
from aoc_data_structures.grid_helpers import parse, grid_str


def solve(grid):
    print(grid_str(grid))

    accessible = []
    n_accessible = -1

    while len(accessible) > n_accessible:
        n_accessible = len(accessible)
        newly_accessible = get_accessible(grid)
        remove(grid, newly_accessible)
        accessible.extend(newly_accessible)
        print(grid_str(grid))

    return len(accessible)


def remove(grid, accessible):
    for coord in accessible:
        grid[coord] = "."


def get_accessible(grid):
    accessible = []

    for y in range(grid.shape[0]):
        for x in range(grid.shape[1]):
            coord = VectorTuple(y, x)
            if grid[coord] == "@" and is_accessible(coord, grid):
                accessible.append(coord)

    return accessible


def is_accessible(coord, grid):
    n_adjacent_rolls = 0

    for adjacency in coord.adjacencies(grid):
        if grid[adjacency] == "@":
            n_adjacent_rolls += 1

    return n_adjacent_rolls < 4


def read_file(filename):
    with open(filename, encoding="utf-8") as f_in:
        return f_in.readlines()


def main(filename, expected=None):
    result = solve(parse(read_file(filename)))
    print(result)
    if expected is not None:
        assert result == expected


if __name__ == "__main__":
    main("test_0.txt", 43)
    main("input.txt")

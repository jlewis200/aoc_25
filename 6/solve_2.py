#!/usr/bin/env python3

import numpy as np

# my data structures package
# https://github.com/jlewis200/aoc_data_structures
# https://pypi.org/project/aoc-data-structures/
from aoc_data_structures.grid_helpers import grid_str


def solve(grid):
    operations = get_operations(grid)
    operand_groups = get_operand_groups(grid)
    results = []

    for operation, operands in zip(operations, operand_groups):
        results.append(perform_operation(operation, operands))

    return sum(results)


def perform_operation(operation, operands):
    if operation == "*":
        return np.prod(operands)

    return sum(operands)


def get_operations(grid):
    operations = grid.T[:, -1]
    return "".join(operations).split()


def get_operand_groups(grid):
    operands = grid.T[:, :-1]
    operands = grid_str(operands)
    operand_groups = [[]]

    for operand in operands.split("\n"):

        try:
            operand_groups[-1].append(int(operand))
        except ValueError:
            operand_groups.append([])

    return operand_groups


def parse(lines):
    parsed = []

    for line in lines:
        parsed.append(list(line.replace("\n", "")))

    return np.array(parsed)


def read_file(filename):
    with open(filename, encoding="utf-8") as f_in:
        return f_in.readlines()


def main(filename, expected=None):
    result = solve(parse(read_file(filename)))
    print(result)
    if expected is not None:
        assert result == expected


if __name__ == "__main__":
    main("test_0.txt", 3263827)
    main("input.txt")

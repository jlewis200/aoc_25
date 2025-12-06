#!/usr/bin/env python3

import numpy as np


def solve(parsed):
    operations = parsed[-1]
    operand_groups = get_operand_groups(parsed[:-1])
    results = []

    for operation, operands in zip(operations, operand_groups):
        results.append(perform_operation(operation, operands))

    return sum(results)


def perform_operation(operation, operands):
    if operation == "*":
        return np.prod(operands)

    return sum(operands)


def get_operand_groups(operands):
    return np.array(operands).astype(int).T


def parse(lines):
    parsed = []

    for line in lines:
        parsed.append(line.split())

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
    main("test_0.txt", 4277556)
    main("input.txt")

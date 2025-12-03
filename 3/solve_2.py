#!/usr/bin/env python3

import numpy as np


def solve(parsed):
    joltages = []

    for battery in parsed:
        joltage = get_max_joltage(battery)
        joltages.append(joltage)

    return sum(joltages)


def get_max_joltage(battery):
    digits = []
    base = 0

    for idx in range(len(battery) - 11, len(battery) + 1, 1):
        battery_slice = battery[base:idx]
        arg_max = np.argmax(battery_slice)
        digits.append(battery[base + arg_max])
        base += arg_max + 1

    return int("".join(map(str, digits)))


def parse(lines):
    parsed = []

    for line in lines:
        parsed.append(list(map(int, line.strip())))

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
    main("test_0.txt", 3121910778619)
    main("input.txt")

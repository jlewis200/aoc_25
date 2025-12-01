#!/usr/bin/env python3


def solve(parsed):
    position = 50
    zeros = 0

    for turn in parsed:
        increment = turn // abs(turn)

        while abs(turn) > 0:
            turn -= increment
            position += increment
            position %= 100

            if position == 0:
                zeros += 1

    return zeros


def parse(lines):
    parsed = []

    for line in lines:
        line = line.replace("L", "-")
        line = line.replace("R", "")
        line = line.strip()
        parsed.append(int(line))

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
    main("test_0.txt", 6)
    main("input.txt")

#!/usr/bin/env python3


def solve(ranges):
    invalid = []

    for rng in ranges:
        invalid.extend(get_invalid(rng))

    return sum(invalid)


def get_invalid(rng):
    invalid = []

    for value in rng:
        if is_invalid(str(value)):
            invalid.append(value)

    return invalid


def is_invalid(value):
    for idx in range(1, 1 + (len(value) // 2)):
        if len(value) % idx != 0:
            continue

        expected = len(value) // idx

        if value.count(value[:idx]) == expected:
            return True

    return False


def parse(data):
    data = data.strip()
    intervals = data.split(",")
    ranges = []

    for interval in intervals:
        start, stop = interval.split("-")
        start = int(start)
        stop = int(stop) + 1
        ranges.append(range(start, stop))

    return ranges


def read_file(filename):
    with open(filename, encoding="utf-8") as f_in:
        return f_in.read()


def main(filename, expected=None):
    result = solve(parse(read_file(filename)))
    print(result)
    if expected is not None:
        assert result == expected


if __name__ == "__main__":
    main("test_0.txt", 4174379265)
    main("input.txt")

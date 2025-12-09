#!/usr/bin/env python3

import itertools

# my data structures package
# https://github.com/jlewis200/aoc_data_structures
# https://pypi.org/project/aoc-data-structures/
from aoc_data_structures import VectorTuple, Interval

RIGHT = VectorTuple(1, 0)
LEFT = VectorTuple(-1, 0)
UP = VectorTuple(0, -1)
DOWN = VectorTuple(0, 1)


class Segment:
    """
    A vertical or horizontal line segment represented by two endpoints.
    """

    def __init__(self, coord_0, coord_1):
        self.x = Interval(coord_0[0], coord_1[0])
        self.y = Interval(coord_0[1], coord_1[1])

    def intersects(self, other):
        """
        Return true if there is an intersection.  This returns true for
        parallel and perpendicular overlaps.
        """
        try:
            # Interval.intersection() raises value error if no overlap.
            self.x & other.x
            self.y & other.y
            return True
        except ValueError:
            return False

    def __repr__(self):
        return f"x:  {self.x}  y:  {self.y}"


def solve(coords):
    """
    Steps:
    - construct exclusive perimiter 1 size larger than supplied inclusive perimeter
    - iterate through rectangle possibilities
    - check rectangle validity by detecting rectangle intersection with perimeter
    """
    perimeter = get_perimeter(coords)
    perimeter = get_segments(perimeter)
    max_area = 0

    for coord_0, coord_1 in itertools.combinations(coords, r=2):
        x_0, y_0, x_1, y_1 = get_bounds(coord_0, coord_1)
        delta_y = y_1 - y_0
        delta_x = x_1 - x_0
        area = (1 + delta_x) * (1 + delta_y)

        if area < max_area:
            continue

        rectangle = [(x_0, y_0), (x_1, y_0), (x_1, y_1), (x_0, y_1)]
        rectangle = get_segments(rectangle)

        if valid(perimeter, rectangle):
            max_area = area

    return max_area


def get_segments(coords):
    """
    Get line segments for given coords.
    """
    coords = coords.copy()
    src = coords.pop(0)
    coords.append(src)
    segments = []

    for dst in coords:
        segments.append(Segment(src, dst))
        src = dst

    return segments


def get_bounds(coord_0, coord_1):
    y_0 = min(coord_0[1], coord_1[1])
    y_1 = max(coord_0[1], coord_1[1])
    x_0 = min(coord_0[0], coord_1[0])
    x_1 = max(coord_0[0], coord_1[0])
    return x_0, y_0, x_1, y_1


def valid(perimeter, rectangle):
    for p_segment in perimeter:
        for r_segment in rectangle:
            if r_segment.intersects(p_segment):
                return False
    return True


def get_perimeter(coords):
    """
    Get corners of external perimeter.  This assumes clockwise order.
    This approach would fail if two edges were adjacent, but all edges of the
    input data have a gap of at least 1.
    """
    modified_coords = []
    first, last = coords[0], coords[-1]
    coords = coords.copy()
    coords.insert(0, last)
    coords.append(first)

    for idx in range(len(coords) - 2):
        c0, c1, c2 = coords[idx : idx + 3]
        delta_0 = get_delta(c0, c1)
        delta_1 = get_delta(c1, c2)
        delta_set = {delta_0, delta_1}

        if delta_set == {RIGHT, UP}:
            modified_coords.append(c1 + UP + LEFT)

        if delta_set == {RIGHT, DOWN}:
            modified_coords.append(c1 + UP + RIGHT)

        if delta_set == {LEFT, UP}:
            modified_coords.append(c1 + DOWN + LEFT)

        if delta_set == {LEFT, DOWN}:
            modified_coords.append(c1 + DOWN + RIGHT)

    return modified_coords


def get_delta(src, dst):
    delta_y = dst[0] - src[0]
    if delta_y > 0:
        delta_y = 1
    if delta_y < 0:
        delta_y = -1

    delta_x = dst[1] - src[1]
    if delta_x > 0:
        delta_x = 1
    if delta_x < 0:
        delta_x = -1

    return VectorTuple(delta_y, delta_x)


def parse(lines):
    parsed = []

    for line in lines:
        args = list(map(int, line.strip().split(",")))
        parsed.append(VectorTuple(args))

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
    main("test_0.txt", 24)
    main("input.txt")

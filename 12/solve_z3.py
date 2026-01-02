#!/usr/bin/env python3

import re
import itertools
import numpy as np
import z3

BIT_SIZE = 8


def solve(shapes, grids):
    valid_grids = 0

    for idx, (grid_shape, shape_counts) in enumerate(grids):
        if pre_accept(grid_shape, shape_counts, shapes):
            valid_grids += 1
            continue

        if pre_reject(grid_shape, shape_counts, shapes):
            continue

        print(idx)
        if valid_grid(grid_shape, shape_counts, shapes):
            valid_grids += 1

    return valid_grids


def pre_accept(grid_shape, shape_counts, shapes):
    """
    Accept the trivial case where each shape is assumed to be:

    ###
    ###
    ###

    and there are enough 3x3 squares to fit the total number of shapes.
    """
    min_shapes_supported = (grid_shape[0] // 3) * (grid_shape[1] // 3)
    return min_shapes_supported >= sum(shape_counts)


def pre_reject(grid_shape, shape_counts, shapes):
    """
    Reject the trivial case where the total area of the shapes is greater than
    the total area of the grid.
    """
    min_cells_required = (shapes * np.array(shape_counts).reshape(6, 1, 1)).sum()
    return min_cells_required > np.prod(grid_shape)


def valid_grid(grid_shape, shape_counts, shapes):
    shapes = get_shapes(shape_counts, shapes)
    shapes = [np.array(shape).astype(int) for shape in shapes]
    grid = np.zeros(grid_shape, dtype=int)
    if validate(grid, shapes):
        return True

    return False


def get_indices(shape):
    return np.argwhere(shape.flatten() == 1).flatten().tolist()


def get_shape_indices(shape, shape_index):
    shape_indices = []

    for jdx in range(shape.sum()):
        y = z3.BitVec(f"shape_{shape_index}_{jdx}_y", BIT_SIZE)
        x = z3.BitVec(f"shape_{shape_index}_{jdx}_x", BIT_SIZE)

        shape_indices.append((y, x))

    return shape_indices


def validate(grid, shapes):
    solver = z3.Solver()

    all_shape_indices = []
    constraints = []

    for shape_index, shape in enumerate(shapes):
        shape_indices = get_shape_indices(shape, shape_index)
        all_shape_indices.extend(shape_indices)

        constraints.append(get_relative_indices(shape, shape_indices))
        constraints.extend(get_range_constraints(shape_indices, grid))

    for (shape_0_y, shape_0_x), (shape_1_y, shape_1_x) in itertools.combinations(
        all_shape_indices,
        2,
    ):
        constraints.append(z3.Or(shape_0_y != shape_1_y, shape_0_x != shape_1_x))

    constraints = z3.And(constraints)
    constraints = z3.simplify(constraints)
    solver.add(constraints)

    return str(solver.check()) == "sat"


def get_relative_indices(shape, shape_indices):
    candidates = []
    shape_indices = shape_indices.copy()

    for permutation in permutations(shape):
        candidates.append(_get_relative_indices(permutation))

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


def _get_relative_indices(shape):
    rebased_coords = np.argwhere(shape == 1)
    rebased_coords -= rebased_coords[0]
    return list(tuple(map(int, item)) for item in rebased_coords)


def get_range_constraints(relative_indices, grid):
    range_constraints = []

    for shape_y, shape_x in relative_indices:
        range_constraints.append(z3.And(shape_y >= 0, shape_y < grid.shape[0]))
        range_constraints.append(z3.And(shape_x >= 0, shape_x < grid.shape[1]))

    return range_constraints


def permutations(shape):
    shape_dict = {}

    for _ in range(4):
        shape = np.rot90(shape)

        for __ in range(2):
            shape = np.fliplr(shape)
            shape_dict[str(shape)] = shape

    yield from shape_dict.values()


def get_shapes(required_shapes, shapes):
    shapes_ = []

    for idx, count in enumerate(required_shapes):
        jdx = count

        for _ in range(jdx):
            shapes_.append(shapes[idx])

    return shapes_


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
            for line in section.strip().split("\n"):
                shape, shapes_ = line.split(":")
                shape = tuple(map(int, shape.split("x")))
                shapes_ = tuple(map(int, shapes_.strip().split()))
                grids.append((shape, shapes_))

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

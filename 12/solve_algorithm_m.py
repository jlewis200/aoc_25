#!/usr/bin/env python3

import itertools
import numpy as np
from dlx.algorithm_m import AlgorithmM
from dlx.test_algorithm_m import generate_graph


def solve(shapes, grids):
    valid_grids = 0

    for grid_shape, shape_counts in grids:
        if pre_accept(grid_shape, shape_counts):
            valid_grids += 1
            continue

        if pre_reject(grid_shape, shape_counts, shapes):
            continue

        valid_grids += validate(grid_shape, shape_counts, shapes)

    return valid_grids


def pre_accept(grid_shape, shape_counts):
    """
    All shapes are at most 3x3.  Accept the trivial case where each shape is
    assumed to be:

    ###
    ###
    ###

    and there are enough 3x3 squares to fit the total number of shapes.  This
    signifies that the shapes don't need to be interleaved.
    """
    min_shapes_supported = (grid_shape[0] // 3) * (grid_shape[1] // 3)
    return min_shapes_supported >= sum(shape_counts)


def pre_reject(grid_shape, shape_counts, shapes):
    """
    Reject the trivial case where the total area of the shapes is greater than
    the total area of the grid.
    """
    min_cells_required = (shapes * np.array(shape_counts).reshape((6, 1, 1))).sum()
    return min_cells_required > np.prod(grid_shape)


def get_indices(shape):
    """
    Get the flattened indices of a shape/permutation.
    """
    indices = np.argwhere(shape.flatten() == 1).flatten().tolist()
    return list(map(str, indices))


def get_grid_coords(grid_shape):
    """
    Generate all coordinate pairs of a grid.
    """
    grid_coords = list(range(np.prod(grid_shape)))
    return list(map(str, grid_coords))


def enumerate_shape_positions(shape_name, shape, grid_shape):
    """
    Generate every combination of coordinates that could satisfy a shape:
    - every rotation
    - every reflection
    - every position on the grid
    """
    shape = shape.copy()
    options = []

    for permutation in permutations(shape):
        for y, x in itertools.product(range(grid_shape[0]), range(grid_shape[1])):
            grid = np.zeros(grid_shape, dtype=int)

            try:
                grid[
                    y : y + permutation.shape[0], x : x + permutation.shape[1]
                ] += permutation
                options.append([shape_name] + get_indices(grid))
            except ValueError:
                pass

    return options


def validate(grid_shape, shape_counts, shapes):
    """
    Formulate the packing problem as a multiple cover with color (MCC) problem.

    primary items:  the 6 shapes
    primary multiplicities:  the specified shape counts
    secondary items:  the grid coordinates
    secondary colors:  implicit unique to force occupation by only one shape (no overlap allowed)
    options:  the coordinates occupied by the permuataions/locations of the shapes
    """
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
    """
    Generate and de-duplicate the rotations/reflections of a shape.
    """
    shape_dict = {}

    for _ in range(4):
        shape = np.rot90(shape)

        for __ in range(2):
            shape = np.fliplr(shape)
            shape_dict[str(shape)] = shape

    yield from shape_dict.values()


def parse(data):
    shapes = []

    for section in data.split("\n\n"):
        lines = section.strip().split("\n")

        if "x" not in section:
            shapes.append(parse_shape(lines))

        if "x" in section:
            grids = parse_grids(lines)

    return np.array(shapes), grids


def parse_shape(lines):
    """
    Parse a shape section of input.
    """
    lines.pop(0)
    shape = []

    for line in lines:
        shape.append([char == "#" for char in line])

    return np.array(shape)


def parse_grids(lines):
    """
    Parse a grid section of input.
    """
    grids = []

    for line in lines:
        grid_size, shape_counts = line.split(":")
        grid_size = tuple(map(int, grid_size.split("x")))
        shape_counts = tuple(map(int, shape_counts.strip().split()))
        grids.append((grid_size, shape_counts))

    return grids


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

#!/usr/bin/env python3

import itertools
import numpy as np
import z3

BIT_SIZE = 8


def solve(shapes, grids):
    valid_grids = 0

    for grid_shape, shape_counts in grids:
        if pre_accept(grid_shape, shape_counts):
            valid_grids += 1
            continue

        if pre_reject(grid_shape, shape_counts, shapes):
            continue

        valid_grids += valid_grid(grid_shape, shape_counts, shapes)

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


def valid_grid(grid_shape, shape_counts, shapes):
    """
    Preprocess the parameters and return true if the grid is valid.
    """
    shapes = get_shapes(shape_counts, shapes)
    shapes = [np.array(shape).astype(int) for shape in shapes]
    grid = np.zeros(grid_shape, dtype=int)
    return validate(grid, shapes)


def get_shape_indices(shape, shape_index):
    """
    Get the symbolic indices of a shape.
    """
    shape_indices = []

    for jdx in range(shape.sum()):
        y = z3.BitVec(f"shape_{shape_index}_{jdx}_y", BIT_SIZE)
        x = z3.BitVec(f"shape_{shape_index}_{jdx}_x", BIT_SIZE)
        shape_indices.append((y, x))

    return shape_indices


def validate(grid, shapes):
    """
    Formulate a z3 constraint problem to see if the required number of shapes
    can/can't be packed in the specified area.

    Each shape must have:
    - unique coords
    - coords arranged in one of their specified permuataions
    - coords within the y/x bound specified by the grid

    z3.sat indicates they can be packed without overlapping
    """
    solver = z3.Solver()
    all_shape_indices = []
    constraints = []

    for shape_index, shape in enumerate(shapes):
        shape_indices = get_shape_indices(shape, shape_index)
        constraints.append(get_relative_constraints(shape, shape_indices))
        constraints.extend(get_range_constraints(shape_indices, grid))
        all_shape_indices.extend(shape_indices)

    constraints.extend(get_unique_coord_constraints(all_shape_indices))
    constraints = z3.And(constraints)
    constraints = z3.simplify(constraints)
    solver.add(constraints)
    return solver.check() == z3.sat


def get_unique_coord_constraints(all_shape_indices):
    """
    Get constraints to restrict two pairs of coords from sharing both the same
    x and y values.
    """
    constraints = []

    for (shape_0_y, shape_0_x), (shape_1_y, shape_1_x) in itertools.combinations(
        all_shape_indices,
        2,
    ):
        constraints.append(z3.Or(shape_0_y != shape_1_y, shape_0_x != shape_1_x))

    return constraints


def get_relative_constraints(shape, shape_indices):
    """
    Generate the constraints that relate the coordinates of a shape to each
    other.

    Ex:
    shape of: ##
    in a 2x2 grid with indices:
    0,0  0,1
    1,0  1,1

    the shape indices can be:
    (0,0 and 0,1) or (1,0 and 1,1) or (0,0 and 1,0) or (0,1 and 1,1)

    there are two unique permutations:
    - horizontal
    - vertical

    the shape has two coordinates, the location of the second coord can be
    specified relative to the first.
    (
        (coord_0 == base_coord and coord_1 == base_coord + 0,1) or  # horizontal
        (coord_0 == base_coord and coord_1 == base_coord + 1,0)     # vertical
    )
    """
    shape_indices = shape_indices.copy()
    base_y, base_x = shape_indices[0]
    constraints = []

    for permutation in permutations(shape):
        relative_coords = get_relative_coords(permutation)
        candidate_constraints = []

        for (shape_y, shape_x), (delta_y, delta_x) in zip(
            shape_indices, relative_coords
        ):
            candidate_constraints.append(shape_y == base_y + delta_y)
            candidate_constraints.append(shape_x == base_x + delta_x)

        constraints.append(z3.And(candidate_constraints))

    return z3.Or(constraints)


def get_relative_coords(shape):
    """
    Helper to generate relative indices for a single shape/permutation.
    """
    rebased_coords = np.argwhere(shape == 1)
    rebased_coords -= rebased_coords[0]
    return list(tuple(map(int, item)) for item in rebased_coords)


def get_range_constraints(relative_indices, grid):
    """
    Generate constraints to restrict every element of a shape to have valid y/x
    coordinates.
    """
    range_constraints = []

    for shape_y, shape_x in relative_indices:
        range_constraints.append(z3.And(shape_y >= 0, shape_y < grid.shape[0]))
        range_constraints.append(z3.And(shape_x >= 0, shape_x < grid.shape[1]))

    return range_constraints


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


def get_shapes(required_shapes, shapes):
    """
    Generate a list of the shapes with specified multiplicities.
    """
    duplicated_shapes = []

    for idx, count in enumerate(required_shapes):
        for _ in range(count):
            duplicated_shapes.append(shapes[idx])

    return duplicated_shapes


def parse(data):
    shapes = []

    for section in data.split("\n\n"):
        lines = section.strip().split("\n")

        if "x" in section:
            grids = parse_grids(lines)

        else:
            shapes.append(parse_shape(lines))

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

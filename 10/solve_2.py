#!/usr/bin/env python3

import re
import json
import z3


def get_min_presses(joltages, buttons):
    solver = z3.Solver()
    n_presses = [z3.Int(f"p_{idx}") for idx in range(len(buttons))]

    for sym_var in n_presses:
        solver.add(sym_var >= 0)

    for idx, joltage in enumerate(joltages):
        applicable_buttons = get_applicable_buttons(buttons, idx)
        solver.add(sum([n_presses[button] for button in applicable_buttons]) == joltage)

    light_sum = sum(n_presses)

    while str(solver.check()) == "sat":
        model = solver.model()
        min_presses = get_n_presses(model, n_presses)
        solver.add(light_sum < min_presses)

    return min_presses


def get_n_presses(model, n_presses):
    return sum([model[n_press].as_long() for n_press in n_presses])


def get_applicable_buttons(buttons, light_index):
    applicable_buttons = []

    for jdx, button in enumerate(buttons):
        if light_index in button:
            applicable_buttons.append(jdx)

    return applicable_buttons


def solve(parsed):
    n_presses = 0

    for _, buttons, joltages in parsed:
        n_presses += get_min_presses(joltages, buttons)

    return n_presses


def parse(lines):
    parsed = []

    for line in lines:
        indicator_lights, *buttons, joltages = line.split()
        indicator_lights = indicator_lights[1:-1]
        _buttons = []

        for button in buttons:
            button = button.replace("(", "[")
            button = button.replace(")", "]")
            button = json.loads(button)
            _buttons.append(tuple(button))

        indicator_lights = [light == "#" for light in indicator_lights]
        joltages = list(map(int, re.findall(r"\d+", joltages)))

        parsed.append((indicator_lights, _buttons, joltages))

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
    main("test_0.txt", 33)
    main("input.txt")

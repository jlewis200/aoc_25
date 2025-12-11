#!/usr/bin/env python3

import networkx as nx


def solve(parsed):
    graph = nx.DiGraph(parsed)
    return len(list(nx.all_simple_paths(graph, "you", "out")))


def parse(lines):
    parsed = []

    for line in lines:
        src, dsts = line.split(":")

        for dst in dsts.split():
            parsed.append((src, dst.strip()))

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
    main("test_0.txt", 5)
    main("input.txt")

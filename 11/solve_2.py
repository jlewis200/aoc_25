#!/usr/bin/env python3

from collections import defaultdict
import networkx as nx


def solve(parsed):
    """
    Multiply number of paths from src->dac, dac->fft, fft->out.
    """
    graph = nx.DiGraph(parsed)
    dst_0, dst_1 = get_ordered(graph, "dac", "fft")
    path = [("svr", dst_0), (dst_0, dst_1), (dst_1, "out")]
    prod = 1

    for src, dst in path:
        prod *= get_n_paths(graph, src, dst)

    return prod


def get_ordered(graph, node_0, node_1):
    topo_sort = list(nx.topological_sort(graph))
    idx_0, idx_1 = topo_sort.index(node_0), topo_sort.index(node_1)
    return topo_sort[min(idx_0, idx_1)], topo_sort[max(idx_0, idx_1)]


def get_n_paths(graph, src, dst):
    """
    Get number of paths from src to dst.
    """
    topo_sort = list(nx.topological_sort(graph))
    cache = defaultdict(lambda: 0)
    cache[src] = 1

    while topo_sort[0] != src:
        topo_sort.pop(0)

    for src in topo_sort:
        for adjacency in graph[src]:
            cache[adjacency] += cache[src]

    return cache[dst]


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
    main("test_1.txt", 2)
    main("input.txt")

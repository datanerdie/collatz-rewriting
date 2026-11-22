"""A small string rewriting engine: successors, full exploration, cycle detection."""


class TooLarge(Exception):
    pass


def successors(string, rules):
    """Every (rule, position, result) obtainable from `string` in one step."""
    out = []
    for rule in rules:
        left, right = rule
        i = string.find(left)
        while i != -1:
            out.append((rule, i, string[:i] + right + string[i + len(left):]))
            i = string.find(left, i + 1)
    return out


def explore(start, rules, limit=200000):
    """The whole rewrite graph reachable from `start`: {string: [(rule, next string), ...]}.

    Every rule is tried at every position of every reachable string, so the graph contains
    all rewrite sequences that start from `start`, not just one strategy's.
    """
    graph = {}
    stack = [start]
    while stack:
        s = stack.pop()
        if s in graph:
            continue
        edges = [(rule, t) for rule, _, t in successors(s, rules)]
        graph[s] = edges
        if len(graph) > limit:
            raise TooLarge(start)
        stack.extend(t for _, t in edges if t not in graph)
    return graph


def find_cycle(graph):
    """A list of strings forming a cycle in the graph, or None if the graph is acyclic."""
    WHITE, GREY, BLACK = 0, 1, 2
    colour = dict.fromkeys(graph, WHITE)
    for root in graph:
        if colour[root] != WHITE:
            continue
        path = [root]
        iters = [iter(graph[root])]
        colour[root] = GREY
        while iters:
            for _, t in iters[-1]:
                if colour[t] == GREY:
                    return path[path.index(t):] + [t]
                if colour[t] == WHITE:
                    colour[t] = GREY
                    path.append(t)
                    iters.append(iter(graph[t]))
                    break
            else:
                colour[path.pop()] = BLACK
                iters.pop()
    return None


def longest_path(graph):
    """Length of the longest rewrite sequence in an acyclic graph."""
    depth = {}
    for root in graph:
        if root in depth:
            continue
        stack = [(root, False)]
        while stack:
            s, done = stack.pop()
            if done:
                depth[s] = 1 + max((depth[t] for _, t in graph[s]), default=-1)
            elif s not in depth:
                stack.append((s, True))
                stack.extend((t, False) for _, t in graph[s] if t not in depth)
    return max(depth.values())

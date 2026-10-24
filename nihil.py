#!/usr/bin/env python3
"""
⟁ NIHIL  v0.2
════════════════════════════════════════════════════════════════════════
You do not write an algorithm. You FORBID worlds. What survives is the answer.

A real constraint engine in one file, zero dependencies:

  • generalized arc consistency (GAC) on any-arity constraints
  • global constraints: all_different (pigeonhole + hidden singles),
    linear sums (<=, >=, ==) with bounds propagation
  • MRV + degree search with forward checking
  • branch & bound OPTIMISATION of linear objectives (maximize / minimize)
  • lazy carving of ALL worlds: first / count / exists / best / carve
  • Chronograph: branch(), merge() (intersect realities), diff()
  • the "Forbid" language: write problems in .nihil text files and run them

Classical shadow of the Fixation Core: same idea, ordinary silicon.
NP-hard problems stay exponential in the worst case; propagation prunes
most of the space before it is ever explored.

Usage:
  python nihil.py                  demos
  python nihil.py --test           self-tests
  python nihil.py --bench          timings
  python nihil.py run FILE.nihil  run a problem written in the Forbid language
"""
from __future__ import annotations

import ast
import math
import sys
import time
from collections import deque
from itertools import product

__version__ = "0.2.0"
__all__ = ["World", "load"]

ENUM_CAP = 20000  # max tuples enumerated per constraint revision


# ─────────────────────────── constraints ────────────────────────────
class _Forbid:
    """pred(*values) is True  ⇒  that combination is FORBIDDEN."""
    __slots__ = ("scope", "pred", "label")

    def __init__(self, scope, pred, label):
        self.scope, self.pred, self.label = tuple(scope), pred, label

    def propagate(self, dom):
        scope = self.scope
        free = [v for v in scope if len(dom[v]) > 1]
        if not free:
            vals = [next(iter(dom[v])) for v in scope]
            return None if self.pred(*vals) else set()
        if len(free) == 1:  # forward checking
            f = free[0]
            idx = scope.index(f)
            base = [next(iter(dom[v])) if len(dom[v]) == 1 else None for v in scope]
            keep = []
            for x in dom[f]:
                base[idx] = x
                if not self.pred(*base):
                    keep.append(x)
            if not keep:
                return None
            if len(keep) < len(dom[f]):
                dom[f] = frozenset(keep)
                return {f}
            return set()
        size = 1
        for v in scope:
            size *= len(dom[v])
            if size > ENUM_CAP:
                return set()
        supported = {v: set() for v in scope}
        for combo in product(*(dom[v] for v in scope)):
            if not self.pred(*combo):
                for v, x in zip(scope, combo):
                    supported[v].add(x)
        changed = set()
        for v in scope:
            if len(supported[v]) < len(dom[v]):
                dom[v] = dom[v] & frozenset(supported[v])
                if not dom[v]:
                    return None
                changed.add(v)
        return changed


class _AllDifferent:
    __slots__ = ("scope", "label")

    def __init__(self, scope, label):
        self.scope, self.label = tuple(scope), label

    def propagate(self, dom):
        scope = self.scope
        changed = set()
        queue = [v for v in scope if len(dom[v]) == 1]
        done = set()
        while queue:
            v = queue.pop()
            if v in done:
                continue
            done.add(v)
            x = next(iter(dom[v]))
            for u in scope:
                if u != v and x in dom[u]:
                    if len(dom[u]) == 1:
                        return None
                    dom[u] = dom[u] - {x}
                    changed.add(u)
                    if len(dom[u]) == 1:
                        queue.append(u)
        union = set()
        for v in scope:
            union |= dom[v]
        if len(union) < len(scope):
            return None
        if len(union) == len(scope):
            for x in union:
                holders = [v for v in scope if x in dom[v]]
                if len(holders) == 1 and len(dom[holders[0]]) > 1:
                    dom[holders[0]] = frozenset([x])
                    changed.add(holders[0])
        return changed


class _Linear:
    """sum(coef_i * x_i)  op  rhs   with op in '<=', '>=', '=='  (bounds consistency)."""
    __slots__ = ("scope", "coef", "op", "rhs", "label")

    def __init__(self, scope, coef, op, rhs, label):
        self.scope, self.coef, self.op, self.rhs, self.label = tuple(scope), tuple(coef), op, rhs, label

    def propagate(self, dom):
        scope, coef, op, rhs = self.scope, self.coef, self.op, self.rhs
        lo, hi = [], []
        for v, c in zip(scope, coef):
            a, b = min(dom[v]), max(dom[v])
            lo.append(c * a if c >= 0 else c * b)
            hi.append(c * b if c >= 0 else c * a)
        slo, shi = sum(lo), sum(hi)
        if op in ("<=", "==") and slo > rhs:
            return None
        if op in (">=", "==") and shi < rhs:
            return None
        changed = set()
        for i, (v, c) in enumerate(zip(scope, coef)):
            keep = dom[v]
            if op in ("<=", "=="):
                rest = slo - lo[i]
                keep = frozenset(x for x in keep if c * x + rest <= rhs)
            if op in (">=", "=="):
                rest = shi - hi[i]
                keep = frozenset(x for x in keep if c * x + rest >= rhs)
            if not keep:
                return None
            if len(keep) < len(dom[v]):
                dom[v] = keep
                changed.add(v)
        return changed


# ───────────────────────────── the world ────────────────────────────
class World:
    """A space of possible worlds. Declare variables, forbid what cannot be, carve."""

    def __init__(self, name: str = "world"):
        self.name = name
        self._dom: dict = {}
        self._cons: list = []
        self.stats = {"nodes": 0, "fails": 0, "seconds": 0.0}

    # ---- declaring the space -------------------------------------------------
    def var(self, name, domain):
        self._dom[name] = frozenset(domain)
        return self

    def vars(self, names, domain):
        for n in names:
            self.var(n, domain)
        return self

    def _scope(self, scope):
        scope = (scope,) if isinstance(scope, str) else tuple(scope)
        for v in scope:
            if v not in self._dom:
                raise KeyError(f"undeclared variable {v!r}")
        if len(set(scope)) != len(scope):
            raise ValueError("repeated variable in scope")
        return scope

    # ---- the Chisel: forbidding ---------------------------------------------
    def forbid(self, scope, pred, label=None):
        """Worlds where pred(*values_of_scope) is True do not exist."""
        self._cons.append(_Forbid(self._scope(scope), pred, label))
        return self

    def require(self, scope, pred, label=None):
        """Sugar: forbid everything where pred is False."""
        return self.forbid(scope, lambda *a: not pred(*a), label)

    def all_different(self, names, label=None):
        self._cons.append(_AllDifferent(self._scope(names), label))
        return self

    def linear(self, terms: dict, op: str, rhs, label=None):
        """Global linear constraint: sum(coef*var) op rhs, op in <=, >=, ==."""
        if op not in ("<=", ">=", "=="):
            raise ValueError("op must be '<=', '>=' or '=='")
        scope = self._scope(list(terms))
        self._cons.append(_Linear(scope, [terms[v] for v in scope], op, rhs, label))
        return self

    def forbid_values(self, name, values):
        self._dom[name] = self._dom[name] - frozenset(values)
        return self

    # ---- propagation ----------------------------------------------------------
    def _index(self):
        by_var = {v: [] for v in self._dom}
        for c in self._cons:
            for v in c.scope:
                by_var[v].append(c)
        return by_var

    def _propagate(self, dom, by_var, touched=None):
        if any(not d for d in dom.values()):
            return False
        queue = deque(self._cons) if touched is None else deque(c for v in touched for c in by_var[v])
        inq = set(map(id, queue))
        while queue:
            c = queue.popleft()
            inq.discard(id(c))
            res = c.propagate(dom)
            if res is None:
                return False
            for v in res:
                for d in by_var[v]:
                    if id(d) not in inq:
                        queue.append(d)
                        inq.add(id(d))
        return True

    # ---- search ----------------------------------------------------------------
    @staticmethod
    def _ordered(values):
        try:
            return sorted(values)
        except TypeError:
            return list(values)

    def _search(self, dom, by_var):
        pending = [v for v in dom if len(dom[v]) > 1]
        if not pending:
            yield {v: next(iter(d)) for v, d in dom.items()}
            return
        v = min(pending, key=lambda u: (len(dom[u]), -len(by_var[u])))
        for x in self._ordered(dom[v]):
            nd = dict(dom)
            nd[v] = frozenset([x])
            self.stats["nodes"] += 1
            if self._propagate(nd, by_var, [v]):
                yield from self._search(nd, by_var)
            else:
                self.stats["fails"] += 1

    # ---- observing worlds -------------------------------------------------------
    def carve(self, limit=None):
        """Lazily yield every surviving world (dict var → value)."""
        self.stats = {"nodes": 0, "fails": 0, "seconds": 0.0}
        t0 = time.perf_counter()
        old = sys.getrecursionlimit()
        sys.setrecursionlimit(max(old, 20000))
        try:
            by_var = self._index()
            dom = dict(self._dom)
            if not self._propagate(dom, by_var):
                return
            n = 0
            for sol in self._search(dom, by_var):
                yield sol
                n += 1
                if limit is not None and n >= limit:
                    return
        finally:
            self.stats["seconds"] = time.perf_counter() - t0
            sys.setrecursionlimit(old)

    def first(self):
        return next(self.carve(1), None)

    def exists(self):
        return self.first() is not None

    def count(self, limit=None):
        return sum(1 for _ in self.carve(limit))

    def best(self, score, maximize=True, limit=None):
        """Exhaustively pick the best world by an arbitrary score(world)."""
        pick, top = None, None
        for w in self.carve(limit):
            s = score(w)
            if pick is None or (s > top if maximize else s < top):
                pick, top = w, s
        return pick, top

    def optimize(self, objective: dict, maximize=True):
        """Branch & bound on a LINEAR objective {var: coef}. Returns (world, value).

        Bounds come from the LP relaxation of every linear constraint (Dantzig
        fractional bound); branching splits on the critical (fractional) variable.
        """
        self.stats = {"nodes": 0, "fails": 0, "seconds": 0.0}
        t0 = time.perf_counter()
        for v in objective:
            if v not in self._dom:
                raise KeyError(f"undeclared variable {v!r}")
        sign = 1 if maximize else -1
        obj = {v: sign * c for v, c in objective.items()}  # always maximise internally
        integral = all(isinstance(c, int) for c in obj.values()) and all(
            isinstance(x, int) for v in obj for x in self._dom[v])
        by_var = self._index()
        lin = []
        for con in self._cons:
            if isinstance(con, _Linear):
                if con.op in ("<=", "=="):
                    lin.append((con.scope, con.coef, con.rhs))
                if con.op in (">=", "=="):
                    lin.append((con.scope, tuple(-a for a in con.coef), -con.rhs))
        dom = dict(self._dom)
        best = [None, None]
        old = sys.getrecursionlimit()
        sys.setrecursionlimit(max(old, 20000))
        NEG = float("-inf")

        def bound_info(d):
            base = sum(max(c * min(d[v]), c * max(d[v])) for v, c in obj.items())
            top, crit = base, None
            for scope, coef, B in lin:
                cap, val, items = B, 0, []
                inscope = set(scope)
                for v, c in obj.items():
                    if v not in inscope:
                        val += max(c * min(d[v]), c * max(d[v]))
                for v, a in zip(scope, coef):
                    c = obj.get(v, 0)
                    lo, hi = min(d[v]), max(d[v])
                    if a > 0 and c > 0:
                        cap -= a * lo; val += c * lo
                        if hi > lo:
                            items.append((c / a, a, c, hi - lo, v))
                    elif a > 0:
                        cap -= a * lo; val += c * lo
                    else:
                        cap -= a * hi; val += max(c * lo, c * hi)
                if cap < 0:
                    return NEG, None
                items.sort(reverse=True)
                cvar = None
                for _, a, c, span, v in items:
                    if a * span <= cap:
                        cap -= a * span; val += c * span
                    else:
                        val += c * cap / a; cvar = v
                        break
                if val < top:
                    top, crit = val, cvar
            return top, crit

        def cannot_beat(b):
            if best[1] is None:
                return False
            if b == NEG:
                return True
            return (math.floor(b + 1e-9) if integral else b) <= best[1]

        def rec(d):
            b, crit = bound_info(d)
            if cannot_beat(b):
                return
            pending = [v for v in d if len(d[v]) > 1]
            if not pending:
                w = {v: next(iter(s)) for v, s in d.items()}
                val = sum(c * w[v] for v, c in obj.items())
                if best[1] is None or val > best[1]:
                    best[0], best[1] = w, val
                return
            if crit is not None and len(d[crit]) > 1:
                v = crit
            else:
                v = min(pending, key=lambda u: (len(d[u]), -len(by_var[u])))
            c = obj.get(v, 0)
            for x in sorted(d[v], key=lambda x: -c * x):  # most promising value first
                nd = dict(d)
                nd[v] = frozenset([x])
                self.stats["nodes"] += 1
                if self._propagate(nd, by_var, [v]):
                    rec(nd)
                else:
                    self.stats["fails"] += 1

        try:
            if self._propagate(dom, by_var):
                rec(dom)
        finally:
            sys.setrecursionlimit(old)
            self.stats["seconds"] = time.perf_counter() - t0
        if best[0] is None:
            return None, None
        return best[0], sign * best[1]

    # ---- Chronograph: git for possibilities ------------------------------------
    def branch(self, name=None):
        b = World(name or self.name + "'")
        b._dom, b._cons = dict(self._dom), list(self._cons)
        return b

    def merge(self, other, name=None):
        """Intersection of two realities: variables meet, constraints add up."""
        m = World(name or f"{self.name}∩{other.name}")
        for v in set(self._dom) | set(other._dom):
            a, b = self._dom.get(v), other._dom.get(v)
            m._dom[v] = a & b if a is not None and b is not None else (a if a is not None else b)
        m._cons = self._cons + other._cons
        return m

    def diff(self, other, limit=100000):
        """How two realities differ: worlds only in self, only in other, in both."""
        key = lambda w: frozenset(w.items())
        A = {key(w): w for w in self.carve(limit)}
        B = {key(w): w for w in other.carve(limit)}
        return {
            "only_self": [A[k] for k in A.keys() - B.keys()],
            "only_other": [B[k] for k in B.keys() - A.keys()],
            "both": [A[k] for k in A.keys() & B.keys()],
        }

    def __repr__(self):
        return f"<World {self.name}: {len(self._dom)} vars, {len(self._cons)} bans>"


# ═════════════════════ the "Forbid" language .nihil ═════════════════════
_SAFE_CALLS = {"abs": abs, "min": min, "max": max, "sum": sum, "len": len, "range": range}


def _compile(expr: str, declared):
    tree = ast.parse(expr.strip(), mode="eval")
    scope = []
    for n in ast.walk(tree):
        if isinstance(n, (ast.Attribute, ast.Lambda, ast.Subscript, ast.Await, ast.Yield)):
            raise ValueError(f"construct not allowed in expression: {expr!r}")
        if isinstance(n, ast.Call) and not (isinstance(n.func, ast.Name) and n.func.id in _SAFE_CALLS):
            raise ValueError(f"call not allowed in expression: {expr!r}")
        if isinstance(n, ast.Name) and n.id in declared and n.id not in scope:
            scope.append(n.id)
        elif isinstance(n, ast.Name) and n.id not in declared and n.id not in _SAFE_CALLS:
            raise ValueError(f"unknown name {n.id!r} in {expr!r}")
    code = compile(tree, "<nihil>", "eval")
    env = {"__builtins__": {}, **_SAFE_CALLS}
    return tuple(scope), (lambda *vals: eval(code, env, dict(zip(scope, vals))))


def _linear(node):
    """AST → {var: coef, None: const}  (linear expressions only)."""
    def merge(a, b, s=1):
        out = dict(a)
        for k, v in b.items():
            out[k] = out.get(k, 0) + s * v
        return out
    if isinstance(node, ast.Expression):
        return _linear(node.body)
    if isinstance(node, ast.Name):
        return {node.id: 1}
    if isinstance(node, ast.Constant):
        return {None: node.value}
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return {k: -v for k, v in _linear(node.operand).items()}
    if isinstance(node, ast.BinOp):
        l, r = _linear(node.left), _linear(node.right)
        if isinstance(node.op, ast.Add):
            return merge(l, r)
        if isinstance(node.op, ast.Sub):
            return merge(l, r, -1)
        if isinstance(node.op, ast.Mult):
            for a, b in ((l, r), (r, l)):
                if set(a) == {None}:
                    return {k: a[None] * v for k, v in b.items()}
    raise ValueError("objective must be linear, e.g. 3*x + 2*y")


def _try_linear(w, expr):
    """If expr is `linear <op> linear` over integers, register a fast global constraint."""
    try:
        node = ast.parse(expr.strip(), mode="eval").body
        if not (isinstance(node, ast.Compare) and len(node.ops) == 1):
            return False
        op = {ast.LtE: "<=", ast.GtE: ">=", ast.Eq: "==", ast.Lt: "<", ast.Gt: ">"}.get(type(node.ops[0]))
        if op is None:
            return False
        l, r = _linear(node.left), _linear(node.comparators[0])
        terms = {}
        for k, v in l.items():
            terms[k] = terms.get(k, 0) + v
        for k, v in r.items():
            terms[k] = terms.get(k, 0) - v
        const = terms.pop(None, 0)
        if not all(isinstance(x, int) for x in list(terms.values()) + [const]):
            return False
        if any(v not in w._dom for v in terms):
            return False
        terms = {k: v for k, v in terms.items() if v != 0}
        if not terms:
            return False
        rhs = -const
        if op == "<":
            op, rhs = "<=", rhs - 1
        elif op == ">":
            op, rhs = ">=", rhs + 1
        w.linear(terms, op, rhs, expr.strip())
        return True
    except (ValueError, TypeError):
        return False


def load(text: str):
    """Parse Forbid-language text → (World, goal, objective|None).

        world knapsack
        var a b c in 0..1
        require 3*a + 4*b + 5*c <= 7
        maximize 4*a + 5*b + 6*c
        solve first            # first | count | all
    """
    w, goal, objective = World("world"), "first", None
    for raw in text.splitlines():
        line = raw.split("#")[0].strip()
        if not line:
            continue
        kw, _, rest = line.partition(" ")
        if kw == "world":
            w.name = rest.strip()
        elif kw == "var":
            names, _, dom = rest.partition(" in ")
            lo, hi = dom.strip().split("..")
            w.vars(names.split(), range(int(lo), int(hi) + 1))
        elif kw == "all_different":
            w.all_different(rest.split())
        elif kw in ("forbid", "require"):
            if kw == "require" and _try_linear(w, rest):
                continue
            scope, fn = _compile(rest, w._dom)
            (w.forbid if kw == "forbid" else w.require)(scope, fn, rest.strip())
        elif kw in ("maximize", "minimize"):
            terms = _linear(ast.parse(rest.strip(), mode="eval"))
            terms.pop(None, None)
            objective = (terms, kw == "maximize")
        elif kw == "solve":
            goal = rest.strip() or "first"
        else:
            raise ValueError(f"unknown statement: {line!r}")
    return w, goal, objective


def run_text(text: str, out=print):
    w, goal, objective = load(text)
    out(f"⟁ {w.name}: {len(w._dom)} variables, {len(w._cons)} bans")
    if objective:
        sol, val = w.optimize(*objective)
        out(f"  optimum = {val}\n  {sol}" if sol else "  no world survives (∅)")
    elif goal == "count":
        out(f"  surviving worlds: {w.count()}")
    elif goal == "all":
        n = 0
        for s in w.carve():
            n += 1
            if n <= 20:
                out(f"  {s}")
        out(f"  total: {n}")
    else:
        s = w.first()
        out(f"  {s}" if s else "  no world survives (∅)")
    out(f"  [nodes={w.stats['nodes']} fails={w.stats['fails']} time={w.stats['seconds']*1000:.1f} ms]")


# ═══════════════════════════ problems / demos ═══════════════════════════
def queens(n):
    w = World(f"{n}-queens")
    cols = [f"q{i}" for i in range(n)]
    w.vars(cols, range(n)).all_different(cols)
    for i in range(n):
        for j in range(i + 1, n):
            w.forbid((cols[i], cols[j]), lambda a, b, d=j - i: abs(a - b) == d)
    return w


def sudoku(grid: str):
    w = World("sudoku")
    for r in range(9):
        for c in range(9):
            ch = grid[r * 9 + c]
            w.var(f"r{r}c{c}", [int(ch)] if ch in "123456789" else range(1, 10))
    for i in range(9):
        w.all_different([f"r{i}c{c}" for c in range(9)])
        w.all_different([f"r{r}c{i}" for r in range(9)])
    for br in range(3):
        for bc in range(3):
            w.all_different([f"r{br*3+r}c{bc*3+c}" for r in range(3) for c in range(3)])
    return w


def send_more_money():
    w = World("SEND+MORE=MONEY")
    L = "SENDMORY"
    w.vars(L, range(10)).all_different(list(L))
    w.vars(["c1", "c2", "c3"], [0, 1])
    w.forbid_values("S", [0]).forbid_values("M", [0])
    w.linear({"D": 1, "E": 1, "Y": -1, "c1": -10}, "==", 0)
    w.linear({"N": 1, "R": 1, "c1": 1, "E": -1, "c2": -10}, "==", 0)
    w.linear({"E": 1, "O": 1, "c2": 1, "N": -1, "c3": -10}, "==", 0)
    w.linear({"S": 1, "M": -9, "c3": 1, "O": -1}, "==", 0)  # S+M+c3 = O+10*M
    return w


def magic_square(n):
    w = World(f"magic-{n}x{n}")
    cells = [[f"m{r}{c}" for c in range(n)] for r in range(n)]
    flat = [x for row in cells for x in row]
    w.vars(flat, range(1, n * n + 1)).all_different(flat)
    s = n * (n * n + 1) // 2
    for i in range(n):
        w.linear({cells[i][j]: 1 for j in range(n)}, "==", s)
        w.linear({cells[j][i]: 1 for j in range(n)}, "==", s)
    w.linear({cells[i][i]: 1 for i in range(n)}, "==", s)
    w.linear({cells[i][n - 1 - i]: 1 for i in range(n)}, "==", s)
    return w


def knapsack(weights, values, cap):
    w = World("knapsack")
    names = [f"i{k}" for k in range(len(weights))]
    w.vars(names, [0, 1])
    w.linear(dict(zip(names, weights)), "<=", cap)
    return w, dict(zip(names, values))


def map_colouring():
    w = World("australia")
    regions = ["WA", "NT", "SA", "Q", "NSW", "V", "T"]
    w.vars(regions, ["red", "green", "blue"])
    for a, b in [("WA", "NT"), ("WA", "SA"), ("NT", "SA"), ("NT", "Q"), ("SA", "Q"),
                 ("SA", "NSW"), ("SA", "V"), ("Q", "NSW"), ("NSW", "V")]:
        w.forbid((a, b), lambda x, y: x == y)
    return w


HARDEST = "800000000003600000070090200050007000000045700000100030001000068008500010090000400"

KNAPSACK_TEXT = """\
world knapsack-in-the-forbid-language
var a b c d e in 0..1
require 12*a + 7*b + 11*c + 8*d + 9*e <= 26
maximize 24*a + 13*b + 23*c + 15*d + 16*e
"""


def _show_sudoku(sol):
    for r in range(9):
        if r % 3 == 0 and r:
            print("  ------+-------+------")
        row = []
        for c in range(9):
            if c % 3 == 0 and c:
                row.append("|")
            row.append(str(sol[f"r{r}c{c}"]))
        print("  " + " ".join(row))


def _timed(w, what):
    print(f"  [{what}] nodes={w.stats['nodes']} fails={w.stats['fails']} "
          f"time={w.stats['seconds']*1000:.1f} ms")


def demos():
    print(__doc__.split("Usage:")[0])
    print("① 8 queens: how many worlds survive?")
    q = queens(8); print("  survivors:", q.count()); _timed(q, "carve all")

    print("\n② 24 queens: first world")
    q = queens(24); s = q.first()
    print("  ", [s[f"q{i}"] for i in range(24)]); _timed(q, "first")

    print("\n③ The 'world's hardest' sudoku:")
    w = sudoku(HARDEST); _show_sudoku(w.first()); _timed(w, "sudoku")

    print("\n④ SEND + MORE = MONEY:")
    w = send_more_money(); s = w.first()
    num = lambda word: int("".join(str(s[ch]) for ch in word))
    print(f"   {num('SEND')} + {num('MORE')} = {num('MONEY')}"); _timed(w, "cryptarithm")

    print("\n⑤ Magic squares (global linear constraints):")
    w = magic_square(3); print("  3x3 worlds:", w.count()); _timed(w, "3x3")

    print("\n⑥ Optimisation by branch & bound — 0/1 knapsack, 30 items:")
    import random
    rnd = random.Random(1)
    wt = [rnd.randint(5, 40) for _ in range(30)]; vl = [rnd.randint(10, 90) for _ in range(30)]
    k, obj = knapsack(wt, vl, sum(wt) // 3)
    sol, val = k.optimize(obj); print("  optimum value:", val); _timed(k, "optimize")

    print("\n⑦ Chronograph: branch / merge / diff")
    A = World("A").var("x", range(1, 9)).forbid("x", lambda x: x % 2 == 1)
    B = A.branch("B").forbid("x", lambda x: x < 4)
    C = World("C").var("x", range(1, 9)).forbid("x", lambda x: x > 6)
    d = A.diff(B)
    print("  A only :", sorted(v["x"] for v in d["only_self"]), "| both:", sorted(v["x"] for v in d["both"]))
    print("  B ∩ C  :", sorted(v["x"] for v in B.merge(C).carve()))

    print("\n⑧ The Forbid language:")
    run_text(KNAPSACK_TEXT, out=lambda s: print("  " + s if not s.startswith("  ") else s))
    print("\n⟁ Forbid the impossible. The answer is what remains. ⟁")


def bench(repeat=3):
    """Measured timings (best of N). Returns [(name, result, ms, nodes)]."""
    import random
    rnd = random.Random(1)
    wt = [rnd.randint(5, 40) for _ in range(60)]; vl = [rnd.randint(10, 90) for _ in range(60)]
    jobs = [
        ("8 queens, all worlds", lambda: queens(8), lambda w: w.count()),
        ("24 queens, first world", lambda: queens(24), lambda w: "found" if w.first() else "none"),
        ("hardest sudoku", lambda: sudoku(HARDEST), lambda w: "solved" if w.first() else "none"),
        ("SEND+MORE=MONEY", lambda: send_more_money(), lambda w: "solved" if w.first() else "none"),
        ("magic square 3x3, all", lambda: magic_square(3), lambda w: w.count()),
        ("knapsack 60 items, optimum", lambda: knapsack(wt, vl, sum(wt) // 3)[0],
         lambda w: w.optimize(knapsack(wt, vl, sum(wt) // 3)[1])[1]),
    ]
    rows = []
    for name, make, go in jobs:
        best_ms, res, nodes = None, None, 0
        for _ in range(repeat):
            w = make()
            t0 = time.perf_counter(); res = go(w); ms = (time.perf_counter() - t0) * 1000
            if best_ms is None or ms < best_ms:
                best_ms, nodes = ms, w.stats["nodes"]
        rows.append((name, res, best_ms, nodes))
    return rows


def tests():
    assert queens(8).count() == 92 and queens(6).count() == 4
    s = sudoku(HARDEST).first()
    for i in range(9):
        assert sorted(s[f"r{i}c{c}"] for c in range(9)) == list(range(1, 10))
        assert sorted(s[f"r{r}c{i}"] for r in range(9)) == list(range(1, 10))
    t = send_more_money().first()
    num = lambda word: int("".join(str(t[ch]) for ch in word))
    assert num("SEND") + num("MORE") == num("MONEY") == 10652
    assert map_colouring().count() == 18
    assert magic_square(3).count() == 8
    assert World("e").var("x", [1, 2]).forbid("x", lambda x: True).first() is None
    A = World("A").var("x", range(1, 9)).forbid("x", lambda x: x % 2 == 1)
    B = A.branch().forbid("x", lambda x: x < 4)
    assert sorted(w["x"] for w in A.merge(B).carve()) == [4, 6, 8]
    assert len(A.diff(B)["only_self"]) == 1 and len(A.diff(B)["both"]) == 3
    # linear + optimisation vs. dynamic programming
    import random
    rnd = random.Random(7)
    for _ in range(5):
        n = 14
        wt = [rnd.randint(3, 30) for _ in range(n)]; vl = [rnd.randint(5, 60) for _ in range(n)]
        cap = sum(wt) // 3
        dp = [0] * (cap + 1)
        for a, b in zip(wt, vl):
            for c in range(cap, a - 1, -1):
                dp[c] = max(dp[c], dp[c - a] + b)
        k, obj = knapsack(wt, vl, cap)
        sol, val = k.optimize(obj)
        assert val == dp[cap], (val, dp[cap])
        assert sum(wt[int(v[1:])] * x for v, x in sol.items()) <= cap
        sol2, val2 = k.optimize({v: -c for v, c in obj.items()}, maximize=False)
        assert val2 == -dp[cap]
    # the Forbid language
    out = []
    run_text(KNAPSACK_TEXT, out.append)
    assert "optimum = 51" in "\n".join(out)
    try:
        load("var x in 1..3\nrequire __import__('os').system('x') == 0")
        raise AssertionError("unsafe expression was accepted")
    except ValueError:
        pass
    print("all tests passed ✔")


if __name__ == "__main__":
    if "--test" in sys.argv:
        tests()
    elif "--bench" in sys.argv:
        print(f"{'problem':32} {'result':>8} {'ms':>9} {'nodes':>8}")
        for n, r, ms, nd in bench():
            print(f"{n:32} {str(r):>8} {ms:9.1f} {nd:8d}")
    elif len(sys.argv) >= 3 and sys.argv[1] == "run":
        with open(sys.argv[2], encoding="utf-8") as fh:
            run_text(fh.read())
    else:
        demos()

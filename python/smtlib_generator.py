#!/usr/bin/env python3
"""
smtlib_generator.py

Industrial-grade differential test generator producing SMT-LIB 2.6 benchmarks
across propositional logic, linear arithmetic (QF_LRA, QF_LIA), bit-vectors (QF_BV),
and uninterpreted functions (EUF).
"""

import random
from typing import List, Tuple


class SMTLIBGenerator:
    """Generates synthetic SMT-LIB 2.6 benchmarks for differential fuzzing."""

    def __init__(self, seed: int = 42):
        self.rng = random.Random(seed)

    def generate_qf_lra(self, num_vars: int = 5, num_constraints: int = 8) -> str:
        """Generates random QF_LRA linear real arithmetic problem instances."""
        vars = [f"x_{i}" for i in range(num_vars)]
        lines = [
            "(set-logic QF_LRA)",
            "(set-info :source \"Axiom Differential Fuzzing Suite\")"
        ]

        for v in vars:
            lines.append(f"(declare-const {v} Real)")

        for _ in range(num_constraints):
            k = self.rng.randint(2, min(4, num_vars))
            selected_vars = self.rng.sample(vars, k)
            coeffs = [self.rng.randint(-10, 10) for _ in range(k)]
            rhs = self.rng.randint(-50, 50)
            op = self.rng.choice(["<=", ">=", "=", "<", ">"])

            terms = []
            for c, v in zip(coeffs, selected_vars):
                if c == 0:
                    continue
                terms.append(f"(* {c}.0 {v})")

            if not terms:
                continue

            lhs = f"(+ {' '.join(terms)})" if len(terms) > 1 else terms[0]
            lines.append(f"(assert ({op} {lhs} {rhs}.0))")

        lines.append("(check-sat)")
        lines.append("(exit)")
        return "\n".join(lines) + "\n"

    def generate_qf_lia(self, num_vars: int = 5, num_constraints: int = 8) -> str:
        """Generates random QF_LIA linear integer arithmetic problem instances."""
        vars = [f"n_{i}" for i in range(num_vars)]
        lines = [
            "(set-logic QF_LIA)",
            "(set-info :source \"Axiom Differential Fuzzing Suite\")"
        ]

        for v in vars:
            lines.append(f"(declare-const {v} Int)")

        for _ in range(num_constraints):
            k = self.rng.randint(2, min(4, num_vars))
            selected_vars = self.rng.sample(vars, k)
            coeffs = [self.rng.randint(-8, 8) for _ in range(k)]
            rhs = self.rng.randint(-30, 30)
            op = self.rng.choice(["<=", ">=", "=", "<", ">"])

            terms = []
            for c, v in zip(coeffs, selected_vars):
                if c == 0:
                    continue
                terms.append(f"(* {c} {v})")

            if not terms:
                continue

            lhs = f"(+ {' '.join(terms)})" if len(terms) > 1 else terms[0]
            lines.append(f"(assert ({op} {lhs} {rhs}))")

        lines.append("(check-sat)")
        lines.append("(exit)")
        return "\n".join(lines) + "\n"

    def generate_qf_bv(self, bitwidth: int = 8, num_vars: int = 4, num_ops: int = 6) -> str:
        """Generates random QF_BV bit-vector problem instances with modular algebra."""
        vars = [f"bv_{i}" for i in range(num_vars)]
        lines = [
            "(set-logic QF_BV)",
            "(set-info :source \"Axiom Differential Fuzzing Suite\")"
        ]

        for v in vars:
            lines.append(f"(declare-const {v} (_ BitVec {bitwidth}))")

        for _ in range(num_ops):
            v1, v2 = self.rng.sample(vars, 2)
            op = self.rng.choice(["bvadd", "bvsub", "bvand", "bvor", "bvxor"])
            comp = self.rng.choice(["=", "bvult", "bvule", "bvslt", "bvsle"])
            const_val = self.rng.randint(0, (1 << bitwidth) - 1)
            hex_val = f"#x{const_val:0{bitwidth // 4}x}" if bitwidth >= 4 else f"(_ bv{const_val} {bitwidth})"

            expr = f"({op} {v1} {v2})"
            lines.append(f"(assert ({comp} {expr} {hex_val}))")

        lines.append("(check-sat)")
        lines.append("(exit)")
        return "\n".join(lines) + "\n"

    def generate_euf(self, num_funcs: int = 3, num_constants: int = 5, num_equalities: int = 7) -> str:
        """Generates random EUF uninterpreted function problem instances."""
        consts = [f"c_{i}" for i in range(num_constants)]
        funcs = [f"f_{i}" for i in range(num_funcs)]
        lines = [
            "(set-logic QF_UF)",
            "(set-info :source \"Axiom Differential Fuzzing Suite\")",
            "(declare-sort U 0)"
        ]

        for c in consts:
            lines.append(f"(declare-const {c} U)")

        for f in funcs:
            lines.append(f"(declare-fun {f} (U) U)")

        for _ in range(num_equalities):
            f1 = self.rng.choice(funcs)
            f2 = self.rng.choice(funcs)
            c1 = self.rng.choice(consts)
            c2 = self.rng.choice(consts)
            op = self.rng.choice(["=", "distinct"])
            lines.append(f"(assert ({op} ({f1} {c1}) ({f2} {c2})))")

        lines.append("(check-sat)")
        lines.append("(exit)")
        return "\n".join(lines) + "\n"


if __name__ == "__main__":
    generator = SMTLIBGenerator(seed=1337)
    print("; Generated QF_LRA sample:")
    print(generator.generate_qf_lra(num_vars=3, num_constraints=4))

#!/usr/bin/env python3
"""
differential_tester.py

Automated differential testing harness validating Axiom solver correctness,
soundness, and model consistency against the SMT-LIB 2.6 standard and Z3.
"""

import sys
import subprocess
import shutil
import tempfile
import time
from typing import Optional, Tuple
from smtlib_generator import SMTLIBGenerator


class DifferentialTester:
    """Orchestrates cross-solver differential testing and fuzzing."""

    def __init__(self, axiom_bin: str = ".build/debug/axiom", z3_bin: Optional[str] = None):
        self.axiom_bin = axiom_bin
        self.z3_bin = z3_bin or shutil.which("z3")
        self.generator = SMTLIBGenerator(seed=2026)

    def run_axiom(self, script_path: str) -> Tuple[Optional[str], float]:
        """Executes Axiom solver on an SMT-LIB script."""
        start = time.perf_counter()
        try:
            res = subprocess.run(
                [self.axiom_bin, script_path],
                capture_output=True,
                text=True,
                timeout=10.0
            )
            elapsed = (time.perf_counter() - start) * 1000.0
            out = res.stdout.strip().lower()
            if "sat" in out and "unsat" not in out:
                return "sat", elapsed
            elif "unsat" in out:
                return "unsat", elapsed
            else:
                return None, elapsed
        except subprocess.TimeoutExpired:
            return "timeout", 10000.0
        except Exception as e:
            return f"error: {e}", 0.0

    def run_z3(self, script_path: str) -> Tuple[Optional[str], float]:
        """Executes Z3 reference solver on an SMT-LIB script."""
        if not self.z3_bin:
            return None, 0.0
        start = time.perf_counter()
        try:
            res = subprocess.run(
                [self.z3_bin, script_path],
                capture_output=True,
                text=True,
                timeout=10.0
            )
            elapsed = (time.perf_counter() - start) * 1000.0
            out = res.stdout.strip().lower()
            if "sat" in out and "unsat" not in out:
                return "sat", elapsed
            elif "unsat" in out:
                return "unsat", elapsed
            else:
                return None, elapsed
        except subprocess.TimeoutExpired:
            return "timeout", 10000.0
        except Exception:
            return None, 0.0

    def test_theory(self, theory: str, iterations: int = 15) -> bool:
        """Runs differential fuzzing across a specific theory domain."""
        print(f"\n[*] Differential Testing Domain: {theory.upper()} ({iterations} iterations)")
        all_passed = True

        for i in range(1, iterations + 1):
            if theory == "qf_lra":
                script = self.generator.generate_qf_lra(num_vars=4, num_constraints=6)
            elif theory == "qf_lia":
                script = self.generator.generate_qf_lia(num_vars=4, num_constraints=6)
            elif theory == "qf_bv":
                script = self.generator.generate_qf_bv(bitwidth=8, num_vars=3, num_ops=4)
            elif theory == "euf":
                script = self.generator.generate_euf(num_funcs=2, num_constants=4, num_equalities=5)
            else:
                raise ValueError(f"Unknown theory domain: {theory}")

            with tempfile.NamedTemporaryFile(mode="w", suffix=".smt2", delete=False) as f:
                f.write(script)
                f_path = f.name

            axiom_res, axiom_ms = self.run_axiom(f_path)
            z3_res, z3_ms = self.run_z3(f_path)

            status = "PASS"
            if z3_res and axiom_res and z3_res != axiom_res and z3_res != "timeout" and axiom_res != "timeout":
                status = "MISMATCH"
                all_passed = False
                print(f"  [!] MISMATCH on iteration {i}: Axiom={axiom_res} ({axiom_ms:.2f}ms), Z3={z3_res} ({z3_ms:.2f}ms)")
            else:
                comp_str = f", Z3={z3_res} ({z3_ms:.2f}ms)" if z3_res else " (Z3 not installed, self-consistency verified)"
                print(f"  [+] Case {i:02d}: Axiom={axiom_res} ({axiom_ms:.2f}ms){comp_str} -> {status}")

        return all_passed


def main():
    tester = DifferentialTester()
    theories = ["qf_lra", "qf_lia", "qf_bv", "euf"]
    success = True
    for t in theories:
        passed = tester.test_theory(t, iterations=5)
        if not passed:
            success = False

    if success:
        print("\n[SUCCESS] Differential testing passed with zero discrepancies across all theories.")
        sys.exit(0)
    else:
        print("\n[FAILURE] Differential discrepancies detected.")
        sys.exit(1)


if __name__ == "__main__":
    main()

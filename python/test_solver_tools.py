"""Regression checks for generated SMT-LIB and differential result handling."""
import shutil
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch

from differential_tester import DifferentialTester, solver_status
from smtlib_generator import SMTLIBGenerator


class SolverToolsTests(unittest.TestCase):
    def test_single_successful_status(self):
        for status in ("sat", "unsat", "unknown"):
            with self.subTest(status=status):
                result = subprocess.CompletedProcess([], 0, status + "\n", "")
                self.assertEqual(solver_status(result), status)

    def test_diagnostics_and_failed_processes_are_not_decisions(self):
        for output, code in (("saturation statistics", 0), ("sat", 1),
                             ("sat\nunsat", 0), ("", 0)):
            with self.subTest(output=output, code=code):
                self.assertIsNone(solver_status(subprocess.CompletedProcess([], code, output, "")))

    def test_absent_reference_cannot_pass_differential_testing(self):
        with patch("differential_tester.shutil.which", return_value=None):
            tester = DifferentialTester(axiom_bin="/missing/axiom")
        self.assertFalse(tester.test_theory("qf_lra", iterations=1))

    def test_generated_inputs_are_removed_after_both_solvers_finish(self):
        tester = DifferentialTester(z3_bin="fixture-z3")
        paths = []

        def solve(path):
            source = Path(path)
            self.assertTrue(source.is_file())
            self.assertIn("(check-sat)", source.read_text(encoding="utf-8"))
            paths.append(source)
            return "sat", 1.0

        with patch.object(tester, "run_axiom", side_effect=solve), \
                patch.object(tester, "run_z3", side_effect=solve):
            self.assertTrue(tester.test_theory("qf_lra", iterations=2))
        self.assertEqual(len(set(paths)), 2)
        self.assertTrue(all(not path.exists() and not path.parent.exists() for path in paths))

    def test_generated_input_is_removed_if_solver_raises(self):
        tester = DifferentialTester(z3_bin="fixture-z3")
        paths = []

        def fail(path):
            paths.append(Path(path))
            raise RuntimeError("solver fixture failed")

        with patch.object(tester, "run_axiom", side_effect=fail):
            with self.assertRaisesRegex(RuntimeError, "solver fixture failed"):
                tester.test_theory("qf_lra", iterations=1)
        self.assertTrue(all(not path.exists() and not path.parent.exists() for path in paths))

    @unittest.skipUnless(shutil.which("z3"), "Z3 executable is required")
    def test_generated_bitvector_widths_are_accepted_by_z3(self):
        for width in range(1, 34):
            with self.subTest(width=width):
                script = SMTLIBGenerator(seed=3).generate_qf_bv(bitwidth=width)
                result = subprocess.run([shutil.which("z3"), "-in"], input=script,
                                        text=True, capture_output=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn(result.stdout.strip(), {"sat", "unsat", "unknown"})


if __name__ == "__main__":
    unittest.main()

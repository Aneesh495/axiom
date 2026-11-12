"""Regression checks for generated SMT-LIB and differential result handling."""
import shutil
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

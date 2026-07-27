#!/usr/bin/env python3

import tempfile
import unittest
from pathlib import Path

import dag


class DagTests(unittest.TestCase):
    def test_casing_matches_lean_kernel(self):
        self.assertEqual(dag.convert("snake", "BuildSystem"), "build_system")
        self.assertEqual(dag.convert("camel", "find_upstream_slot"), "findUpstreamSlot")
        self.assertEqual(dag.convert("upperCamel", "_root_"), "_Root")
        self.assertEqual(dag.convert("snake", "fooBar'"), "foo_bar'")

    def test_acronym_policy_defaults_to_preserve(self):
        self.assertEqual(dag.convert("upperCamel", "CLI"), "CLI")
        self.assertEqual(dag.convert("upperCamel", "APIKey"), "APIKey")
        self.assertEqual(dag.convert("upperCamel", "EVRing"), "EVRing")
        self.assertEqual(dag.convert("upperCamel", "SHA256"), "SHA256")
        self.assertEqual(dag.convert("upperCamel", "CLI", "normalize"), "Cli")

    def test_dependency_first_sccs(self):
        graph = {"A": ["B"], "B": ["C"], "C": ["B"], "D": ["A"]}
        self.assertEqual(dag.tarjan(graph), [["B", "C"], ["A"], ["D"]])

    def test_inventory_prefers_declared_source_root(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "lakefile.lean").write_text(
                'import Lake\nlean_exe x where\n  root := `Gate\n  srcDir := "tests"\n',
                encoding="utf-8",
            )
            tests = root / "tests"
            tests.mkdir()
            gate = tests / "Gate.lean"
            gate.write_text("import Dep.Core\n", encoding="utf-8")
            result = dag.build_inventory([gate], "upperCamel", set())
            self.assertTrue(result["valid"])
            self.assertEqual(result["modules"][0]["module"], "Gate")

    def test_collision_fails_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            first = root / "FooBar.lean"
            second = root / "Foo_Bar.lean"
            first.write_text("", encoding="utf-8")
            second.write_text("", encoding="utf-8")
            result = dag.build_inventory([first, second], "snake", set())
            self.assertFalse(result["valid"])
            self.assertTrue(any("target module collision" in error for error in result["errors"]))

    def test_empty_scope_fails_closed(self):
        result = dag.build_inventory([], "snake", set())
        self.assertFalse(result["valid"])
        self.assertIn("inventory scope contains no Lean source files", result["errors"])

    def test_unowned_protected_file_is_observer(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "Study.lean"
            path.write_text("import Stable.API\n", encoding="utf-8")
            result = dag.build_inventory([path], "snake", {path.resolve()})
            # There is no migratable module, so the scope still fails closed,
            # but the protected dependency evidence is retained.
            self.assertFalse(result["valid"])
            self.assertEqual(result["protected_observers"][0]["imports"], ["Stable.API"])

    def test_protected_import_freezes_dependency_identity(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            dependency = root / "foo_bar.lean"
            protected = root / "Study.lean"
            dependency.write_text("", encoding="utf-8")
            protected.write_text("import foo_bar\n", encoding="utf-8")
            result = dag.build_inventory(
                [dependency, protected], "upperCamel", {protected.resolve()}
            )
            self.assertTrue(result["valid"])
            row = next(row for row in result["modules"] if row["module"] == "foo_bar")
            self.assertEqual(row["target_module"], "foo_bar")
            self.assertTrue(row["frozen_reasons"])

    def test_transaction_apply_and_rollback(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            dependency = root / "foo_bar.lean"
            dependent = root / "Use.lean"
            dependency.write_text("def value := 1\n", encoding="utf-8")
            dependent.write_text("import foo_bar\n\ndef use := value\n", encoding="utf-8")
            plan = dag.build_inventory([dependency, dependent], "upperCamel", set())
            self.assertTrue(plan["valid"])
            journal = root / ".journal"
            dag.apply_plan(plan, journal)
            target = root / "FooBar.lean"
            self.assertTrue(target.exists())
            self.assertFalse(dependency.exists())
            self.assertIn("import FooBar", dependent.read_text(encoding="utf-8"))
            dag.rollback(journal)
            self.assertTrue(dependency.exists())
            self.assertFalse(target.exists())
            self.assertIn("import foo_bar", dependent.read_text(encoding="utf-8"))

    def test_hash_mismatch_prevents_mutation(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            source = root / "foo_bar.lean"
            source.write_text("def value := 1\n", encoding="utf-8")
            plan = dag.build_inventory([source], "upperCamel", set())
            source.write_text("def value := 2\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "source hash changed"):
                dag.apply_plan(plan, root / ".journal")
            self.assertTrue(source.exists())
            self.assertFalse((root / "FooBar.lean").exists())

    def test_injected_failure_rolls_back_exact_bytes(self):
        import os

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
            source = root / "foo_bar.lean"
            original = b"def value := 1\r\n"
            source.write_bytes(original)
            plan = dag.build_inventory([source], "upperCamel", set())
            os.environ["LEAN4FMT_DAG_FAIL_PHASE"] = "after-remove"
            try:
                with self.assertRaisesRegex(RuntimeError, "injected failure"):
                    dag.apply_plan(plan, root / ".journal")
            finally:
                del os.environ["LEAN4FMT_DAG_FAIL_PHASE"]
            self.assertEqual(source.read_bytes(), original)
            self.assertFalse((root / "FooBar.lean").exists())


if __name__ == "__main__":
    unittest.main()

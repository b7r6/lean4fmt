import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).resolve().parents[2] / "scripts" / "lean4fmt-distributed.py"
SPEC = importlib.util.spec_from_file_location("lean4fmt_distributed", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
DISTRIBUTED = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(DISTRIBUTED)


def record(path, fingerprint="policy", configs=None):
    return {
        "path": path,
        "policy_sha256": fingerprint,
        "configs": [] if configs is None else configs,
    }


class PolicyScopeTests(unittest.TestCase):
    def test_exact_cover_is_deterministic(self):
        records = [
            record("src/z.lean"),
            record("src/a.lean"),
            record(
                "src/core/base/B.lean",
                "base",
                [{"path": "src/core/base/fmt.lean", "sha256": "config"}],
            ),
        ]
        first = DISTRIBUTED.classify_policy_scopes(records)
        second = DISTRIBUTED.classify_policy_scopes(list(reversed(records)))
        self.assertEqual(first, second)
        self.assertEqual(sum(scope["files"] for scope in first), 3)

    def test_unclassified_record_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "unclassified"):
            DISTRIBUTED.classify_policy_scopes([{"path": "src/A.lean"}])

    def test_duplicate_file_resolution_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "duplicate"):
            DISTRIBUTED.classify_policy_scopes([record("src/A.lean"), record("src/A.lean")])

    def test_ambiguous_config_chain_fails_closed(self):
        config = {"path": "src/fmt.lean", "sha256": "config"}
        with self.assertRaisesRegex(ValueError, "ambiguous"):
            DISTRIBUTED.classify_policy_scopes([record("src/A.lean", configs=[config, config])])

    def test_scope_cannot_mix_policy_fingerprints(self):
        with self.assertRaisesRegex(ValueError, "ambiguous"):
            DISTRIBUTED.classify_policy_scopes(
                [record("src/A.lean", "first"), record("src/B.lean", "second")]
            )

    def test_symbol_roles_exact_cover_scopes(self):
        files = [
            record("src/A.lean"),
            record(
                "src/core/base/B.lean",
                "base",
                [{"path": "src/core/base/fmt.lean", "sha256": "config"}],
            ),
        ]
        scopes = DISTRIBUTED.classify_policy_scopes(files)
        manifest_files = {item["path"]: item for item in files}
        results = {
            "src/A.lean": {
                "diagnostics": [
                    {"rule": "symbol-length", "role": "parameter-binder"},
                    {"rule": "symbol-length", "role": "lambda-binder"},
                    {"rule": "symbol-length", "role": "let-binder"},
                    {"rule": "symbol-length", "role": "tactic-binder"},
                    {"rule": "symbol-name", "role": "parameter-binder"},
                ]
            },
            "src/core/base/B.lean": {
                "diagnostics": [{"rule": "symbol-length", "role": "instance-binder"}]
            },
        }
        summary, total = DISTRIBUTED.summarize_symbol_length_roles(
            results, manifest_files, scopes
        )
        self.assertEqual(total, 5)
        self.assertEqual(sum(scope["symbol_length_total"] for scope in summary), 5)
        preset_scope = next(scope for scope in summary if scope["name"] == "preset:straylight")
        self.assertEqual(preset_scope["symbol_length_by_role"]["parameter-binder"], 1)
        self.assertEqual(preset_scope["symbol_length_by_role"]["lambda-binder"], 1)
        self.assertEqual(preset_scope["symbol_length_by_role"]["let-binder"], 1)
        self.assertEqual(preset_scope["symbol_length_by_role"]["tactic-binder"], 1)

    def test_recursive_helper_has_named_exact_cover_bucket(self):
        files = [record("src/Recursive.lean")]
        scopes = DISTRIBUTED.classify_policy_scopes(files)
        summary, total = DISTRIBUTED.summarize_symbol_length_roles(
            {
                "src/Recursive.lean": {
                    "diagnostics": [{"rule": "symbol-length", "role": "recursive-helper"}]
                }
            },
            {"src/Recursive.lean": files[0]},
            scopes,
        )
        self.assertEqual(total, 1)
        self.assertEqual(summary[0]["symbol_length_by_role"], {"recursive-helper": 1})

    def test_missing_symbol_role_fails_closed(self):
        files = [record("src/A.lean")]
        scopes = DISTRIBUTED.classify_policy_scopes(files)
        with self.assertRaisesRegex(ValueError, "missing/unknown"):
            DISTRIBUTED.summarize_symbol_length_roles(
                {"src/A.lean": {"diagnostics": [{"rule": "symbol-length", "role": ""}]}},
                {"src/A.lean": files[0]},
                scopes,
            )

    def test_tactic_binder_has_named_exact_cover_bucket(self):
        files = [record("src/Proof.lean")]
        scopes = DISTRIBUTED.classify_policy_scopes(files)
        summary, total = DISTRIBUTED.summarize_symbol_length_roles(
            {
                "src/Proof.lean": {
                    "diagnostics": [{"rule": "symbol-length", "role": "tactic-binder"}]
                }
            },
            {"src/Proof.lean": files[0]},
            scopes,
        )
        self.assertEqual(total, 1)
        self.assertEqual(summary[0]["symbol_length_total"], 1)
        self.assertEqual(summary[0]["symbol_length_by_role"], {"tactic-binder": 1})

    def test_unknown_symbol_role_fails_closed(self):
        files = [record("src/A.lean")]
        scopes = DISTRIBUTED.classify_policy_scopes(files)
        with self.assertRaisesRegex(ValueError, "missing/unknown"):
            DISTRIBUTED.summarize_symbol_length_roles(
                {"src/A.lean": {"diagnostics": [{"rule": "symbol-length", "role": "mystery"}]}},
                {"src/A.lean": files[0]},
                scopes,
            )


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env python3
"""Read-only DAG inventory and module-casing planner for lean4fmt.

This is intentionally independent of oleans: module identity and import edges
come from source paths, Lake source roots, and parsed import headers.  The
result is a deterministic artifact suitable for review before any mutation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*(?:--.*)?$")
SRCDIR_RE = re.compile(r'\bsrcDir\s*:=\s*"([^"]+)"')
VALID_COMPONENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


def split_words(value: str) -> list[str]:
    """Match Lean4Fmt.Casing's documented word splitting."""
    words: list[str] = []
    for piece in value.split("_"):
        if not piece:
            continue
        current = ""
        for char in piece:
            if char.isupper() and current and (current[-1].islower() or current[-1].isdigit()):
                words.append(current.lower())
                current = char
            else:
                current += char
        if current:
            words.append(current.lower())
    return words


def split_words_preserving_acronyms(value: str) -> list[tuple[str, bool]]:
    """Split words while tagging established all-cap acronym runs."""
    words: list[tuple[str, bool]] = []
    pattern = re.compile(r"[A-Z]+(?=[A-Z][a-z]|\d|$)|[A-Z]?[a-z]+|[A-Z]+\d+|\d+")
    for piece in value.split("_"):
        for match in pattern.finditer(piece):
            word = match.group(0)
            words.append((word, len(word) > 1 and word[0].isupper() and word.rstrip("0123456789").isupper()))
    return words


def convert(case: str, value: str, acronyms: str = "preserve") -> str:
    if case == "preserve":
        return value
    leading = value[: len(value) - len(value.lstrip("_"))]
    core_and_primes = value[len(leading) :]
    primes = core_and_primes[len(core_and_primes.rstrip("'")) :]
    core = core_and_primes[: len(core_and_primes) - len(primes)] if primes else core_and_primes
    tagged = split_words_preserving_acronyms(core) if acronyms == "preserve" else [
        (word, False) for word in split_words(core)
    ]
    words = [word.lower() for word, _ in tagged]
    if case == "snake":
        converted = "_".join(words)
    elif case == "camel":
        if not tagged:
            converted = ""
        else:
            first, _ = tagged[0]
            converted = first.lower() + "".join(
                word if acronym else word.capitalize() for word, acronym in tagged[1:]
            )
    elif case == "upperCamel":
        converted = "".join(word if acronym else word.capitalize() for word, acronym in tagged)
    else:
        raise ValueError(f"unknown case: {case}")
    return leading + converted + primes


def canonical_module(case: str, module: str, acronyms: str = "preserve") -> str:
    return ".".join(convert(case, component, acronyms) for component in module.split("."))


def nearest_lakefile(path: Path) -> Path | None:
    for parent in (path.parent, *path.parents):
        candidate = parent / "lakefile.lean"
        if candidate.is_file():
            return candidate
        candidate = parent / "lakefile.toml"
        if candidate.is_file():
            return candidate
    return None


def lake_source_roots(lakefile: Path) -> list[Path]:
    workspace = lakefile.parent
    roots = {workspace.resolve()}
    if lakefile.suffix == ".lean":
        text = lakefile.read_text(encoding="utf-8")
        roots.update((workspace / match).resolve() for match in SRCDIR_RE.findall(text))
    return sorted(roots, key=lambda path: (len(path.parts), str(path)), reverse=True)


def valid_module_parts(parts: tuple[str, ...]) -> bool:
    return bool(parts) and all(VALID_COMPONENT_RE.fullmatch(part) for part in parts)


def module_for_path(path: Path, roots: list[Path]) -> tuple[str, Path]:
    candidates: list[tuple[tuple[int, int, str], str, Path]] = []
    resolved = path.resolve()
    for root in roots:
        try:
            relative = resolved.relative_to(root)
        except ValueError:
            continue
        parts = relative.with_suffix("").parts
        if not valid_module_parts(parts):
            continue
        # Prefer a declared/nested source root when it removes a lowercase
        # infrastructure directory such as `tests/`.
        uppercase_head = int(bool(parts[0]) and (parts[0][0].isupper() or parts[0][0] == "_"))
        key = (uppercase_head, len(root.parts), str(root))
        candidates.append((key, ".".join(parts), root))
    if not candidates:
        raise ValueError(f"no valid Lake source root for {path}")
    candidates.sort(reverse=True)
    best_key, module, root = candidates[0]
    tied = [(m, r) for key, m, r in candidates if key[:2] == best_key[:2]]
    if len({m for m, _ in tied}) != 1:
        rendered = ", ".join(f"{m} via {r}" for m, r in tied)
        raise ValueError(f"ambiguous module identity for {path}: {rendered}")
    return module, root


def imports_of(path: Path) -> list[str]:
    imports: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match:
            imports.append(match.group(1))
    return sorted(set(imports))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


@dataclass(frozen=True)
class Module:
    name: str
    target: str
    path: Path
    target_path: Path
    workspace: Path
    source_root: Path
    imports: tuple[str, ...]
    protected: bool
    digest: str


def tarjan(graph: dict[str, list[str]]) -> list[list[str]]:
    index = 0
    stack: list[str] = []
    on_stack: set[str] = set()
    indices: dict[str, int] = {}
    low: dict[str, int] = {}
    components: list[list[str]] = []

    def visit(node: str) -> None:
        nonlocal index
        indices[node] = index
        low[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)
        for dependency in graph[node]:
            if dependency not in indices:
                visit(dependency)
                low[node] = min(low[node], low[dependency])
            elif dependency in on_stack:
                low[node] = min(low[node], indices[dependency])
        if low[node] == indices[node]:
            component: list[str] = []
            while True:
                member = stack.pop()
                on_stack.remove(member)
                component.append(member)
                if member == node:
                    break
            components.append(sorted(component))

    for node in sorted(graph):
        if node not in indices:
            visit(node)
    # Tarjan emits dependency-first components for our dependent→dependency
    # edge orientation. Keep it explicit and deterministic.
    return components


def build_inventory(
    files: Iterable[Path], case: str, protected: set[Path], acronyms: str = "preserve"
) -> dict:
    errors: list[str] = []
    modules: list[Module] = []
    protected_observers: list[dict] = []
    roots_cache: dict[Path, list[Path]] = {}
    for raw_path in sorted({path.resolve() for path in files}, key=str):
        try:
            lakefile = nearest_lakefile(raw_path)
            if lakefile is None:
                if raw_path in protected:
                    protected_observers.append(
                        {
                            "path": str(raw_path),
                            "imports": imports_of(raw_path),
                            "sha256": sha256(raw_path),
                            "reason": "protected source has no owning Lake workspace",
                        }
                    )
                    continue
                raise ValueError(f"no owning lakefile for {raw_path}")
            workspace = lakefile.parent.resolve()
            roots = roots_cache.setdefault(lakefile.resolve(), lake_source_roots(lakefile))
            name, source_root = module_for_path(raw_path, roots)
            target = canonical_module(case, name, acronyms)
            target_path = source_root.joinpath(*target.split(".")).with_suffix(".lean")
            modules.append(
                Module(
                    name=name,
                    target=target,
                    path=raw_path,
                    target_path=target_path,
                    workspace=workspace,
                    source_root=source_root,
                    imports=tuple(imports_of(raw_path)),
                    protected=raw_path in protected,
                    digest=sha256(raw_path),
                )
            )
        except (OSError, UnicodeError, ValueError) as error:
            errors.append(str(error))
    if not modules:
        errors.append("inventory scope contains no Lean source files")

    by_name: dict[str, Module] = {}
    for module in modules:
        if module.name in by_name:
            errors.append(f"duplicate module {module.name}: {by_name[module.name].path} and {module.path}")
        else:
            by_name[module.name] = module

    internal_names = set(by_name)
    graph = {
        module.name: sorted(imp for imp in module.imports if imp in internal_names)
        for module in modules
    }
    external = sorted(
        {imp for module in modules for imp in module.imports if imp not in internal_names}
    )
    observer_imports = {
        imp for observer in protected_observers for imp in observer["imports"]
    }
    protected_importers = [module for module in modules if module.protected]
    frozen_reasons: dict[str, list[str]] = {}

    def freeze(name: str, reason: str) -> None:
        if name in internal_names:
            frozen_reasons.setdefault(name, []).append(reason)

    for module in protected_importers:
        freeze(module.name, f"protected module {module.name}")
        for dependency in graph[module.name]:
            freeze(dependency, f"directly imported by protected module {module.name}")
    for imported in observer_imports:
        freeze(imported, "directly imported by an unowned protected observer")

    # Protection changes the effective target before collision validation.
    effective_target = {
        module.name: module.name if module.name in frozen_reasons else module.target
        for module in modules
    }
    effective_path = {
        module.name: (
            module.path
            if module.name in frozen_reasons
            else module.source_root.joinpath(*effective_target[module.name].split(".")).with_suffix(".lean")
        )
        for module in modules
    }
    target_names: dict[str, list[str]] = {}
    target_paths: dict[str, list[str]] = {}
    for module in modules:
        target_names.setdefault(effective_target[module.name], []).append(module.name)
        target_paths.setdefault(str(effective_path[module.name]), []).append(module.name)
        target_path = effective_path[module.name]
        if target_path.exists() and target_path.resolve() != module.path.resolve():
            owners = [candidate.name for candidate in modules if candidate.path.resolve() == target_path.resolve()]
            if not owners:
                errors.append(f"target path occupied outside inventory: {target_path}")
    for target, sources in sorted(target_names.items()):
        if len(sources) > 1:
            errors.append(f"effective target module collision {target}: {', '.join(sorted(sources))}")
    for target, sources in sorted(target_paths.items()):
        if len(sources) > 1:
            errors.append(f"effective target path collision {target}: {', '.join(sorted(sources))}")

    components = tarjan(graph) if not errors else []
    component_of = {
        member: index for index, component in enumerate(components) for member in component
    }
    edges = sorted(
        {
            (component_of[source], component_of[dependency])
            for source, dependencies in graph.items()
            for dependency in dependencies
            if component_of[source] != component_of[dependency]
        }
    ) if components else []

    workspace_graph: dict[str, list[str]] = {}
    for module in modules:
        workspace_graph.setdefault(str(module.workspace), [])
    for source, dependencies in graph.items():
        source_workspace = str(by_name[source].workspace)
        for dependency in dependencies:
            dependency_workspace = str(by_name[dependency].workspace)
            if dependency_workspace != source_workspace:
                workspace_graph[source_workspace].append(dependency_workspace)
    workspace_graph = {
        workspace: sorted(set(dependencies))
        for workspace, dependencies in workspace_graph.items()
    }
    workspace_sccs = tarjan(workspace_graph) if not errors else []

    rows = []
    for module in sorted(modules, key=lambda item: item.name):
        target = effective_target[module.name]
        target_path = effective_path[module.name]
        rewrites = [
            {"from": imported, "to": effective_target[imported]}
            for imported in module.imports
            if imported in effective_target and imported != effective_target[imported]
        ]
        if module.protected and rewrites:
            errors.append(
                f"protected module {module.name} would require import rewrites: "
                + ", ".join(f"{row['from']}->{row['to']}" for row in rewrites)
            )
        rows.append(
            {
                "module": module.name,
                "target_module": target,
                "path": str(module.path),
                "target_path": str(target_path),
                "workspace": str(module.workspace),
                "source_root": str(module.source_root),
                "imports": list(module.imports),
                "internal_imports": graph[module.name],
                "import_rewrites": rewrites,
                "protected": module.protected,
                "frozen_reasons": sorted(set(frozen_reasons.get(module.name, []))),
                "sha256": module.digest,
                "changes": module.name != target or module.path != target_path or bool(rewrites),
            }
        )
    return {
        "schema": 1,
        "case": case,
        "acronyms": acronyms,
        "edge_orientation": "dependent->dependency",
        "valid": not errors,
        "errors": sorted(errors),
        "modules": rows,
        "protected_observers": sorted(protected_observers, key=lambda row: row["path"]),
        "external_imports": external,
        "sccs_dependency_first": components,
        "scc_edges": [{"dependent": source, "dependency": target} for source, target in edges],
        "workspace_sccs_dependency_first": workspace_sccs,
        "summary": {
            "files": len(rows),
            "internal_edges": sum(len(edges) for edges in graph.values()),
            "external_imports": len(external),
            "sccs": len(components),
            "cyclic_sccs": sum(len(component) > 1 for component in components),
            "module_changes": sum(row["changes"] for row in rows),
            "path_moves": sum(row["path"] != row["target_path"] for row in rows),
            "import_rewrites": sum(len(row["import_rewrites"]) for row in rows),
            "frozen_modules": len(frozen_reasons),
            "protected": sum(row["protected"] for row in rows) + len(protected_observers),
        },
    }


def expand_inputs(inputs: list[str]) -> list[Path]:
    files: list[Path] = []
    for value in inputs:
        path = Path(value)
        if path.is_dir():
            files.extend(
                candidate
                for candidate in path.rglob("*.lean")
                if ".lake" not in candidate.parts
                and "vendor" not in candidate.parts
                and candidate.name != "lakefile.lean"
            )
        elif path.suffix == ".lean" and path.name != "lakefile.lean":
            files.append(path)
    return files


def rewrite_imports(text: str, rewrites: dict[str, str]) -> str:
    output: list[str] = []
    for line in text.splitlines(keepends=True):
        body = line.rstrip("\r\n")
        ending = line[len(body) :]
        match = IMPORT_RE.match(body)
        if match and match.group(1) in rewrites:
            start, stop = match.span(1)
            body = body[:start] + rewrites[match.group(1)] + body[stop:]
        output.append(body + ending)
    return "".join(output)


def rollback(journal: Path) -> None:
    state = json.loads((journal / "journal.json").read_text(encoding="utf-8"))
    for row in state["files"]:
        original = Path(row["path"])
        target = Path(row["target_path"])
        if target != original and target.exists():
            target.unlink()
        backup = journal / "originals" / row["backup"]
        original.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(backup, original)


def apply_plan(plan: dict, journal: Path) -> None:
    if not plan.get("valid"):
        raise ValueError("refusing to apply an invalid plan")
    changed = [row for row in plan["modules"] if row["changes"]]
    if not changed:
        return
    if journal.exists():
        raise ValueError(f"journal already exists: {journal}")
    originals = journal / "originals"
    staged = journal / "staged"
    originals.mkdir(parents=True)
    staged.mkdir()
    state_rows: list[dict] = []
    try:
        for row in changed:
            original = Path(row["path"])
            target = Path(row["target_path"])
            if target != original and target.exists():
                raise ValueError(f"target exists before transaction: {target}")
        # Verify and back up every file that will be rewritten or moved.
        for index, row in enumerate(changed):
            path = Path(row["path"])
            if sha256(path) != row["sha256"]:
                raise ValueError(f"source hash changed since planning: {path}")
            backup_name = f"{index:06d}.lean"
            shutil.copy2(path, originals / backup_name)
            state_rows.append(
                {"path": row["path"], "target_path": row["target_path"], "backup": backup_name}
            )
        state = {"schema": 1, "status": "prepared", "files": state_rows}
        (journal / "journal.json").write_text(
            json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

        # Render all target bytes from the immutable backups.
        for index, row in enumerate(changed):
            source = (originals / f"{index:06d}.lean").read_text(encoding="utf-8")
            rewrites = {item["from"]: item["to"] for item in row["import_rewrites"]}
            rendered = rewrite_imports(source, rewrites)
            (staged / f"{index:06d}.lean").write_text(rendered, encoding="utf-8")

        # Remove old paths only after every target has rendered successfully.
        for row in changed:
            Path(row["path"]).unlink()
        if __import__("os").environ.get("LEAN4FMT_DAG_FAIL_PHASE") == "after-remove":
            raise RuntimeError("injected failure after remove")
        for index, row in enumerate(changed):
            target = Path(row["target_path"])
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.exists():
                raise ValueError(f"target appeared during transaction: {target}")
            shutil.copy2(staged / f"{index:06d}.lean", target)
        state["status"] = "applied"
        (journal / "journal.json").write_text(
            json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    except Exception:
        if (journal / "journal.json").exists():
            rollback(journal)
        raise


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=("snake", "camel", "upperCamel", "preserve"), default="upperCamel")
    parser.add_argument("--acronyms", choices=("preserve", "normalize"), default="preserve")
    parser.add_argument("--protect", action="append", default=[])
    parser.add_argument("--output")
    parser.add_argument("--apply-plan")
    parser.add_argument("--rollback")
    parser.add_argument("--journal")
    parser.add_argument("inputs", nargs="*")
    args = parser.parse_args()
    if args.rollback:
        rollback(Path(args.rollback))
        return 0
    if args.apply_plan:
        if not args.journal:
            parser.error("--apply-plan requires --journal")
        plan = json.loads(Path(args.apply_plan).read_text(encoding="utf-8"))
        apply_plan(plan, Path(args.journal))
        return 0
    if not args.inputs:
        parser.error("inventory requires at least one input")
    result = build_inventory(
        expand_inputs(args.inputs),
        args.case,
        {Path(path).resolve() for path in args.protect},
        args.acronyms,
    )
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0 if result["valid"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

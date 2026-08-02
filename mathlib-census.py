#!/usr/bin/env python3
"""Aggregate a mathlib census run (mathlib-census.sh): attempted vs SHIPPED
coverage (gate-rejected files ship identity — their code bytes are all
passthrough), the measured ceiling (policy-content excluded), gate-reject
classes, and the opt-out queue ranked by BYTES with bail reasons."""
import bisect
import json
import re
import sys
from collections import Counter
from pathlib import Path

res = Path(sys.argv[1])
clearances_path = Path(sys.argv[2]) if len(sys.argv) > 2 else None
att_a = att_v = shp_a = shp_v = pol_t = 0
nfiles = nrej = nerr = 0
rejects = []
kind_bytes = Counter()
kind_count = Counter()
why_bytes = Counter()
perfile = []

for out in sorted(res.glob("*.out")):
    err = out.with_suffix(".err")
    etext = err.read_text() if err.exists() else ""
    m = re.search(r"^(\d+) (\d+) (\d+) (\d+) (\S+)$", out.read_text(), re.M)
    if not m:
        nerr += 1
        continue
    a, v, _t, pol, path = int(m[1]), int(m[2]), int(m[3]), int(m[4]), m[5]
    nfiles += 1
    att_a += a; att_v += v; pol_t += pol
    gate = re.search(r"\[gate\]: not formatted: gate rejected output \((.*?)\)", etext)
    # the reparse-fail class has NO parenthesized tag (the standing grep law
    # — it hid three rejects across the whole campaign scoreboard)
    if not gate:
        gate = re.search(r"\[gate\]: not formatted: output (failed to reparse)", etext)
    if gate:
        nrej += 1
        rejects.append((path, gate[1]))
        shp_v += a + v
        cov = 0.0
    else:
        shp_a += a; shp_v += v
        cov = 100 * a / max(1, a + v)
    perfile.append((cov, path))
    for k, ln, why in re.findall(r"opt-out: (\S+) len=(\d+)(?: why=(\S+))?", etext):
        kind_bytes[k] += int(ln)
        kind_count[k] += 1
        if why:
            why_bytes[why] += int(ln)

code = att_a + att_v
portable = code - min(pol_t, code)
pct = lambda n, d: f"{100 * n / d:.1f}%" if d else "-"
print(f"files: {nfiles} parsed, {nerr} no-stats, {nrej} gate-rejected")
print(f"ATTEMPTED code-active: {pct(att_a, code)}")
print(f"SHIPPED   code-active: {pct(shp_a, code)}")
print(f"CEILING:   portable {pct(portable, code)} of code (policy {pol_t} bytes)")
print(f"           shipped-of-portable {pct(shp_a, portable)}   <- the campaign number")
print("\ngate rejects:")
for p, c in rejects:
    print(f"  {c:12} {p}")
print("\ncoverage distribution (shipped):")
edges = [0, 1, 25, 50, 70, 90, 101]
labels = ["0%", "1-25%", "25-50%", "50-70%", "70-90%", "90-100%"]
counts = [0] * 6
for c, _ in perfile:
    counts[min(5, bisect.bisect_right(edges, c) - 1)] += 1
for l, n in zip(labels, counts):
    print(f"  {l:>8}: {'#' * n} {n}")
print("\nworst files (shipped):")
for c, p in sorted(perfile)[:10]:
    print(f"  {c:5.1f}%  {p}")
print(f"\nopt-out queue by BYTES (top 25 of {len(kind_bytes)} kinds):")
for k, b in kind_bytes.most_common(25):
    print(f"  {b:8}  x{kind_count[k]:<5} {k}")
print(f"\nbail reasons by BYTES (top 15 of {len(why_bytes)}):")
for w, b in why_bytes.most_common(15):
    print(f"  {b:8}  {w}")

if clearances_path is not None:
    clearances = json.loads(clearances_path.read_text())
    failures = []
    minimum_coverage = float(clearances.get("minimum_shipped_of_portable", 0))
    coverage = 100 * shp_a / portable if portable else 0
    if coverage < minimum_coverage:
        failures.append(f"coverage {coverage:.3f} < {minimum_coverage:.3f}")
    maximum_rejects = int(clearances.get("maximum_gate_rejects", 0))
    if nrej > maximum_rejects:
        failures.append(f"gate rejects {nrej} > {maximum_rejects}")
    for kind, maximum in clearances.get("maximum_kind_bytes", {}).items():
        actual = kind_bytes[kind]
        if actual > int(maximum):
            failures.append(f"{kind} {actual} > {maximum}")
    print(f"\nclearances: {clearances_path}")
    if failures:
        for failure in failures:
            print(f"  FAIL {failure}")
        raise SystemExit(1)
    print("  PASS")

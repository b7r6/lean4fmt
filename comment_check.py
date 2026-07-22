#!/usr/bin/env python3
"""Comment-preservation check for a git worktree diff.

For each modified file, extract the multiset of comment texts (line comments
`-- ...` to EOL, block comments `/- ... -/` including doc `/-- -/`, nesting-aware)
from the HEAD version and the worktree version, and report any difference.
Whitespace inside comments is normalized (formatter may re-anchor indentation
of continuation lines). This is the companion check to the token gate, which
is comment-blind.
"""
import subprocess, sys, re

def extract_comments(src: str):
    out = []
    i, n = 0, len(src)
    in_str = False
    while i < n:
        c = src[i]
        if in_str:
            if c == '\\':
                i += 2; continue
            if c == '"':
                in_str = False
            i += 1; continue
        if c == '"':
            in_str = True; i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i)
            if j == -1: j = n
            out.append(src[i:j])
            i = j; continue
        if src.startswith('/-', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith('/-', j): depth += 1; j += 2
                elif src.startswith('-/', j): depth -= 1; j += 2
                else: j += 1
            out.append(src[i:j])
            i = j; continue
        i += 1
    # normalize interior whitespace so re-indentation isn't a false positive
    return sorted(re.sub(r'\s+', ' ', c).strip() for c in out)

files = subprocess.run(['git', 'diff', '--name-only'], capture_output=True, text=True).stdout.split()
bad = 0
for f in files:
    if not f.endswith('.lean'): continue
    old = subprocess.run(['git', 'show', f'HEAD:{f}'], capture_output=True, text=True).stdout
    new = open(f, encoding='utf-8').read()
    co, cn = extract_comments(old), extract_comments(new)
    if co != cn:
        bad += 1
        print(f'=== {f}')
        so, sn = set(co), set(cn)
        for c in sorted(so - sn): print(f'  LOST: {c[:120]}')
        for c in sorted(sn - so): print(f'  ADDED: {c[:120]}')
        if so == sn: print('  (multiset count difference only)')
print(f'--- {len(files)} files checked, {bad} with comment drift')

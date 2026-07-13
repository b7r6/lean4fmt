import random, sys
# parse-preserving-ish trivia mutations; invalid ones are filtered downstream
# by the spine comparison in the fuzz driver.
random.seed(int(sys.argv[2]))
lines = open(sys.argv[1]).read().split('\n')
out = []
in_block = False   # crude /- -/ and string guards
in_meta = False    # macro_rules/syntax/notation/elab quotations: CONTENT (pin)
import re
META = re.compile(r'^(@\[[^]]*\]\s*)?(local\s+|scoped\s+)*(macro_rules|macro\s|syntax\s|notation\s|elab\s|elab_rules)')
for ln in lines:
    s = ln
    if META.match(s): in_meta = True
    elif in_meta and s and not s[0].isspace() and not s.lstrip().startswith('|'):
        in_meta = False
    guard = ('"' in s) or ('/-' in s) or ('-/' in s) or in_block or in_meta \
        or s.lstrip().startswith('--') or ('|]' in s) or ('[' in s and '|' in s and ']' in s)
    if '/-' in s and '-/' not in s: in_block = True
    if '-/' in s: in_block = False
    r = random.random()
    if not guard and s.strip():
        if r < 0.15:
            s = s + ' ' * random.randint(1, 3)          # trailing spaces
        elif r < 0.30 and '  ' not in s.strip():
            toks = s.split(' ')
            if len(toks) > 3:
                i = random.randint(1, len(toks) - 2)
                if toks[i] and toks[i-1]:
                    toks[i] = ' ' + toks[i]              # double an inner gap
                s = ' '.join(toks)
    out.append(s)
    # blank INSERTION/removal between decls is a CONTENT mutation under the
    # blank-line pin (0-vs->=1 between one-liners is authorial) -- excluded.
    # Blank lines inside block comments are comment CONTENT -- excluded.
    # Extra blanks inside an existing blank run stay ws-perturbation:
    if not s.strip() and not in_block and random.random() < 0.2:
        out.append('')
print('\n'.join(out), end='')

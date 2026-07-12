import random, sys
# parse-preserving-ish trivia mutations; invalid ones are filtered downstream
# by the spine comparison in the fuzz driver.
random.seed(int(sys.argv[2]))
lines = open(sys.argv[1]).read().split('\n')
out = []
in_block = False  # crude /- -/ and string guards
for ln in lines:
    s = ln
    guard = ('"' in s) or ('/-' in s) or ('-/' in s) or in_block or s.lstrip().startswith('--')
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
    if not s.strip() and random.random() < 0.2:
        out.append('')                                    # extra blank line
    elif not guard and s.strip() and random.random() < 0.05:
        out.append('')                                    # inserted blank
print('\n'.join(out), end='')

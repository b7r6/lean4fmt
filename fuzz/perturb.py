import random, sys
# parse-preserving-ish trivia mutations; invalid ones are filtered downstream
# by the spine comparison in the fuzz driver.
random.seed(int(sys.argv[2]))
lines = open(sys.argv[1]).read().split('\n')
out = []
in_block = False   # crude /- -/ and string guards
blk_depth = 0      # block comments NEST; a line can hold both /- and -/ (e.g.
                   # a docstring QUOTING `/-- doc -/` inline) -- count, don't toggle
in_meta = False    # macro_rules/syntax/notation/elab quotations: CONTENT (pin)
in_tpl = False     # MULTI-LINE quasiquote templates [ident| ... |]: CONTENT (pin)
import re
META = re.compile(r'^(@\[[^]]*\]\s*)?(local\s+|scoped\s+)*(macro_rules|macro\s|syntax\s|notation\s|elab\s|elab_rules)')
TPL_OPEN = re.compile(r'\[[A-Za-z_][A-Za-z0-9_\.]*\|')
for ln in lines:
    s = ln
    if META.match(s): in_meta = True
    elif in_meta and s and not s[0].isspace() and not s.lstrip().startswith('|'):
        in_meta = False
    tpl_line = in_tpl
    if TPL_OPEN.search(s) and '|]' not in s:
        in_tpl = True
        tpl_line = True
    if '|]' in s:
        tpl_line = True   # the closing line is template content too
        in_tpl = False
    guard = ('"' in s) or ('/-' in s) or ('-/' in s) or in_block or in_meta or tpl_line \
        or s.lstrip().startswith('--') or ('|]' in s) or ('[' in s and '|' in s and ']' in s) \
        or ('`(' in s)   # quotation terms: interior is CONTENT (pin)
    blk_depth = max(0, blk_depth + s.count('/-') - s.count('-/'))
    in_block = blk_depth > 0
    r = random.random()
    if not guard and s.strip():
        if r < 0.15:
            s = s + ' ' * random.randint(1, 3)          # trailing spaces
        elif r < 0.30 and '  ' not in s.strip():
            # comment TEXT is content (pin): only mutate the code prefix
            cut = s.find(' --')
            code, tail = (s, '') if cut < 0 else (s[:cut], s[cut:])
            toks = code.split(' ')
            if len(toks) > 3:
                i = random.randint(1, len(toks) - 2)
                # the gap after `{` is CONTENT (column-aligned structInst
                # fields) -- the emitter's ws canon exempts it too
                if toks[i] and toks[i-1] and not toks[i-1].endswith('{'):
                    toks[i] = ' ' + toks[i]              # double an inner gap
                s = ' '.join(toks) + tail
    out.append(s)
    # blank INSERTION/removal between decls is a CONTENT mutation under the
    # blank-line pin (0-vs->=1 between one-liners is authorial) -- excluded.
    # Blank lines inside block comments are comment CONTENT -- excluded.
    # Extra blanks inside an existing blank run stay ws-perturbation:
    if not s.strip() and not in_block and random.random() < 0.2:
        out.append('')
print('\n'.join(out), end='')

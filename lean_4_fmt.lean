/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                  // LEAN4FMT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Library barrel. The v2 module tree (doc/design.md §11):

        Syntax/   trivia, kinds, queries        (L0)
        Doc/      the document IR + renderer     (L0/L1 core)
        Style/    the preset/override ontology   (L1)
        Emit/     Syntax → Doc walker            (L2)   [scaffold: verbatim]
        Rules/    lint diagnostics               (L2)
        Config/   .lean4fmt.lean discovery/load  (L3)
        Frontend/ parse + safety gate + session  (L3)
        Driver/   single-file + tree + io + pool (L4)
        Cli       argument surface               (L5)
        Emitter   the v1 prototype (current active formatter, behind the gate)

    The executable is `Main.lean`.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.syntax.kinds
import lean_4_fmt.syntax.trivia
import lean_4_fmt.syntax.query
import lean_4_fmt.doc
import lean_4_fmt.style
import lean_4_fmt.emit
import lean_4_fmt.rules
import lean_4_fmt.config
import lean_4_fmt.frontend
import lean_4_fmt.driver
import lean_4_fmt.cli
import lean_4_fmt.emitter
import lean_4_fmt.proofs

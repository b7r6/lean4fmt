/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                  // LEAN4FMT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Library barrel. The v2 module tree (DESIGN_V2 §11):

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

import Lean4Fmt.Syntax.Kinds
import Lean4Fmt.Syntax.Trivia
import Lean4Fmt.Syntax.Query
import Lean4Fmt.Doc
import Lean4Fmt.Style
import Lean4Fmt.Emit
import Lean4Fmt.Rules
import Lean4Fmt.Config
import Lean4Fmt.Frontend
import Lean4Fmt.Driver
import Lean4Fmt.Cli
import Lean4Fmt.Emitter
import Lean4Fmt.Proofs

/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // LEAN4FMT // CONFIG // LOAD
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Elaborate a `.lean4fmt.lean` config to a `StylePatch` (doc/design.md §7). Config
    is Lean source that evaluates to a `StylePatch`, so there is no config parser.
    SCAFFOLD: returns the empty patch until the config elaboration path lands.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import lean_4_fmt.style

namespace Lean4Fmt.Config

/-- Load a config file to a `StylePatch`. SCAFFOLD (no-op patch). -/
def load (_path : System.FilePath) : IO Lean4Fmt.Style.style_patch := pure {}

end Lean4Fmt.Config

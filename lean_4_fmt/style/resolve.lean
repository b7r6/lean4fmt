/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // LEAN4FMT // STYLE // RESOLVE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    resolve : Preset → List StylePatch → Style  (doc/design.md §7). Patches merged
    left-to-right (later wins).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.style.options
import lean_4_fmt.style.patch
import lean_4_fmt.style.preset

namespace Lean4Fmt.Style

/-- Resolve a base preset plus a precedence-ordered list of patches into the
    concrete `Style` the renderer reads. -/
def resolve (base : Style) (patches : List style_patch) : Style := patches.foldl Style.apply base

end Lean4Fmt.Style

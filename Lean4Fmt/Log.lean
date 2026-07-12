/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // LEAN4FMT // LOG
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Leveled diagnostic sink, PURE LEAN. Mirrors the StdlibEx.Logging surface
    (Level + setLevel + log) without the spdlog shim: log.cpp is compiled
    GNU-ABI (system g++/libstdc++) while Lean links libc++ — with both
    runtimes in one exe, exception unwinding through the elab fallback breaks
    (std::terminate; stdlibex decision VII names exactly this hazard). Until
    log.cpp compiles with Lean's clang, a formatter that runs the elaborator
    in-process cannot link it.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Lean4Fmt.Log

inductive Level where
  | trace | debug | info | warn | error
  deriving Repr, DecidableEq, Inhabited

def Level.rank : Level → Nat
  | .trace => 0 | .debug => 1 | .info => 2 | .warn => 3 | .error => 4

def Level.tag : Level → String
  | .trace => "trace" | .debug => "debug" | .info => "info"
  | .warn => "warning" | .error => "error"

def Level.ofString : String → Level
  | "trace" => .trace | "debug" => .debug | "info" => .info
  | "error" => .error | _ => .warn

initialize levelRef : IO.Ref Level ← IO.mkRef .warn

def setLevel (l : Level) : IO Unit := levelRef.set l

def log (l : Level) (msg : String) : IO Unit := do
  if l.rank ≥ (← levelRef.get).rank then
    (← IO.getStderr).putStrLn s!"[{l.tag}] {msg}"

end Lean4Fmt.Log

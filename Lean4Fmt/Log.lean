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

inductive level where
  | trace
  | debug
  | info
  | warn
  | error
  deriving Repr, DecidableEq, Inhabited

def level.rank : level → Nat
  | .trace => 0
  | .debug => 1
  | .info  => 2
  | .warn  => 3
  | .error => 4

def level.tag : level → String
  | .trace => "trace"
  | .debug => "debug"
  | .info  => "info"
  | .warn  => "warning"
  | .error => "error"

def level.of_string : String → level
  | "trace" => .trace
  | "debug" => .debug
  | "info"  => .info
  | "error" => .error
  | _       => .warn

initialize levelRef : IO.Ref level ← IO.mkRef .warn

def set_level (lineValue : level) : IO Unit := levelRef.set lineValue

def log (lineValue : level) (msg : String) : IO Unit := do
  if lineValue.rank ≥ (← levelRef.get).rank then
    (← IO.getStderr).putStrLn
      s!
          "[{lineValue.tag}] {msg}"

end Lean4Fmt.Log

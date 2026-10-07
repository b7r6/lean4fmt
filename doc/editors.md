# Editor integration

lean4fmt formats from stdin so it drops into any editor's format-on-save path:

```sh
lean4fmt --stdin [--stdin-path /abs/path/to/Buffer.lean] < buffer > formatted
```

- **stdin → stdout**, so it works on unsaved buffers.
- **`--stdin-path`** (optional) is the buffer's real path; it's used only to
  resolve style config (nearest `fmt.lean` / preset) and to label diagnostics —
  the bytes always come from stdin.
- **Identity fallback is guaranteed.** If the input can't be formatted (a parse
  error mid-edit, notation that needs elaboration without an env, any exception),
  lean4fmt echoes the original bytes and exits 0. An editor buffer is never
  emptied or corrupted — the worst case is "left unformatted".
- **Layout only.** `--stdin` never touches the rename axis; snake_case renaming
  stays a deliberate project pass (`--rename-apply`), never format-on-save.

## Latency and the `timeout` guard

Typical files format in well under a format-on-save budget. Two cases are slow:
pathological single lines (tens of thousands of chars on one line — generated
data tables) and files that need the elaborating frontend. Formatters below run
**asynchronously**, so a slow format lands late rather than freezing the editor —
but a `timeout` wrapper caps wasted work and falls back to identity:

```sh
#!/usr/bin/env bash
# lean4fmt-editor — format on stdin with a hard budget; identity on timeout.
exec timeout 2s lean4fmt --stdin "$@" || exec cat
```

Install that on `PATH` and point editors at `lean4fmt-editor` instead of
`lean4fmt` if you want the cap. (`--elab auto` is the default and is what lets
notation-heavy code format at all; keep it on.)

## Emacs

### apheleia (async format-on-save, recommended)

```elisp
(with-eval-after-load 'apheleia
  (add-to-list 'apheleia-formatters
               '(lean4fmt . ("lean4fmt" "--stdin" "--stdin-path" filepath)))
  (add-to-list 'apheleia-mode-alist '(lean4-mode . lean4fmt)))
(add-hook 'lean4-mode-hook #'apheleia-mode)
```

`filepath` is apheleia's symbol for the buffer's file; it becomes `--stdin-path`.

### reformatter.el (synchronous alternative)

```elisp
(reformatter-define lean4fmt
  :program "lean4fmt" :args '("--stdin"))
(add-hook 'lean4-mode-hook #'lean4fmt-on-save-mode)
```

## VS Code

The Lean 4 extension doesn't expose a custom formatter, so use the
**`jkillian.custom-local-formatters`** extension and add to `settings.json`:

```jsonc
{
  "customLocalFormatters.formatters": [
    { "command": "lean4fmt --stdin", "languages": ["lean4"] }
  ],
  "[lean4]": {
    "editor.defaultFormatter": "jkillian.custom-local-formatters",
    "editor.formatOnSave": true
  }
}
```

`custom-local-formatters` pipes the document through the command's stdin/stdout.

## Neovim

### conform.nvim (recommended)

```lua
require("conform").setup({
  formatters = {
    lean4fmt = { command = "lean4fmt", args = { "--stdin" }, stdin = true },
  },
  formatters_by_ft = { lean = { "lean4fmt" } },
  format_on_save = { timeout_ms = 2000, lsp_fallback = false },
})
```

### none-ls / null-ls (alternative)

Register a `formatting` source whose command is `lean4fmt` with `args = {"--stdin"}`
and `to_stdin = true`.

## Notes

- Formatting does not require a built project. `--elab auto` is best-effort: it
  formats notation-heavy code (e.g. mathlib) standalone, and anything it can't
  resolve falls back to identity rather than erroring.
- The rename/migration pass (`--rename-apply --rename-case snake`) is a separate,
  build-validated project operation — do not wire it to save.

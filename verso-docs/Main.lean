/-
SciLean Documentation Site Generator

Uses Verso's literate Lean feature for proper syntax highlighting.
-/
import VersoBlog
import SciLeanDocs
import SciLeanDocs.LitNN

open Verso Genre Blog Site Syntax
open Output Html Template Theme

-- Import literate Lean modules with proper syntax highlighting
-- Uses `set_option doc.verso true` for SubVerso highlighting
literate_page nnDocs from SciLeanDocs.LitNN in "." as "Neural Networks"

def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html>
        <head>
          <meta charset="utf-8"/>
          <meta name="viewport" content="width=device-width, initial-scale=1"/>
          <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/sakura.css/css/sakura.css" type="text/css"/>
          <title>{{ (← param (α := String) "title") }} " — SciLean"</title>
          {{← builtinHeader }}
          <style>
            "body { max-width: 900px; }"
            "pre { background: #f5f5f5; padding: 1em; border-radius: 8px; overflow-x: auto; }"
            "code { font-family: 'SF Mono', 'Consolas', monospace; }"
            "table { width: 100%; border-collapse: collapse; margin: 1em 0; }"
            "th, td { padding: 0.5em; border: 1px solid #ddd; text-align: left; }"
            "th { background: #f0f0f0; }"
            ".nav { display: flex; gap: 2em; margin: 1em 0; }"
            ".nav a { color: #1d4ed8; }"
            "h1 { color: #1e293b; }"
            ".hl.lean { background: #fafafa; border: 1px solid #e5e7eb; border-radius: 6px; padding: 0.5em 1em; }"
          </style>
        </head>
        <body>
          <header>
            <h1><a href="." style="text-decoration: none; color: inherit;">"SciLean"</a></h1>
            <div class="nav">
              {{ ← topNav }}
            </div>
          </header>
          <main>
            {{ (← param "content") }}
          </main>
          <footer style="margin-top: 3em; padding-top: 1em; border-top: 1px solid #ddd; color: #666;">
            <p>
              "Built with "
              <a href="https://github.com/leanprover/verso">"Verso"</a>
              " and "
              <a href="https://leanprover.github.io/">"Lean 4"</a>
            </p>
          </footer>
        </body>
      </html>
    }}
}

def scileanSite : Site := site SciLeanDocs.Front /
  static "static" ← "static"
  "nn" nnDocs

def main := blogMain theme scileanSite

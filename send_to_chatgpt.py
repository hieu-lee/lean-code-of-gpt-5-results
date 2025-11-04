#!/usr/bin/env python3
import argparse
import base64
import subprocess
import sys
import time
from pathlib import Path
from textwrap import dedent

PROMPT_TEMPLATE = """In our lean project, we have the following Axioms.lean file:

```
{file_content}
```

For each axiom, check if it appears/can be found in literature using web search tool and pdf reader tool to read the papers online, or can be trivially checked using a simple python script (if this's the case, check them by writing a script), remeber that if an axiom is true by checking using a script, it is NOT sus, then compile a list of sus axioms, called A, then return me a prompt (only this prompt should be in your reply) to copy paste into Codex, to ask it to:
- remove the wrong axioms or fully formalize the axioms (should be changed to theorems) that can't be found in literally, or non-trivial
- revise the project until `lake build` is successful"""

def read_file(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except Exception as e:
        print(f"Error reading {path}: {e}", file=sys.stderr)
        sys.exit(1)

def run_applescript(script: str) -> subprocess.CompletedProcess:
    # Feed the AppleScript via stdin so we don't have to escape everything.
    return subprocess.run(["osascript", "-"], input=script, text=True, capture_output=True)

def build_focus_js() -> str:
    # Small JS only to focus the composer; content will be pasted via clipboard.
    js = """
    (function() {
      let candidates = Array.from(document.querySelectorAll('textarea, div[contenteditable="true"]'));
      if (!candidates.length) return "no-composer";
      candidates.sort((a,b) => a.getBoundingClientRect().top - b.getBoundingClientRect().top);
      const el = candidates[candidates.length - 1];
      el.focus();
      if (el.select) { try { el.select(); } catch (e) {} }
      return "focused";
    })()
    """
    return " ".join(js.split())

def make_applescript(url: str, focus_js: str, send_js: str) -> str:
    # AppleScript that: opens Chrome, opens/activates a tab to the URL, focuses the composer via JS,
    # pastes clipboard, tries to click the Send button via JS, and falls back to Cmd+Enter if needed.
    js_focus_escaped = focus_js.replace("\\", "\\\\").replace('"', '\\"')
    js_send_escaped = send_js.replace("\\", "\\\\").replace('"', '\\"')
    return dedent(f'''
    on run
      set theURL to "{url}"
      tell application "Google Chrome"
        if (count of windows) = 0 then
          make new window
          delay 0.2
        end if
        activate
        -- Open URL in a fresh tab and select it robustly
        tell front window
          make new tab at end of tabs with properties {{URL:theURL}}
          set active tab index to (count of tabs)
        end tell
        -- Give the page a moment to render
        delay 2
        -- Focus the input via JS so paste goes to the right place
        tell active tab of front window
          set jsFocus to "{js_focus_escaped}"
          try
            set res to execute javascript jsFocus
          on error errMsg number errNum
            set res to "js-error"
          end try
        end tell
      end tell
      -- Paste from clipboard and press Enter
      tell application "System Events"
        delay 0.2
        keystroke "v" using {{command down}}
      end tell
      -- Try to send by clicking the button via JS first
      tell application "Google Chrome"
        tell active tab of front window
          set jsSend to "{js_send_escaped}"
          try
            set res2 to execute javascript jsSend
          on error errMsg2 number errNum2
            set res2 to "js-error"
          end try
        end tell
      end tell
      -- Fallback: if clicking failed, press Cmd+Enter
      if res2 is not "clicked-button" and res2 is not "submitted-form" and res2 is not "sent-keyboard" then
        tell application "System Events"
          delay 0.1
          keystroke return using {{command down}}
        end tell
      end if
    end run
    ''')

def set_clipboard(text: str) -> None:
    """Set macOS clipboard to given text, preferring pyperclip if installed."""
    try:
        import pyperclip  # type: ignore
        pyperclip.copy(text)
        return
    except Exception:
        pass
    # Fallback to pbcopy
    try:
        subprocess.run(["pbcopy"], input=text, text=True, check=True)
    except Exception as e:
        print(f"Failed to set clipboard: {e}", file=sys.stderr)
        sys.exit(1)

def main():
    ap = argparse.ArgumentParser(description="Open chatgpt.com in Chrome, insert a prompt, and send (macOS).")
    ap.add_argument("file", type=Path, help="Path to Axioms.lean (or any file)")
    ap.add_argument("--url", default="https://chatgpt.com/", help="Target URL (default: https://chatgpt.com/)")
    args = ap.parse_args()

    file_text = read_file(args.file)
    prompt = PROMPT_TEMPLATE.format(file_content=file_text)

    # Put prompt on clipboard to avoid huge AppleScript/JavaScript payloads.
    set_clipboard(prompt)

    # Tiny JS to focus the input, then we'll paste via System Events.
    js_focus = build_focus_js()
    # JS to find and click a visible Send button; falls back to form submit or keyboard events.
    def build_send_js() -> str:
        js = """
        (function() {
          function visible(el) {
            const r = el.getBoundingClientRect();
            const cs = getComputedStyle(el);
            return r.width > 0 && r.height > 0 && cs.visibility !== 'hidden' && cs.display !== 'none';
          }
          // Prefer explicit markers first
          let btn = document.querySelector('[data-testid="send-button"]');
          if (!btn) {
            const buttons = Array.from(document.querySelectorAll('button,[role="button"]'));
            btn = buttons.find(b => {
              const label = (b.getAttribute('aria-label') || '').toLowerCase();
              const text = (b.textContent || '').toLowerCase();
              return visible(b) && (label.includes('send prompt') || label.includes('send message') || label.includes('send') || /\bsend\b/.test(text));
            }) || null;
          }
          if (btn) { btn.click(); return 'clicked-button'; }

          // Fallback: submit nearest form
          const form = document.querySelector('form');
          if (form && typeof form.requestSubmit === 'function') { form.requestSubmit(); return 'submitted-form'; }

          // Last resort: synthesize Meta+Enter on the composer
          let comps = Array.from(document.querySelectorAll('textarea, div[contenteditable="true"]'));
          const el = comps.length ? comps[comps.length - 1] : null;
          if (el) {
            el.focus();
            const down = new KeyboardEvent('keydown', {key:'Enter',code:'Enter',keyCode:13,which:13,bubbles:true,metaKey:true});
            const up   = new KeyboardEvent('keyup',   {key:'Enter',code:'Enter',keyCode:13,which:13,bubbles:true,metaKey:true});
            el.dispatchEvent(down); el.dispatchEvent(up);
            return 'sent-keyboard';
          }
          return 'no-send-target';
        })()
        """
        return " ".join(js.split())

    js_send = build_send_js()
    ascript = make_applescript(args.url, js_focus, js_send)

    # First run will prompt macOS to let “Python” control Chrome; allow it.
    proc = run_applescript(ascript)
    if proc.returncode != 0:
        print(proc.stderr.strip() or "AppleScript failed.", file=sys.stderr)
        sys.exit(proc.returncode)

    # Optional: show JavaScript return status for debugging
    out = (proc.stdout or "").strip()
    if out:
        print(f"AppleScript output: {out}")
    print("Prompt pasted and sent (Cmd+Enter).")

if __name__ == "__main__":
    main()

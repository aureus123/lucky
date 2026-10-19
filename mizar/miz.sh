#!/bin/sh
# Usage: ./miz.sh ARTICLE   (e.g. ./miz.sh uprf)
# Accommodates and verifies text/ARTICLE.miz and lists the errors with their explanations.
# Requires the Mizar binaries (accom, verifier) on PATH and MIZFILES set to the Mizar
# shared directory (the one containing mml.vct and mizar.msg).
cd "$(dirname "$0")"
if [ -z "$MIZFILES" ] || ! command -v verifier > /dev/null; then
  echo "Set MIZFILES and put the Mizar binaries on PATH (see README.md)." >&2; exit 1
fi
a="text/$1"
rm -f "$a.err"
accom "$a.miz" > "text/$1.acc.log" 2>&1
if [ -s "$a.err" ]; then echo "ACCOMMODATOR ERRORS"; else verifier -q "$a.miz" > /dev/null 2>&1; fi
python3 - "$a" "$MIZFILES/mizar.msg" <<'PY'
import sys, re
a, msgf = sys.argv[1], sys.argv[2]
msgs, cur = {}, None
for l in open(msgf, encoding='latin-1'):
    m = re.match(r'# (\d+)$', l.strip())
    if m: cur = int(m.group(1)); continue
    if cur is not None and l.strip() and cur not in msgs: msgs[cur] = l.strip()
src = open(a + '.miz', encoding='latin-1').read().split('\n')
try: errs = [tuple(map(int, l.split())) for l in open(a + '.err') if l.strip()]
except FileNotFoundError: errs = []
for ln, col, code in errs:
    print(f"{ln}:{col}: *{code} {msgs.get(code, '')}\n    {src[ln-1].strip() if ln-1 < len(src) else ''}")
print(f"ERRORS: {len(errs)}" if errs else f"OK: {a} verified")
PY
# keep only the sources (and the .err file when there are errors)
find text -name "$1.*" ! -name "$1.miz" ! -name "$1.err" -delete
[ -s "$a.err" ] || rm -f "$a.err"

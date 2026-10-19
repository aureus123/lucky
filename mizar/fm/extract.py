#!/usr/bin/env python3
"""Split the Mizar article into top-level items (no proofs)."""
import re, sys, json

KW_END_DEF = re.compile(r'^\s*(coherence|consistency|existence|uniqueness|symmetry|irreflexivity|reflexivity|asymmetry|projectivity|involutiveness|idempotence|commutativity|compatibility)\b')

# proofs up to this many lines get "The theorem is a consequence of ..."
PROOF_LINES = 12


def cited(text):
    """the labels cited with 'by' or 'from', in order, without repetitions"""
    out = []
    for m in re.finditer(r'\b(?:by|from)\s+([^;]*)', text):
        for r in re.split(r'\s*,\s*', m.group(1)):
            r = re.sub(r'\(.*', '', r).strip()
            if re.fullmatch(r'\w+', r) and r not in out:
                out.append(r)
    return out


def strip_comment(line):
    i = line.find('::')
    return line if i < 0 else line[:i]

def items(path):
    text = open(path, encoding='latin-1').read()
    body = text.split('\nbegin\n', 1)[1]
    lines = body.split('\n')
    out = []
    i = 0
    n = len(lines)
    def skip_block(i):
        """skip a 'proof ... end;' block starting at line i (which contains proof)"""
        depth = 0
        while i < n:
            l = strip_comment(lines[i])
            for w in re.findall(r'\b(proof|now|hereby|case|suppose|per|end)\b', l):
                if w in ('proof', 'now', 'hereby'):
                    depth += 1
                elif w in ('case', 'suppose'):
                    depth += 1
                elif w == 'end':
                    depth -= 1
            i += 1
            if depth <= 0:
                return i
        return i
    while i < n:
        raw = lines[i]
        s = raw.strip()
        if s.startswith('::'):
            com = []
            while i < n and lines[i].strip().startswith('::'):
                com.append(lines[i].strip()[2:].strip()); i += 1
            out.append({'kind': 'comment', 'text': ' '.join(com)})
            continue
        if not s:
            i += 1; continue
        m = re.match(r'reserve\s+(.*)', s)
        if m:
            txt = s
            while not txt.rstrip().endswith(';'):
                i += 1; txt += ' ' + lines[i].strip()
            out.append({'kind': 'reserve', 'text': txt[len('reserve'):].strip().rstrip(';')})
            i += 1; continue
        if s.startswith('theorem'):
            m = re.match(r'theorem\s*(\w*)\s*:?\s*(.*)', s)
            label = m.group(1)
            stmt = [m.group(2)]
            refs = []
            i += 1
            while True:
                l = strip_comment(lines[i]).strip()
                if l == 'proof' or l.startswith('proof'):
                    j = skip_block(i)
                    if j - i <= PROOF_LINES:
                        refs = cited(' '.join(strip_comment(x)
                                              for x in lines[i:j]))
                    i = j; break
                if re.search(r'\bby\b', l) and l.endswith(';'):
                    refs = cited(l)
                    stmt.append(re.split(r'\bby\b', l)[0]); i += 1; break
                if l.endswith(';'):
                    stmt.append(l[:-1]); i += 1; break
                stmt.append(l); i += 1
            st = ' '.join(x for x in stmt if x).strip()
            st = re.sub(r'\s+by\s+.*$', '', st)
            out.append({'kind': 'theorem', 'label': label, 'text': st,
                        'refs': refs})
            continue
        if s.startswith('scheme'):
            head = [s]; i += 1
            while not strip_comment(lines[i]).strip().startswith('proof'):
                head.append(strip_comment(lines[i]).strip()); i += 1
            i = skip_block(i)
            out.append({'kind': 'scheme', 'text': ' '.join(head)})
            continue
        if s in ('definition', 'registration'):
            kind = s; i += 1
            blk = []
            depth = 1
            while i < n:
                l = strip_comment(lines[i]).strip()
                if l == 'end;' and depth == 1:
                    i += 1; break
                if re.match(r'^(proof|now)\b', l) or l.endswith(' proof') or l == 'proof':
                    i = skip_block(i); continue
                blk.append(l); i += 1
            out.append({'kind': kind, 'lines': blk})
            continue
        i += 1
    return out

if __name__ == '__main__':
    json.dump(items(sys.argv[1]), sys.stdout, indent=1)

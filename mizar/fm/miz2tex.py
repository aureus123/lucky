#!/usr/bin/env python3
"""Translate the definitions and theorems of ../text/acn.miz into LaTeX in the
style of Formalized Mathematics (statements only, no proofs).

Usage: python3 miz2tex.py ../text/acn.miz > body.tex
"""
import re
import sys

from extract import items

# ---------------------------------------------------------------- tokenizer

TOKEN_RE = re.compile(r"""
    (?P<ws>\s+)
  | (?P<sym>\[\#\]|\[:|:\]|\[/|\\\]|\.:|\|\^|\\/|/\\|-'|c=|<=|>=|<>|-labeling)
  | (?P<word>one-to-one|natural-valued|[A-Za-z_][A-Za-z0-9_#]*)
  | (?P<num>\d+)
  | (?P<one>[()\[\]{},.|&=<>+\-*/\\:;])
""", re.X)


def tokenize(s):
    toks = []
    pos = 0
    while pos < len(s):
        m = TOKEN_RE.match(s, pos)
        if not m:
            raise SyntaxError('cannot tokenize at: ' + s[pos:pos + 30])
        pos = m.end()
        if m.lastgroup != 'ws':
            toks.append(m.group(m.lastgroup))
    return toks


# ---------------------------------------------------------------- AST
# terms:    ('id', name) ('num', n) ('paren', t) ('bin', op, a, b)
#           ('app', fname, [args]) ('pre', fname, t) ('dot', f, x)
#           ('restr', f, J) ('img', R, X) ('pair', a, b) ('prod', a, b)
#           ('set', [elems]) ('ceil', t) ('the', field, t) ('infty',)
# formulas: ('pred', op, [lhs], [rhs])  ('is', t, [attrs], neg)
#           ('and', [f]) ('or', [f]) ('not', f) ('imp', a, b) ('iff', a, b)
#           ('for', segs, cond, body) ('ex', segs, cond) ('fparen', f)
# types:    ('type', [adjs], radix, [args])

PREFIX = {'Nb', 'deg', 'eta', 'card', 'Seg', 'cmBound', 'Sizes', 'KRel',
          'CycRel', 'WRel', 'maxdeg', 'chromatic#', 'dom', 'len', 'inf'}
FUNCS = {'SumN', 'cdiv', 'csucc', 'cpred', 'ksq', 'ksu', 'ksa', 'ksv', 'sseq',
         'PSum', 'eta_t', 'NumSet', 'max', 'In', 'Sum'}
ADJS = {'non', 'empty', 'finite', 'strict', 'natural-valued', 'irreflexive',
        'symmetric', 'one-to-one'}
RADIX_OF = {'Element', 'Subset', 'Function', 'Relation', 'FinSequence',
            'Clique', 'RedSequence'}
RADIX = {'Nat', 'object', 'set', 'Graph', 'RelStr', 'ExtReal', 'Real',
         'Function', 'Relation', 'FinSequence'} | RADIX_OF
TERM_STOP = {'st', 'holds', 'for', 'ex', 'implies', 'iff', 'or', '&', 'not',
             'is', 'in', 'c=', '=', '<>', '<', '<=', '>', '>=', 'misses',
             'meets', 'are_adjacent', 'are_true_twins', ')', ',', ']', '}',
             ':]', '\\]', 'being', 'if', 'otherwise', 'where', ':', ';',
             'means', 'equals', 'be', '-labeling'}
PREDS = {'=', '<>', '<', '<=', '>', '>=', 'in', 'c=', 'misses', 'meets'}


class Parser:
    def __init__(self, s):
        self.t = tokenize(s)
        self.i = 0

    def peek(self, k=0):
        j = self.i + k
        return self.t[j] if j < len(self.t) else None

    def next(self):
        tok = self.t[self.i]
        self.i += 1
        return tok

    def expect(self, tok):
        if self.peek() != tok:
            raise SyntaxError('expected %r at %r' % (tok, self.t[self.i:self.i + 8]))
        self.i += 1

    def at_end(self):
        return self.i >= len(self.t)

    # ---------------- types
    def parse_type(self):
        adjs = []
        while self.peek() in ADJS:
            adjs.append(self.next())
        radix = self.next()
        args = []
        if radix in RADIX_OF and self.peek() == 'of':
            self.next()
            args.append(self.parse_term())
            if radix == 'Function' and self.peek() == ',':
                self.next()
                args.append(self.parse_term())
        return ('type', adjs, radix, args)

    # ---------------- variable segments: x,y being T, z st ...
    def parse_segs(self):
        segs = []
        while True:
            names = [self.next()]
            while self.peek() == ',' and self.peek(2) in (',', 'being', 'be',
                                                          'is', 'st', 'holds',
                                                          'for', 'ex', None):
                # a further name of the same segment
                self.next()
                names.append(self.next())
            typ = None
            if self.peek() in ('being', 'be', 'is'):
                self.next()
                typ = self.parse_type()
            segs.append((names, typ))
            if self.peek() == ',':
                self.next()
                continue
            return segs

    # ---------------- formulas
    def parse_formula(self):
        a = self.parse_or()
        if self.peek() == 'implies':
            self.next()
            return ('imp', a, self.parse_formula())
        if self.peek() == 'iff':
            self.next()
            return ('iff', a, self.parse_formula())
        return a

    def parse_or(self):
        fs = [self.parse_and()]
        while self.peek() == 'or':
            self.next()
            fs.append(self.parse_and())
        return fs[0] if len(fs) == 1 else ('or', fs)

    def parse_and(self):
        fs = [self.parse_neg()]
        while self.peek() == '&':
            self.next()
            fs.append(self.parse_neg())
        return fs[0] if len(fs) == 1 else ('and', fs)

    def parse_neg(self):
        tok = self.peek()
        if tok == 'not':
            self.next()
            return ('not', self.parse_neg())
        if tok == 'for':
            self.next()
            segs = self.parse_segs()
            cond = None
            if self.peek() == 'st':
                self.next()
                cond = self.parse_formula()
            if self.peek() == 'holds':
                self.next()
                body = self.parse_formula()
            else:  # for x ex y ..., for x for y ...
                body = self.parse_formula()
            return ('for', segs, cond, body)
        if tok == 'ex':
            self.next()
            segs = self.parse_segs()
            self.expect('st')
            return ('ex', segs, self.parse_formula())
        return self.parse_atom()

    def parse_atom(self):
        if self.peek() == '(':
            save = self.i
            try:
                return self.parse_pred_atom()
            except SyntaxError:
                self.i = save
            self.next()
            f = self.parse_formula()
            self.expect(')')
            return ('fparen', f)
        return self.parse_pred_atom()

    def parse_pred_atom(self):
        lhs = [self.parse_term()]
        while self.peek() == ',':
            self.next()
            lhs.append(self.parse_term())
        op = self.peek()
        if op in PREDS:
            self.next()
            return ('pred', op, lhs, [self.parse_term()])
        if op in ('are_adjacent', 'are_true_twins'):
            self.next()
            return ('pred', op, lhs, [])
        if op and op.startswith('is_'):
            self.next()
            rhs = [self.parse_term()]
            while self.peek() == ',':
                self.next()
                rhs.append(self.parse_term())
            return ('pred', op, lhs, rhs)
        if op == 'is' and self.peek(1) in RADIX | ADJS - {'finite', 'one-to-one',
                                                         'natural-valued',
                                                         'empty'}:
            self.next()
            return ('istype', lhs[0], self.parse_type())
        if op == 'is':
            self.next()
            neg = False
            attrs = []
            while True:
                tok = self.peek()
                if tok == 'non':
                    self.next()
                    attrs.append(('non', self.next()))
                elif tok == '(' or (tok and self.peek(1) == '-labeling'):
                    if tok == '(':
                        self.next()
                        p = self.parse_term()
                        self.expect(')')
                    else:
                        p = self.parse_primary()
                    self.expect('-labeling')
                    attrs.append(('labeling', p))
                elif tok in ('additive', 'acyclic', 'odd', 'even', 'finite',
                             'one-to-one', 'natural-valued', 'empty'):
                    self.next()
                    attrs.append(('attr', tok))
                else:
                    break
            if not attrs:
                raise SyntaxError('no attribute at %r' % self.t[self.i:self.i + 5])
            return ('is', lhs[0], attrs, neg)
        raise SyntaxError('no predicate at %r' % self.t[self.i:self.i + 8])

    # ---------------- terms
    def parse_term(self):
        a = self.parse_add()
        while self.peek() in ('\\/', '/\\', '\\'):
            op = self.next()
            a = ('bin', op, a, self.parse_add())
        return a

    def parse_add(self):
        a = self.parse_mul()
        while self.peek() in ('+', '-', "-'"):
            op = self.next()
            a = ('bin', op, a, self.parse_mul())
        return a

    def parse_mul(self):
        a = self.parse_pow()
        while self.peek() in ('*', '/', 'div', 'mod'):
            op = self.next()
            a = ('bin', op, a, self.parse_pow())
        return a

    def parse_pow(self):
        a = self.parse_prefix()
        if self.peek() == '|^':
            self.next()
            a = ('bin', '|^', a, self.parse_prefix())
        return a

    def parse_prefix(self):
        tok = self.peek()
        if tok in PREFIX and self.peek(1) not in TERM_STOP | {None}:
            self.next()
            return ('pre', tok, self.parse_prefix())
        if tok == 'the':
            self.next()
            field = self.next()
            self.expect('of')
            return ('the', field, self.parse_prefix())
        if tok == 'bool':
            self.next()
            return ('pre', 'bool', self.parse_prefix())
        if tok == '[#]':
            self.next()
            return self.parse_prefix()
        return self.parse_postfix()

    def parse_postfix(self):
        a = self.parse_primary()
        while True:
            tok = self.peek()
            if tok == '.':
                self.next()
                a = ('dot', a, self.parse_primary())
            elif tok == '.:':
                self.next()
                a = ('img', a, self.parse_primary())
            elif tok == '|':
                self.next()
                a = ('restr', a, self.parse_prefix())
            else:
                return a

    def parse_primary(self):
        tok = self.next()
        if tok == '(':
            t = self.parse_term()
            self.expect(')')
            return ('paren', t)
        if tok == '[:':
            a = self.parse_term()
            self.expect(',')
            b = self.parse_term()
            self.expect(':]')
            return ('prod', a, b)
        if tok == '[':
            a = self.parse_term()
            self.expect(',')
            b = self.parse_term()
            self.expect(']')
            return ('pair', a, b)
        if tok == '[/':
            a = self.parse_term()
            self.expect('\\]')
            return ('ceil', a)
        if tok == '{':
            elems = []
            if self.peek() != '}':
                elems.append(self.parse_term())
                if self.peek() == 'where':
                    self.next()
                    segs = self.parse_segs()
                    self.expect(':')
                    f = self.parse_formula()
                    self.expect('}')
                    return ('compr', elems[0], segs, f)
                while self.peek() == ',':
                    self.next()
                    elems.append(self.parse_term())
            self.expect('}')
            return ('set', elems)
        if tok == '+' and self.peek() == 'infty':
            self.next()
            return ('infty',)
        if tok in FUNCS and self.peek() == '(':
            self.next()
            args = [self.parse_term()]
            while self.peek() == ',':
                self.next()
                args.append(self.parse_term())
            self.expect(')')
            return ('app', tok, args)
        if re.fullmatch(r'\d+', tok):
            return ('num', tok)
        if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_#]*', tok) and tok not in TERM_STOP:
            return ('id', tok)
        raise SyntaxError('unexpected %r' % tok)


# ---------------------------------------------------------------- rendering

SPECIAL_IDS = {'fu': 'f_u', 'fv': 'f_v', 'qF': 'q_F', 'qL': 'q_L',
               'Ri': 'R_i', 'NAT': r'\mathbb{N}', 'it': r'\mathit{it}',
               'pm': r'p_m'}


def r_id(name):
    if name in SPECIAL_IDS:
        return SPECIAL_IDS[name]
    m = re.fullmatch(r'([A-Za-z])(\d+)', name)
    if m:
        return '%s_{%s}' % (m.group(1), m.group(2))
    if len(name) == 1:
        return name
    return r'\mathit{%s}' % name


def unparen(t):
    return t[1] if t[0] == 'paren' else t


def atomic(t):
    return t[0] in ('id', 'num', 'paren', 'app', 'pair', 'set', 'ceil',
                    'infty', 'prod') or (t[0] == 'pre' and t[1] in
                                         ('Nb', 'eta', 'chromatic#', 'maxdeg',
                                          'KRel', 'CycRel', 'WRel', 'card'))


def rt(t):
    """render a term as LaTeX math"""
    k = t[0]
    if k == 'id':
        return r_id(t[1])
    if k == 'num':
        return t[1]
    if k == 'infty':
        return r'+\infty'
    if k == 'paren':
        return '(%s)' % rt(t[1])
    if k == 'bin':
        op, a, b = t[1], t[2], t[3]
        if op == '|^':
            return '{%s}^{%s}' % (rt(a), rt(unparen(b)))
        if op == '/':
            return '%s/%s' % (rt(a), rt(b))
        sym = {'+': '+', '-': '-', "-'": r'\mathbin{\dot{-}}', '*': r'\cdot ',
               'div': r'\mskip4mu\mathrm{div}\mskip4mu', 'mod': r'\bmod',
               '\\/': r'\cup', '/\\': r'\cap', '\\': r'\setminus'}[op]
        return '%s %s %s' % (rt(a), sym, rt(b))
    if k == 'pre':
        f, a = t[1], t[2]
        ua = unparen(a)
        if f == 'Nb':
            return 'N(%s)' % rt(ua)
        if f == 'deg':
            return r'\deg %s' % rt(a) if atomic(a) else r'\deg(%s)' % rt(ua)
        if f == 'eta':
            return r'\eta(%s)' % rt(ua)
        if f == 'chromatic#':
            return r'\chi(%s)' % rt(ua)
        if f == 'maxdeg':
            return r'\Delta(%s)' % rt(ua)
        if f == 'card':
            return r'\overline{\overline{%s}}' % rt(ua)
        if f == 'KRel':
            return 'K_{%s}' % rt(ua)
        if f == 'CycRel':
            return 'C_{%s}' % rt(ua)
        if f == 'WRel':
            return 'W_{%s}' % rt(ua)
        if f == 'bool':
            return '2^{%s}' % rt(ua)
        if f == 'inf':
            return r'\inf %s' % rt(a)
        name = {'Seg': r'\mathrm{Seg}', 'dom': r'\mathrm{dom}',
                'len': r'\mathrm{len}', 'cmBound': r'\mathrm{bound}',
                'Sizes': r'\mathrm{sizes}'}[f]
        if atomic(a):
            return r'%s\,%s' % (name, rt(a))
        return r'%s(%s)' % (name, rt(ua))
    if k == 'the':
        field, a = t[1], t[2]
        sub = rt(unparen(a))
        if field == 'carrier':
            return r'\Omega_{%s}' % sub
        if field == 'InternalRel':
            return r'E_{%s}' % sub
        return r'\mathrm{the\ %s\ of\ }%s' % (field, sub)
    if k == 'dot':
        return '%s(%s)' % (rt(t[1]), rt(unparen(t[2])))
    if k == 'restr':
        return r'%s{\restriction}%s' % (rt(t[1]), rt(t[2]))
    if k == 'img':
        return r'%s^{\circ}%s' % (rt(t[1]), rt(t[2]))
    if k == 'pair':
        return r'\langle %s, %s\rangle' % (rt(t[1]), rt(t[2]))
    if k == 'prod':
        return r'%s \times %s' % tuple(
            rt(x) if atomic(x) or x[0] in ('img', 'pre') else '(%s)' % rt(x)
            for x in t[1:3])
    if k == 'set':
        if not t[1]:
            return r'\emptyset'
        return r'\{%s\}' % ', '.join(rt(e) for e in t[1])
    if k == 'ceil':
        return r'\lceil %s\rceil' % rt(t[1])
    if k == 'compr':
        segs = t[2]
        if (len(segs) == 1 and segs[0][0] == [t[1][1]] and
                segs[0][1] in (('type', [], 'Nat', []),
                               ('type', [], 'Element', [('id', 'NAT')]))):
            return r'\{%s \in \mathbb{N} :$ %s$\}' % (rt(t[1]), rf(t[3]))
        return r'\{%s :$ %s, where %s$\}' % (
            rt(t[1]), rf(t[3]), seg_phrase(t[2], 'ex'))
    if k == 'app':
        f, args = t[1], [rt(unparen(a)) for a in t[2]]
        if f == 'SumN':
            return '%s(N(%s))' % (args[0], args[1])
        if f == 'Sum':
            return r'\textstyle\sum(%s)' % args[0]
        if f == 'cdiv':
            return r'\left\lceil\frac{%s}{%s}\right\rceil' % (args[0], args[1])
        if f == 'csucc':
            return r'\mathrm{succ}_{%s}(%s)' % (args[0], args[1])
        if f == 'cpred':
            return r'\mathrm{pred}_{%s}(%s)' % (args[0], args[1])
        if f == 'eta_t':
            return r'\eta_t(%s)' % ', '.join(args)
        if f == 'PSum':
            return r'%s(%s(%s))' % (args[0], args[1], args[2])
        if f == 'sseq':
            return r'\mathrm{s}(%s, %s)' % (args[0], args[1])
        if f == 'max':
            return r'\max(%s)' % ', '.join(args)
        if f in ('ksq', 'ksu', 'ksa', 'ksv'):
            name = {'ksq': r'\mathfrak{q}', 'ksu': r'\mathrm{ku}',
                    'ksa': r'\mathrm{ka}', 'ksv': r'\mathrm{kv}'}[f]
            return r'%s_{%s}(%s)' % (name, args[0], args[1])
        name = {'NumSet': r'\mathrm{Num}', 'In': r'\mathrm{In}'}[f]
        return r'%s(%s)' % (name, ', '.join(args))
    raise ValueError(t)


def m(s):
    return '$%s$' % s


# ---- types

def article(phrase):
    return ('an ' if phrase.lstrip('\\{$')[:1].lower() in 'aeiou' else 'a ') + phrase


def rtype2(ty, plural=False):
    """(head, tail): the variables go between them, as in 'element v of G'"""
    _, adjs, radix, args = ty
    pl = plural
    a = ['non empty' if x == 'non' else x for x in adjs]
    a = ' '.join(a).replace('non empty empty', 'non empty')
    nouns = {
        'Nat': ('natural number', 'natural numbers'),
        'object': ('object', 'objects'),
        'set': ('set', 'sets'),
        'Graph': ('graph', 'graphs'),
        'RelStr': ('relational structure', 'relational structures'),
        'ExtReal': ('extended real', 'extended reals'),
        'Real': ('real number', 'real numbers'),
    }
    tail = ''
    if radix in nouns:
        noun = nouns[radix][1 if pl else 0]
    elif radix == 'Element':
        noun = 'elements' if pl else 'element'
        tail = ' of ' + m(rt(args[0]))
    elif radix == 'Subset':
        noun = 'subsets' if pl else 'subset'
        tail = ' of ' + m(rt(args[0]))
    elif radix == 'Function':
        noun = 'functions' if pl else 'function'
        if args:
            tail = ' from %s into %s' % (m(rt(args[0])), m(rt(args[1])))
    elif radix == 'Relation':
        noun = 'relations' if pl else 'relation'
        if args:
            tail = ' on ' + m(rt(args[0]))
    elif radix == 'FinSequence':
        noun = 'finite sequences' if pl else 'finite sequence'
        if args:
            tail = ' of ' + m(rt(args[0]))
    elif radix == 'Clique':
        noun = 'cliques' if pl else 'clique'
        tail = ' of ' + m(rt(args[0]))
    elif radix == 'RedSequence':
        noun = 'reduction sequences' if pl else 'reduction sequence'
        tail = ' of ' + m(rt(args[0]))
    else:
        noun = radix
    return (a + ' ' + noun).strip(), tail


def rtype(ty, plural=False):
    h, t = rtype2(ty, plural)
    return h + t


def typed_vars(names, ty, art=False):
    """'element $v$ of $G$', 'natural numbers $i$, $j$'"""
    vs = ', '.join(m(r_id(n)) for n in names)
    if ty is None:
        return vs
    h, t = rtype2(ty, len(names) > 1)
    if art and len(names) == 1:
        h = article(h)
    return '%s %s%s' % (h, vs, t)


class Ctx:
    """reserved variables"""
    def __init__(self):
        self.res = {}
        self.iff = 'iff'      # 'if and only if' in theorems, as in FM


CTX = Ctx()


def seg_phrase(segs, quant):
    """'every natural number $i$ and every $f$', 'a natural number $k$ and $f$'"""
    parts = []
    for names, ty in segs:
        if quant == 'every':
            parts.append(('every ' if ty is not None else '') +
                         typed_vars(names, ty))
        else:
            parts.append(typed_vars(names, ty, art=True))
    return ' and '.join(parts)


def rf(f, top=False):
    """render a formula as text with inline math"""
    k = f[0]
    if k == 'fparen':
        return '(%s)' % rf(f[1])
    if k == 'and':
        return ' and '.join(rf(x) for x in f[1])
    if k == 'or':
        return ' or '.join(rf(x) for x in f[1])
    if k == 'imp':
        return 'if %s, then %s' % (rf(f[1]), rf(f[2]))
    if k == 'iff':
        return '%s %s %s' % (rf(f[1]), CTX.iff, rf(f[2]))
    if k == 'not':
        return rneg(f[1])
    if k == 'for':
        s = 'for ' + seg_phrase(f[1], 'every')
        if f[1][0][1] is None:
            s = 'for every ' + seg_phrase(f[1], 'every')
        if f[2] is not None:
            s += ' such that ' + rf(f[2])
        return s + ' holds ' + rf(f[3])
    if k == 'ex':
        names = sum(len(n) for n, _ in f[1])
        verb = 'there exist ' if names > 1 else 'there exists '
        ph = seg_phrase(f[1], 'ex')
        return verb + ph + ' such that ' + rf(f[2])
    if k == 'pred':
        return rpred(f)
    if k == 'is':
        return ris(f, False)
    if k == 'istype':
        return '%s is %s' % (m(rt(f[1])), article(rtype(f[2])))
    raise ValueError(f)


def ris(f, neg):
    t, attrs = f[1], f[2]
    words = []
    for a in attrs:
        if a[0] == 'labeling':
            words.append(m(rt(unparen(a[1]))) + '-labeling')
        elif a[0] == 'non':
            words.append('non ' + a[1])
        else:
            words.append(a[1])
    if len(words) > 1:
        ws = ', '.join(words[:-1]) + ' and ' + words[-1]
    else:
        ws = words[0]
    return '%s is %s%s' % (m(rt(t)), 'not ' if neg else '', ws)


PRED_TEXT = {
    'is_orientation_of': ('is an orientation of', None),
    'is_topological_for': ('is topological for', None),
    'is_cm_of': ('is a complete multipartition of', None),
    'is_monotone_for': ('is monotone for', None),
    'is_join_of': ('is a join of', 'and'),
    'is_path_of': ('is a path of order', None),
    'is_cycle_of': ('is a cycle of order', None),
    'is_split_by': ('is split by', 'and'),
    'is_thin_spider_of': ('is a thin spider of order', None),
    'is_thick_spider_of': ('is a thick spider of order', None),
}


def rpred(f, neg=False):
    op, lhs, rhs = f[1], f[2], f[3]
    L = [rt(x) for x in lhs]
    R = [rt(x) for x in rhs]
    if op in ('=', '<>', '<', '<=', '>', '>=', 'in', 'c='):
        sym = {'=': '=', '<>': r'\neq', '<': '<', '<=': r'\leq', '>': '>',
               '>=': r'\geq', 'in': r'\in', 'c=': r'\subseteq'}[op]
        if neg:
            sym = {'=': r'\neq', r'\neq': '=', '<': r'\geq', r'\leq': '>',
                   '>': r'\leq', r'\geq': '<', r'\in': r'\notin',
                   r'\subseteq': r'\not\subseteq'}[sym]
        return m('%s %s %s' % (L[0], sym, R[0]))
    if op in ('misses', 'meets'):
        if neg:
            op = {'misses': 'meets', 'meets': 'misses'}[op]
        return '%s %s %s' % (m(L[0]), op, m(R[0]))
    if op == 'are_adjacent':
        return '%s and %s are %sadjacent' % (m(L[0]), m(L[1]),
                                             'not ' if neg else '')
    if op == 'are_true_twins':
        return '%s and %s are %strue twins' % (m(L[0]), m(L[1]),
                                               'not ' if neg else '')
    notw = 'not ' if neg else ''
    if op == 'is_copies_of':
        return '%s is %s%s copies of %s' % (m(L[0]), notw, m(R[0]),
                                            m('K_{%s}' % R[1]))
    if op == 'is_sun_of':
        return '%s is %sthe sun of order %s on %s with base %s' % (
            m(L[0]), notw, m(R[0]), m(R[1]), m(R[2]))
    words, conj = PRED_TEXT[op]
    if neg:
        words = words.replace('is ', 'is not ', 1)
    if conj:
        rr = (' %s ' % conj).join(m(x) for x in R)
    else:
        rr = ', '.join(m(x) for x in R)
    return '%s %s %s' % (m(L[0]), words, rr)


def rneg(f):
    k = f[0]
    if k == 'pred':
        return rpred(f, neg=True)
    if k == 'is':
        return ris(f, True)
    if k == 'fparen':
        return 'not ' + rf(f)
    return 'not ' + rf(f)


def render_theorem(f):
    """'Let us consider ... Suppose ... Then ...' style"""
    segs = []
    conds = []
    body = f
    while body[0] == 'for' and (body[2] is not None or body[3][0] in ('for', 'imp')
                                or True):
        segs.extend(body[1])
        if body[2] is not None:
            conds.append(body[2])
        body = body[3]
        if body[0] != 'for':
            break
    if segs and body[0] == 'imp':
        conds.append(body[1])
        body = body[2]
    out = ''
    if segs:
        parts = []
        for names, ty in segs:
            parts.append(typed_vars(names, ty, art=True))
        if len(parts) > 1:
            out += 'Let us consider %s, and %s. ' % (', '.join(parts[:-1]), parts[-1])
        else:
            out += 'Let us consider %s. ' % parts[0]
        if conds:
            out += 'Suppose %s. ' % ' and '.join(rf(c) for c in conds)
        out += 'Then ' + render_concl(body) + '.'
        return out
    if body[0] == 'imp':
        return 'If %s, then %s.' % (rf(body[1]), render_concl(body[2]))
    s = render_concl(body)
    if s.startswith('('):
        return '(' + s[1].upper() + s[2:] + '.'
    if s.startswith('$') or s.startswith('\\'):
        return s + '.'
    return s[0].upper() + s[1:] + '.'


def render_concl(f):
    if f[0] == 'and' and (len(f[1]) >= 3 or any(
            x[0] in ('fparen', 'for', 'ex', 'imp') for x in f[1])):
        items = [rf(x[1] if x[0] == 'fparen' else x) for x in f[1]]
        return r'\begin{fmlist}' + ', and'.join(r'\item %s' % x for x in items) + \
            r'\fmlistend'
    return rf(f)


# ---------------------------------------------------------------- definitions

def let_phrase(lets):
    """'Let G be a graph and v be an element of G.'"""
    parts = []
    for names, ty in lets:
        if ty is None:
            ty = None
            # reserved: find the type
            for n in names:
                rty = CTX.res.get(n)
                parts.append((n, rty))
        else:
            for n in names:
                parts.append((n, ty))
    # group consecutive names with the same type text
    groups = []
    for n, ty in parts:
        txt = rtype(ty) if ty else None
        if groups and groups[-1][1] == txt:
            groups[-1][0].append(n)
        else:
            groups.append(([n], txt))
    phr = []
    for ns, txt in groups:
        vs = ', '.join(m(r_id(n)) for n in ns)
        if txt is None:
            phr.append(vs)
        elif len(ns) > 1:
            tp = rtype(next(ty for n, ty in parts if n == ns[0]), True)
            phr.append('%s be %s' % (vs, tp))
        else:
            phr.append('%s be %s' % (vs, article(txt)))
    if len(phr) == 1:
        return 'Let %s.' % phr[0]
    return 'Let %s, and %s.' % (', '.join(phr[:-1]), phr[-1])


DEFNO = [0]


def defno():
    DEFNO[0] += 1
    return DEFNO[0]


def render_head(kind, head):
    """the defined notion, rendered"""
    if kind in ('pred', 'attr'):
        f = Parser(head).parse_pred_atom()
        return rf(f) if f[0] == 'pred' else ris(f, False)
    return m(rt(Parser(head).parse_term()))


def parse_cases(text):
    """'A if C1, B if C2 otherwise D' -> [(A,C1),(B,C2)], D"""
    cases = []
    p = Parser(text)
    while True:
        t = p.parse_term()
        if p.peek() == 'if':
            p.next()
            c = p.parse_formula()
            cases.append((t, c))
            if p.peek() == ',':
                p.next()
                continue
            p.expect('otherwise')
            return cases, p.parse_term()
        return None, t


def render_definition(lines):
    out = []
    text = ' '.join(lines)
    text = re.sub(r':\w+:', ' ', text)
    # split into statements at ';' (correctness conditions dropped)
    stmts = [s.strip() for s in text.split(';') if s.strip()]
    lets = []
    assume = None
    i = 0
    while i < len(stmts):
        s = stmts[i]
        if s.startswith('let '):
            p = Parser(s[4:])
            lets.extend(p.parse_segs())
        elif s.startswith('assume '):
            assume = re.sub(r'^assume\s+\w+:\s*', '', s)
        elif s.startswith('mode '):
            mm = re.match(r'mode (\w+) is (.*)', s)
            ty = Parser(mm.group(2)).parse_type()
            out.append('A graph is %s.' % article(rtype(ty)).replace(
                'RelStr', 'relational structure'))
        elif re.match(r'(pred|attr|func) ', s):
            mm = re.match(r'(pred|attr|func) (.*?)\s+(means|equals)\s+(.*)$', s,
                          re.S)
            kind, head, how, body = mm.groups()
            body = re.sub(r'\s+(coherence|consistency|existence|uniqueness|'
                          r'symmetry|irreflexivity)\b.*$', '', body)
            props = re.findall(r'\b(symmetry|irreflexivity)\b', s)
            ytype = None
            if kind == 'func':
                head, ytype = re.match(r'(.*?)\s*->\s*(.*)$', head).groups()
            intro = let_phrase(lets) + ' '
            if assume:
                intro += 'Assume that %s. ' % rf(Parser(assume).parse_formula())
            n = defno()
            if kind in ('pred', 'attr'):
                hd = render_head(kind, head)
                f = Parser(body).parse_formula()
                out.append(intro + r'We say that %s if and only if' % hd)
                out.append(r'\fmdef{%d}{%s.}' % (n, rf(f)))
                for pr in props:
                    out.append('Note that the predicate is %s.' % {
                        'symmetry': 'symmetric',
                        'irreflexivity': 'irreflexive'}[pr])
            else:
                hd = render_head(kind, head)
                yt = rtype(Parser(ytype).parse_type())
                if how == 'means':
                    f = Parser(body).parse_formula()
                    out.append(intro + 'The functor %s yielding %s is defined by'
                               % (hd, article(yt)))
                    out.append(r'\fmdef{%d}{%s.}' % (n, rf(f)))
                else:
                    cases, other = parse_cases(body)
                    if cases is None:
                        out.append(intro + 'The functor %s yielding %s is defined '
                                   'by the term' % (hd, article(yt)))
                        out.append(r'\fmdef{%d}{%s.}' % (n, m(rt(other))))
                    else:
                        out.append(intro + 'The functor %s yielding %s is defined '
                                   'by the term' % (hd, article(yt)))
                        conds = ['if %s,' % rf(c) for t, c in cases]
                        conds.append('otherwise.')
                        wide = max(map(len, conds)) > 70
                        rows = [r'%s, & %s' % (rt(t), c if wide else r'\text{%s}' % c)
                                for t, c in zip([t for t, _ in cases] + [other], conds)]
                        out.append(r'\fmdef{%d}{$\left\{\begin{array}'
                                   r'{@{\,}l@{\quad}%s@{}}%s\end{array}\right.$}'
                                   % (n, r'p{0.55\linewidth}' if wide else 'l',
                                      r'\\'.join(rows)))
        i += 1
    return '\n\n'.join(out)


def render_registration(lines):
    text = ' '.join(lines)
    lets = []
    for s in [x.strip() for x in text.split(';') if x.strip()]:
        if s.startswith('let '):
            lets.extend(Parser(s[4:]).parse_segs())
        elif s.startswith('cluster '):
            mm = re.match(r'cluster (.*?) -> (.*)$', s)
            t = Parser(mm.group(1)).parse_term()
            return '%s One can check that %s is %s.' % (let_phrase(lets), m(rt(t)),
                                               mm.group(2))
    return ''


def render_reserve(text):
    """'I for set' / 'f,g for Function of I,NAT' -> From now on ..."""
    parts = []
    segre = re.compile(r'((?:[A-Za-z0-9_]+\s*,\s*)*[A-Za-z0-9_]+)\s+for\s+'
                       r'(.*?)(?=,\s*(?:[A-Za-z0-9_]+\s*,\s*)*[A-Za-z0-9_]+'
                       r'\s+for\s|$)')
    for names, ty in segre.findall(text):
        names = [x.strip() for x in names.split(',')]
        tyast = Parser(ty).parse_type()
        for n in names:
            CTX.res[n] = tyast
        vs = ', '.join(m(r_id(n)) for n in names)
        if len(names) > 1:
            parts.append('%s denote %s' % (vs, rtype(tyast, True)))
        else:
            parts.append('%s denotes %s' % (vs, article(rtype(tyast))))
    return 'From now on %s.' % ', '.join(parts)


SCHEMES = {
    'SumInd': r"""The scheme \emph{SumInd} deals with a set $\mathcal{I}$, a finite
subset $\mathcal{J}$ of $\mathcal{I}$ and a unary predicate $\mathcal{P}$, and
states that $\mathcal{P}[\mathcal{J}]$ provided $\mathcal{P}[\emptyset]$ and for
every object $x$ and every finite subset $B$ of $\mathcal{I}$ such that
$x \in \mathcal{J}$, $B \subseteq \mathcal{J}$, $x \notin B$ and
$\mathcal{P}[B]$ holds $\mathcal{P}[B \cup \{x\}]$.""",
    'LabEx': r"""The scheme \emph{LabEx} deals with a graph $\mathcal{G}$ and a
unary functor $\mathcal{F}$ from the elements of $\mathcal{G}$ into the natural
numbers, and states that there exists a function $f$ from
$\Omega_{\mathcal{G}}$ into $\mathbb{N}$ such that for every element $v$ of
$\mathcal{G}$, $f(v) = \mathcal{F}(v)$.""",
    'GraphEx': r"""The scheme \emph{GraphEx} deals with a non empty finite set
$\mathcal{V}$ and a binary predicate $\mathcal{P}$, and states that there exists
a strict graph $G$ such that $\Omega_G = \mathcal{V}$ and for all objects $x$,
$y$, $\langle x, y\rangle \in E_G$ iff $x \in \mathcal{V}$, $y \in \mathcal{V}$
and $\mathcal{P}[x, y]$, provided for all objects $x$, $y$ such that
$\mathcal{P}[x, y]$ holds $\mathcal{P}[y, x]$, and for every object $x$ not
$\mathcal{P}[x, x]$.""",
    'NatCases': r"""The scheme \emph{NatCases} deals with a unary predicate
$\mathcal{P}$ and two unary functors $\mathcal{F}$, $\mathcal{H}$ from the
natural numbers into the natural numbers, and states that there exists a
function $g$ from $\mathbb{N}$ into $\mathbb{N}$ such that for every natural
number $i$, if $\mathcal{P}[i]$, then $g(i) = \mathcal{F}(i)$, and if not
$\mathcal{P}[i]$, then $g(i) = \mathcal{H}(i)$.""",
}

SECTIONS = [
    ('Section 0.', 'Preliminaries on Sums of Labels'),
    ('Section 1.', 'Graphs, Additive Colorings and the Additive Chromatic Number'),
    ('Section 2.', 'Regular Bipartite and Complete Multipartite Graphs'),
    ('Section 3. Join', 'Joins with Complete Graphs'),
    ('Section 3: paths', 'Paths and Fans'),
    ('Section 3: windmills', 'Windmills'),
    ('Section 3: cycles', 'Cycles and Wheels'),
    ('Section 4. Split', 'Split Graphs'),
    ('Vertices on two sides', 'Headless Spiders'),
    ('Suns.', 'Suns'),
    ('Section 5:', 'Cycle Suns and Wheel Suns'),
    ('Section 4: complete suns', 'Complete Suns'),
]


def plural(n, word):
    return word if n == 1 else word + 's'


def consequence(refs, numbers):
    """'The theorem is a consequence of (3) and (7).'"""
    ns = []
    for r in refs:
        if r in numbers and numbers[r] not in ns:
            ns.append(numbers[r])
    if not ns:
        return ''
    xs = ['(%d)' % n for n in ns]
    if len(xs) == 1:
        lst = xs[0]
    elif len(xs) == 2:
        lst = '%s and %s' % tuple(xs)
    else:
        lst = ', '.join(xs[:-1]) + ', and ' + xs[-1]
    return 'The theorem is a consequence of %s.' % lst


def main(path):
    out = []      # (kind, text)
    thno = 0
    numbers = {}  # theorem label -> number
    for it in items(path):
        k = it['kind']
        if k == 'comment':
            for key, title in SECTIONS:
                if it['text'].startswith(key):
                    out.append(('section', r'\fmsection{%s}' % title))
            continue
        if k == 'reserve':
            out.append(('para', render_reserve(it['text'])))
        elif k == 'definition':
            try:
                out.append(('para', render_definition(it['lines'])))
            except (SyntaxError, IndexError, KeyError, ValueError,
                    AttributeError) as e:
                sys.stderr.write('DEFINITION: %s\n  %s\n' % (e, it['lines']))
        elif k == 'registration':
            out.append(('para', render_registration(it['lines'])))
        elif k == 'scheme':
            name = re.match(r'scheme (\w+)', it['text']).group(1)
            out.append(('para', SCHEMES[name]))
        elif k == 'theorem':
            thno += 1
            CTX.iff = 'if and only if'
            try:
                f = Parser(it['text']).parse_formula()
                body = render_theorem(f)
            except (SyntaxError, IndexError, KeyError, ValueError) as e:
                sys.stderr.write('THEOREM %s: %s\n  %s\n' % (it['label'], e,
                                                            it['text']))
                body = r'\texttt{%s}' % it['text']
            CTX.iff = 'iff'
            if body.startswith(r'\begin{fmlist}'):
                body = r'\fmsameline' + body
            c = consequence(it['refs'], numbers)
            if c and body.endswith(r'\fmlistend.'):
                body += r'\fmafterlist{%s}' % c
            elif c:
                body += ' ' + c
            numbers[it['label']] = thno
            out.append(('thm', r'\fmthm{%d}{%s}{%s}' % (thno, body, it['label'])))
    # "Now we state the proposition(s):" before each run of theorems, appended
    # to the preceding paragraph when there is one
    res = []
    i = 0
    while i < len(out):
        k, t = out[i]
        if k == 'thm':
            j = i
            while j < len(out) and out[j][0] == 'thm':
                j += 1
            now = 'Now we state the %s:' % plural(j - i, 'proposition')
            if res and res[-1][0] == 'para':
                res[-1] = ('para', res[-1][1] + ' ' + now)
            else:
                res.append(('para', now))
            res.extend(out[i:j])
            i = j
            continue
        res.append((k, t))
        i += 1
    print('\n\n'.join(r'\fmpara{%s}' % t if k == 'para' else t for k, t in res))


if __name__ == '__main__':
    main(sys.argv[1])

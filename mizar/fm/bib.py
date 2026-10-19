#!/usr/bin/env python3
"""Write refs.tex: the MML articles used by ../text/acn.miz (from the fm.bib of
the Mizar distribution) and the papers cited by the text, in the style of the
bibliographies of Formalized Mathematics.

Only the works cited in the given LaTeX files are listed, as in recent issues
of Formalized Mathematics.

Usage: python3 bib.py ../text/acn.miz $MIZFILES/../doc/fm.bib acn.tex > refs.tex
"""
import re
import sys

EXTRA = [
    ('Bancerek', r"""Grzegorz Bancerek, Czes{\l}aw Byli\'nski, Adam Grabowski, Artur
Korni{\l}owicz, Roman Matuszewski, Adam Naumowicz, Karol P{\k a}k, and Josef
Urban. Mizar: State-of-the-art and beyond. In Manfred Kerber, Jacques Carette,
Cezary Kaliszyk, Florian Rabe, and Volker Sorge, editors, \emph{Intelligent
Computer Mathematics}, volume 9150 of \emph{Lecture Notes in Computer Science},
pages 261--279. Springer International Publishing, 2015.
doi:10.1007/978-3-319-20615-8\_17.""", 'mizar'),
    ('Czerwinski', r"""Sebastian Czerwi\'nski, Jaros{\l}aw Grytczuk, and Wiktor
\.Zelazny. Lucky labelings of graphs. \emph{Information Processing Letters},
109(18):1078--1081, 2009. doi:10.1016/j.ipl.2009.05.011.""", 'czerwinski'),
    ('Grabowski', r"""Adam Grabowski, Artur Korni{\l}owicz, and Adam Naumowicz.
Four decades of Mizar. \emph{Journal of Automated Reasoning}, 55(3):191--198,
2015. doi:10.1007/s10817-015-9345-1.""", 'fourdecades'),
    ('Marenco', r"""Javier Marenco, Marcelo Mydlarz, and Daniel Sever\'in.
Topological additive numbering of directed acyclic graphs. \emph{Information
Processing Letters}, 115(2):199--202, 2015.
doi:10.1016/j.ipl.2014.09.011.""", 'marenco'),
    ('Severin', r"""Daniel Sever\'in. On the additive chromatic number of several
families of graphs. \emph{Information Processing Letters}, 158:105937, 2020.
doi:10.1016/j.ipl.2020.105937.""", 'severin'),
]


def environ_articles(path):
    head = open(path, encoding='latin-1').read().split('\nbegin\n')[0]
    names = set()
    for d in ('notations', 'theorems', 'schemes'):
        m = re.search(r'\b%s\b([^;]*);' % d, head)
        if m:
            names |= {x.strip() for x in m.group(1).split(',') if x.strip()}
    return sorted(names)


def parse_bib(path):
    text = open(path, encoding='latin-1').read()
    entries = {}
    for m in re.finditer(r'@\w+\{([A-Z0-9_]+)\.ABS,(.*?)\n\s*\n', text + '\n\n', re.S):
        key, body = m.group(1), m.group(2)
        fields = {}
        for f in re.finditer(r'(\w+)\s*=\s*(\{(?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*\}|\d+)',
                             body):
            v = f.group(2)
            if v.startswith('{'):
                v = v[1:-1]
            fields[f.group(1).upper()] = v.strip()
        entries[key] = fields
    return entries


def names_fl(author):
    out = []
    for a in re.split(r'\s+and\s+', author):
        if ',' in a:
            last, first = [x.strip() for x in a.split(',', 1)]
            out.append('%s %s' % (first, last))
        else:
            out.append(a.strip())
    if len(out) == 1:
        return out[0]
    if len(out) == 2:
        return '%s and %s' % tuple(out)
    return ', '.join(out[:-1]) + ', and ' + out[-1]


def first_last(author):
    a = re.split(r'\s+and\s+', author)[0]
    last = a.split(',')[0] if ',' in a else a.split()[-1]
    return re.sub(r'[^A-Za-z]', '', last)


def fm_item(key, e):
    title = e.get('TITLE', key)
    title = re.sub(r'\{([^{}]*)\}', r'\1', title)
    title = title[0].upper() + title[1:].lower() if False else title
    author = names_fl(e.get('AUTHOR', ''))
    journal = e.get('JOURNAL', 'Mizar Mathematical Library')
    vol = e.get('VOLUME', '')
    num = re.sub(r'[^0-9]', '', e.get('NUMBER', ''))
    pages = e.get('PAGES', '')
    year = e.get('YEAR', '')
    doi = e.get('DOI', '')
    s = '%s. %s. \\emph{%s}' % (author, title, journal)
    if vol:
        s += ', %s' % vol
        if num:
            s += '(%s)' % num
        if pages:
            s += ':%s' % pages
    s += ', %s.' % year
    if doi:
        s += ' doi:%s.' % doi.replace('_', r'\_')
    return s


def mml_header(name):
    """title, author and year from the header of the article in the MML"""
    import os
    path = os.path.join(os.path.dirname(BIBPATH[0]), '..', 'share', 'mml',
                        name.lower() + '.miz')
    lines = open(path, encoding='latin-1').read().split('\n')[:6]
    title = lines[0][2:].strip()
    by = re.sub(r'^::\s*by\s*', '', lines[1]).strip()
    year = re.search(r'(\d{4})', ' '.join(lines)).group(1)
    authors = re.split(r',\s*|\s+and\s+', by)
    if by == 'Library Committee':
        authors = ['Library Committee of the Association of Mizar Users']
    author = ' and '.join(authors)
    return {'TITLE': title, 'AUTHOR': author, 'YEAR': year,
            'JOURNAL': 'Mizar Mathematical Library'}


BIBPATH = ['']


def cited_keys(paths):
    keys = set()
    for p in paths:
        for m in re.finditer(r'\\cite(?:\[[^]]*\])?\{([^}]*)\}', open(p).read()):
            keys |= {k.strip() for k in m.group(1).split(',')}
    return keys


def main(miz, bib, *tex):
    BIBPATH[0] = bib
    keys = cited_keys(tex)
    entries = parse_bib(bib)
    items = []
    for name in environ_articles(miz):
        e = entries.get(name)
        if e is None:
            e = mml_header(name)
        items.append((first_last(e.get('AUTHOR', 'Z')), e.get('YEAR', ''),
                      name.lower().replace('_', ''), fm_item(name, e)))
    for last, text, key in EXTRA:
        y = re.search(r'(\d{4})\.', text)
        items.append((last, y.group(1) if y else '', key, text))
    items = [x for x in items if x[2] in keys]
    missing = keys - {x[2] for x in items}
    if missing:
        sys.exit('bib.py: unknown keys: %s' % ', '.join(sorted(missing)))
    items.sort(key=lambda x: (x[0].lower(), x[1]))
    print(r'\begin{thebibliography}{99}')
    for last, year, key, text in items:
        print(r'\bibitem{%s} %s' % (key, text))
        print()
    print(r'\end{thebibliography}')


if __name__ == '__main__':
    main(*sys.argv[1:])

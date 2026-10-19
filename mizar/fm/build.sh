#!/bin/sh
# Builds ../acn.pdf from ../text/acn.miz (statements only) with pdfLaTeX.
# Needs Python 3, pdflatex, and the fm.bib of the Mizar distribution
# (default: ../system/doc/fm.bib; set FMBIB to override).
cd "$(dirname "$0")"
FMBIB=${FMBIB:-../system/doc/fm.bib}
python3 miz2tex.py ../text/acn.miz > body.tex || exit 1
python3 bib.py ../text/acn.miz "$FMBIB" acn.tex > refs.tex || exit 1
for i in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error acn.tex > acn.build.log || {
    grep -A5 '^!' acn.build.log; exit 1; }
done
cp acn.pdf ../acn.pdf
rm -f acn.aux acn.log acn.out acn.pdf
echo "OK: ../acn.pdf"

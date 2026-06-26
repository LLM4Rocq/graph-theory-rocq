# Build the statement-audit PDF (PLAN_WEB M19).
#
#   make            regenerate extracted material, then pdflatex x2
#   make check      run the closure audit gate only
#   make clean

PDF      = digraph_formal.pdf
ROOT     = ../..
PY       = python3

.PHONY: all pdf check generated clean

all: generated pdf

# pdf only — used by CI, which consumes the committed generated
# artifacts (the audit job regenerates and diffs them separately).
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error digraph_formal.tex
	pdflatex -interaction=nonstopmode -halt-on-error digraph_formal.tex

generated:
	cd $(ROOT) && $(PY) scripts/statement_closure.py --check
	cd $(ROOT) && $(PY) scripts/extract_quotes.py
	cd $(ROOT) && $(PY) scripts/gen_panels.py
	cd $(ROOT) && $(PY) scripts/extract_catalog.py

check:
	cd $(ROOT) && $(PY) scripts/statement_closure.py --check

clean:
	rm -f *.aux *.log *.out *.toc *.lol $(PDF)

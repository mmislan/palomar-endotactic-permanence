# Building the formalization and paper

## Lean

Install Lean through elan, then run from the repository root:

```sh
lake exe cache get
lake build Solution
```

`lean-toolchain`, `lakefile.toml` and `lake-manifest.json` pin the environment. `Challenge.lean` contains the two intentional statement holes used by Palomar; `Solution.lean` and its proof dependencies contain the proofs.

`verification/local-check.json` is an extract of the saved local verification results. It records exact source hashes, the selected declarations, Comparator's result and the six kernel results. It does not claim a new run or verification of a future Git commit. All checked Lean sources and dependency pins are preserved byte-for-byte in this repository.

The manual GitHub Actions workflow calls Palomar's complete reusable verification workflow at a pinned revision. Dispatch it with the exact full commit hash and require a passing mechanical report before intake. It is not triggered by pushes.

## Manuscript

With a standard LaTeX installation, run:

```sh
cd paper
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
```

The bibliography and saved figure are included. Figure regeneration is optional: from the repository root, `python paper/make_figures.py` requires NumPy, SciPy and Matplotlib. Saved trajectory data are in `paper/figures/trajectory_data.json`. These numerical illustrations are separate from the formal proofs.

The selected formal claims are uniform permanence and initial-data continuous dependence. The paper's formalization table distinguishes the additional conventional corollaries and the example's scalar comparison lemmas from the selected claims.

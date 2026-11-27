# Prescribing terminal log-concavity patterns in trees with perfect matchings

The paper constructs a finite tree for each finite word of strict log-concavity and strict log-convexity signs, starting next to the independence number. The tree has a perfect matching and diameter at most 10. The manuscript uses conventional graph-theoretic notation. Lean uses the explicit split graph and counts its independent vertex subsets.

| File | Contents |
|---|---|
| `paper.pdf` | English manuscript |
| `paper.tex`, `references.bib`, `paper.bbl` | Manuscript and bibliography sources |
| `Audit.lean` | Entry point for theorem signatures and axiom dependencies |
| `FORMAL_VERIFICATION.md` | Statement correspondence and proof coverage |
| `ORIGINALITY_REVIEW.md` | Search record, source comparisons, and coverage limits |
| `proof.zh.md` | Chinese exposition with complete proof |
| `RESEARCH_HANDOFF.md` | Historical handoff from the previous phase |
| `records/replay/` | Fresh compilation and exact experiment outputs |
| `SHA256SUMS` | Integrity manifest for the rest of the release |

## Build the manuscript

Use XeLaTeX and BibTeX with Latin Modern and standard LaTeX packages including TikZ.

```sh
xelatex -halt-on-error paper.tex
bibtex paper
xelatex -halt-on-error paper.tex
xelatex -halt-on-error paper.tex
```

## Check the proofs

The project pins Lean 4.19.0 and mathlib v4.19.0. With elan, Git and access to GitHub, use:

```sh
lake update
lake exe cache get
lake build
lake env lean Audit.lean
```

To reproduce the recorded clean check against matching prebuilt dependency oleans, use:

```sh
./replay-lean.sh /path/to/lean-4.19.0/bin/lean /path/to/mathlib4-v4.19.0
```

The replay builds package modules in a new directory and turns Lean warnings into errors. The source declaration scan and kernel-level axiom output serve complementary purposes.

## Reproduce the computations

From the extracted directory, use Python 3.12 and a C++17 compiler. The programs use no external datasets or third-party libraries. For an exact check of the recorded outputs:

```sh
out=$(mktemp -d)
python3 -O verify.py > "$out/verification.json"
c++ -O2 -std=c++17 -Wall -Wextra -Werror stress_core.cpp -o "$out/stress_core"
"$out/stress_core" > "$out/core_stress.json"
python3 -O check_scales.py > "$out/scales.json"
for f in verification core_stress scales; do
  cmp "$out/$f.json" "records/replay/$f.json" || exit 1
done
```

The three checks were independently rerun from the archived sources with Python 3.12.14 and GCC 14.2.0. All JSON results matched the earlier archive byte for byte. To get exact coefficients for one word, run `python3 verify.py --word '+-+-' --scale 2`. Coefficients in this output are unsigned hexadecimal integers in descending order of independent-set size.

The physical-tree verifier explicitly joins matched pairs, core arrows and pendant labels. It checks acyclicity and connectedness during its traversal. If (E) and (J) count sets excluding and including the root, the recurrence multiplies child factors (E+J) or (E), respectively, with a factor (x) for an included root. The grouped verifier instead counts empty matched labels with a variable (z). A forced pendant mark contributes (1+z) and a free one contributes (2+z). The C++ program separately maximizes the score on the oriented core by exact-budget dynamic programming on the three possible marks, without the claimed closed form. Direct subset enumeration and direct ternary core enumeration provide small-instance cross-checks.

| Test | Recorded coverage |
|---|---|
| Exact integer coefficients | All 254 words of lengths 1–7 using the small-parameter strategy |
| Core maximum by independent dynamic programming | All 8,190 words through length 12 and 91 additional words with length at most 256 |
| Explicit sufficient scale | Nine computed cases at (p=128(L+1)^2), of which three were also checked on the physical edge list |
| Other cross-checks | 26 physical vs. grouped checks, 65 direct subset counts, and 257,310 ternary assignments scanned |

The two controls obtained scores 85 versus 80 without superadditivity and 30 versus 26 without a sufficiently large balanced weight. At scale 1 the small-parameter strategy missed the prescribed word in 195 of the 254 cases. These results test the proposed hypotheses and illustrate the construction.

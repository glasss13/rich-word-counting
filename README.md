# On a counting conjecture for binary rich words

**Max Glass · November 6, 2026 · Preprint**

[Read the paper (PDF)](paper/rich-word-counting.pdf) · [TeX source](paper/rich-word-counting.tex) · [Main Lean theorems](RichWords/AsymptoticProofs.lean)

Let $R_2(n)$ count binary rich words of length $n$. We prove

$$\limsup_{n\to\infty}\frac{\log R_2(n)}{\sqrt n\log n}=\infty.$$

Consequently, for every fixed $C>0$, the bound $R_2(n)=O(n^{C\sqrt n})$
fails. This disproves the conjectured bound
$O((n/g(n))^{\sqrt n})$ for a positive function $g(n)\to\infty$.

The construction combines independent permutation families on disjoint,
ordered alphabets and encodes their concatenation by binary gaps. A dyadic
choice of block sizes yields the unbounded normalized logarithm.

## Verify the proof

Install [elan](https://github.com/leanprover/elan), the Lean toolchain manager,
and Python 3.9 or later. Then run:

```sh
git clone https://github.com/glasss13/rich-word-counting.git
cd rich-word-counting
lake exe cache get
lake build
python3 verify.py
```

`lean-toolchain` selects Lean 4.30.0; `lake-manifest.json` pins Mathlib
v4.30.0 and its dependencies. The cache command downloads compiled dependencies.
The project proofs compile locally. No files from the original research
workspace are needed.

The verification script rebuilds the project, rechecks every proof module,
and audits every declared theorem's transitive axioms. It permits only
`propext`, `Classical.choice`, and `Quot.sound`, and rejects unfinished proofs,
new axiom declarations, and `native_decide`. It writes `verification.json`
and `verification.log`. The committed [verification report](verification.json)
records source hashes, dependency revisions, and the audited axiom sets.

## Formal statements

The definitions use contiguous factors, count distinct palindromes including
the empty word, and count all binary words without identifying reversals or
complements. See [Definitions.lean](RichWords/Definitions.lean) and
[AsymptoticDefinitions.lean](RichWords/AsymptoticDefinitions.lean).

The main results in namespace `RichWords` are:

| Theorem | Statement |
| --- | --- |
| `rich_count_exceeds_sqrt_power` | For every real `C`, real `K`, and threshold `N`, some `n ≥ max(N, 2)` satisfies `K * n^(C * sqrt(n)) < R₂(n)`. |
| `rich_counting_conjecture_false` | Negates the conjecture, including its existential function, multiplicative constant, and eventual threshold. |
| `rich_count_normalized_log_unbounded` | For every real `A` and threshold `N`, some `n ≥ max(N, 2)` has normalized logarithm greater than `A`. |
| `rich_count_divergent_subsequence` | Gives lengths tending to infinity along which the normalized logarithm tends to infinity. |

The last two statements establish the paper's infinite limsup. The formal
proof uses explicit integer estimates for the same scaled dyadic construction;
the paper presents the limiting argument more briefly. The repository contains
the 25 project modules in the main theorem's import dependency chain, unchanged
from the research development, plus the aggregate import file.

Lean checks the formal statements. The preprint has not undergone external
peer review; formal verification alone does not establish novelty or certify
every sentence of the exposition.

## Build the paper

With a LaTeX installation providing `latexmk`, run:

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error rich-word-counting.tex
```

## Acknowledgment

GPT-6 Astra (OpenAI) was used for the main proof construction and drafting of
the paper.

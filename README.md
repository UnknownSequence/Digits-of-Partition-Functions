# Digits of Partition Functions

This repository contains a Lean 4 formalization of both parts of Theorem 1.2
from my paper
[*On the Digits of Partition Functions*](https://link.springer.com/article/10.1007/s00026-026-00827-9),
published in *Annals of Combinatorics*.

## Main result

Let `p(n)` be the ordinary partition function and `PL(n)` the plane-partition
function. Fix an integer base `b ≥ 2` and a valid `t`-digit base-`b` string
`f` whose leading digit is nonzero. Write `N_p(f,b)` and `N_PL(f,b)` for the
smallest indices at which `p(n)` and `PL(n)`, respectively, begin with the
digits `f` in base `b`.

Theorem 1.1 gives the explicit bounds

```text
N_p(f,b)  ≤ 288 b^(2t) + 2,

N_PL(f,b) ≤ 130 b^(3t) + 29400 b^(3t/2).
```

Thus every prescribed finite leading-digit string occurs in each sequence,
and the theorem controls how far one must search for its first occurrence.
The paper obtains these bounds by converting the leading-digit problem into
an interval-hitting problem for fractional parts of logarithms, then applying
elementary derivative estimates and the mean value theorem.

The main Lean statement is
`PartitionDigits.theorem_1_1_first_occurrence` in
`PartitionsBound/PartitionDigits.lean`.

## Formalization boundary and assumptions

The current Lean development formalizes the deduction of Theorem 1.2 from the
two logarithmic estimates quoted in the paper. It **assumes** those estimates;
it does not yet derive them from combinatorial definitions of the partition
and plane-partition functions. More precisely, `p` and `PL` are arbitrary
functions `ℕ → ℕ` subject to the following hypotheses.

### Ordinary partitions

`PartitionEstimate p b` assumes that `p(n) > 0` for every `n`, and that there
is a real constant `C` such that, for every `n ≥ 4`,

```text
| log_b(p(n))
    - [(π√24 / (6 ln b))√n - (ln n)/(ln b) + C] |
  ≤ 4 / (√n ln b).
```

This is Lemma 2.2 of the paper. For the actual partition function, the paper
uses `C = log_b(√3/12)`.

### Plane partitions

`PlanePartitionEstimate PL b A` assumes that `PL(n) > 0` for every `n`, and
that there is a real constant `C` such that, for every `n ≥ 2829`,

```text
| log_b(PL(n))
    - [(3(A/4)^(1/3) / ln b)n^(2/3)
       - (25/(36 ln b)) ln n + C] |
  ≤ 200 / (n^(2/3) ln b).
```

This is Lemma 2.3 of the paper. For the actual plane-partition function,
`A = ζ(3)` and the paper gives an explicit constant `C = log_b(B)`. The Lean
theorem also assumes the rigorous numerical enclosure

```text
1 ≤ A,    54A ≤ 65,
```

which supplies exactly the bounds on `ζ(3)` needed for the stated coefficient
`130`. The present development does not connect `A` to a formal definition of
the Riemann zeta function.

Consequently, the formal result should be read as follows: **for any two
positive natural-number sequences satisfying the displayed estimates, Lean
proves the two leading-digit bounds in Theorem 1.1.** Instantiating this with
the actual functions `p(n)`, `PL(n)`, and `A = ζ(3)` requires formal proofs of
the assumed analytic estimates and numerical enclosure.

## What Lean proves from those assumptions

Starting from the hypotheses above, the development proves:

* the logarithmic characterization of a leading-digit string;
* the required lower bound for the target interval's width;
* the continuous interval-hitting and derivative arguments;
* the passage from a real interval to a natural-number index;
* conversion from the logarithmic condition to genuine leading digits;
* both explicit upper bounds and their least-occurrence formulation.

There are no `sorry`, `admit`, or user-declared axioms in this deduction.

The supplied LaTeX source for the paper is retained in `paper/main.tex` for
reference.

## Open and check the project

Open the entire project folder in VS Code. With the Lean 4 extension installed,
open `PartitionsBound/PartitionDigits.lean`; Lean will display diagnostics and
proof states automatically.

To check the whole project in VS Code's terminal, run:

```text
lake build
```

On the first run, Lake downloads Mathlib and builds or retrieves its cache.
The resulting hidden `.lake` directory can be several gigabytes. It is a local
dependency/build cache, is excluded by `.gitignore`, and should not be added to
GitHub.

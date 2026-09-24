# Partitions Bound

A Lean 4 formalization of both parts of Theorem 1.1 from my paper
[*On the Digits of Partition Functions*](https://link.springer.com/article/10.1007/s00026-026-00827-9),
published in *Annals of Combinatorics*.

The main source file is `PartitionsBound/PartitionDigits.lean`. The statement
closest to the theorem's least-occurrence notation is
`PartitionDigits.theorem_1_1_first_occurrence`.

The formalization proves the elementary logarithmic interval-width estimate,
the continuous interval-hitting argument, the derivative estimates, rounding
to a natural-number index, conversion back to genuine leading digits, and the
final bounds

* `288 * b^(2*t) + 2` for the ordinary partition function;
* `130 * b^(3*t) + 29400 * b^(3*t/2)` for plane partitions.

As intended, the two published asymptotic estimates are explicit hypotheses
named `PartitionEstimate` and `PlanePartitionEstimate`. The numeric enclosure
needed for the plane-partition constant `A = ζ(3)` is represented by the
hypotheses `1 ≤ A` and `54 * A ≤ 65`. There are no `sorry`, `admit`, or
user-declared axioms.

The supplied LaTeX source for the paper is retained in `paper/main.tex` for
reference.

## Open and check the project

Open this entire folder in VS Code. With the Lean 4 extension installed, open
`PartitionsBound/PartitionDigits.lean`; Lean will display diagnostics and proof
states automatically.

To check the whole project in VS Code's terminal, run:

```text
lake build
```

On the first run, Lake downloads Mathlib and builds or retrieves its cache.
The resulting hidden `.lake` directory can be several gigabytes. It is a local
dependency/build cache, is excluded by `.gitignore`, and should not be added to
GitHub.

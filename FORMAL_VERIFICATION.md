# Lean verification report

**Toolchain.** Lean 4.19.0 (commit `6caaee842e94`) with mathlib v4.19.0. The accompanying `records/replay/lean-audit.txt` records a fresh build in dependency order with warnings treated as errors, followed by theorem signatures and kernel-reported axioms. The project pins both releases. The replay uses previously compiled mathlib dependencies. A separate cold `lake update` attempt stopped at the Git clone of mathlib with exit code 128 in this environment. The complete source build and axiom audit were performed with the matching local mathlib cache.

## Comparison with the manuscript

| Paper statement | Lean verification |
|---|---|
| For each length and each strict word there is one witness | `Quantitative.bounded_family_real_limits (word : List Bool)` introduces the core before any letter index. (L) is `word.length`. The Lean statement also covers the empty word. |
| Correct sign for every (1\le r\le L) | `Family.SignedCounts` requires the strict integer product inequality for every zero-based index (i=r-1) and its recorded Boolean. `true` means (A_{r-1}A_{r+1}>A_r^2). The false case gives the strict reverse inequality. |
| Real independent-set coefficients | `Counting.PhysicalLayer` is the finite type of actual vertex subsets satisfying adjacency-based independence and (|S|+r=m). `Geometry.independence_number` proves (m) is exactly the independence number by providing both an upper bound and an attaining set. `Family.coeff` is the cardinality of this type. |
| Tree, perfect matching, diameter at most 10 | The underlying graph uses `Adj`, an undirected, irreflexive relation on the split vertices. The parent certificate directs each edge to the unique lower-depth neighbor of its deeper endpoint. `Forest` states that every nonempty finite vertex set has a vertex with at most one neighbor inside the set, excluding every simple cycle. Pairwise walks of length at most ten imply connectedness and the diameter bound. The matching is an involution without fixed points, and all its pairs are actual edges. |
| Strict vertex bound | `Quantitative.bounded_instance` proves (|V|<2^{15}(L+1)^7) at the paper's (p=128(L+1)^2). The induction bounds weights and core cardinalities. The Lean construction uses the general bonus profile also for the empty suffix. |
| Same core, real limits zero and (+\infty) | `Quantitative.bounded_family_real_limits` proves actual real-valued `Filter.Tendsto` statements. `ratio_thresholds` gives a common scale threshold for every position for each prescribed integer tolerance. |
| All-positive order bound | `Quantitative.all_positive_order` constructs a matched tree with diameter at most 10 and (|V|<2^{14}(L+1)^6) for the all-positive word, using the square profile. |

## Dependency chain

1. `TerminalCurvature.lean` checks the star gain formula, global allocation bounds, the exact-budget optimizer, and the integer sign transfer.
2. `Word.lean` constructs certificates for all sign words, including arbitrary negative prefixes.
3. `Assembly.lean` relates the abstract certificates to actual three-state assignments on labeled cores. `Counting.lean` establishes the rank-preserving equivalence and count estimates on the split graph.
4. `Family.lean` constructs replicated leaves and applies the count estimates. `Geometry.lean` proves the structural conditions.
5. `Bounds.lean`, `Limits.lean`, and `RealLimits.lean` close the order bounds, uniform ratio thresholds, and real limits.
6. `ExplicitTree.lean` directly reduces a finite mixed-sign witness by kernel computation. `Audit.lean` reports the available signatures and axiom sets.

The proof sources contain no `sorry`, `admit`, custom axiom declarations or `native_decide`. The main theorem depends on `propext`, `Classical.choice`, and `Quot.sound`. The 736-vertex recursive computation depends on no axioms.

The formal model uses explicit graph predicates instead of a separate bridge to mathlib's `SimpleGraph.IsTree`. The proof of the normalized logarithmic rate in the manuscript, the full semantic correctness of the separate finite-experiment implementations, and the literature comparisons remain in the written materials. The two real ratio limits asserted in the theorem are formalized.

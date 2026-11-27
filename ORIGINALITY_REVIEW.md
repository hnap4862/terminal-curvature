# Literature and priority review

Search date: 27 November 2026. The comparison concerns the following joint conclusion: any finite word of **strict** ordinary log-concavity and log-convexity signs, at every position starting one below the independence number, on the same tree with a perfect matching and an absolute diameter bound.

## Search coverage

Searches used arXiv abstracts and full text, SpringerLink, the original Alavi–Malde–Schwenk–Erdős scan and public research archives. Queries combined `independence polynomial`, `independent set sequence`, `perfect matching tree`, `consecutive failures`, `arbitrary sign pattern`, `terminal coefficients`, `prescribed log convexity` and `Turán determinants`. Citation trails ran backward from Fan's introduction and Sections 2, 6 and 7 and from the Springer paper's introduction and bibliography. Site-restricted zbMATH Open and MathSciNet queries were attempted. The direct zbMATH results page was inaccessible and MathSciNet served a JavaScript-only entry page, so this record does not claim comprehensive database coverage.

## Closest results

| Source | What is established or reported | Comparison with the present theorem |
|---|---|---|
| Fan, 2026, Theorems 1.2–1.3 and Section 6 | A failure at any given offset, or simultaneous failures at odd offsets. The general weighted-core criterion transfers a positive exponent second difference to a coefficient failure. Section 6 supplies the matching-pair and free-leaf framework. | A single-position existence result allows the tree to vary with the position. The odd-offset theorem leaves the interleaving signs unspecified and omits positive signs at consecutive offsets. The general criterion requires a core with the desired exponent differences. Our exact profile and prefix construction provide that missing input. |
| Bautista-Ramos, Guillén-Galván and Gómez-Salgado, 2026 | Consecutive failures in infinite families of lengths two and three and finite examples of lengths four and five. | These statements do not prescribe mixed signs at every terminal offset on the same perfectly matched tree. |
| Yu, 2026, public archive v1.1.0 | Unbounded consecutive runs in trees, with a lower bound of order (N^{1/3}) in the number of vertices for the maximal run. | This result already covers unbounded run length without our joint constraints and gives a better run-length bound in that setting. It does not prescribe an arbitrary word beginning at deficit one with a perfect matching. |
| Evidence Press, November 2026, public candidate release | Reports unbounded consecutive runs in diameter-four trees built by attaching copies of a specific module to one hub. The run moves with the scale. | A single moving block of failures has a different quantifier from a word fixed at all of the first (L) offsets. The claims correspond to a public, unrefereed candidate. |
| Alavi, Malde, Schwenk and Erdős, 1987 | Arbitrary relative orderings of coefficients for general graphs. | Direct coefficient orderings and the signs of multiplicative second differences encode different inequalities. The general-graph examples do not supply the restricted tree class. |
| Levit, 2026, *Barrier Log-Concavity of Large Forests* | Uses a modified coefficient inequality and includes results for well-covered trees. Its discussion cites the Fan constructions for ordinary failures. | The barrier property uses a different inequality. The cited constructions give prescribed single or alternating positions, and the discussion does not supply the arbitrary strict word in our theorem. |

Primary links: [Fan](https://arxiv.org/abs/2610.18340), [Springer article](https://link.springer.com/article/10.1007/s00373-026-03054-4), [Yu](https://zenodo.org/records/22263331), [Evidence Press candidate](https://www.evidencepress.org/releases/tree-log-concavity-diameter-four/), [1987 article scan](https://www.renyi.hu/~p_erdos/1987-33.pdf), [Levit](https://arxiv.org/abs/2610.22098).

Fan's Section 6 lower bound includes a factor (2^{-r}), accommodating unused core budget by deleting leaf labels. Our optimizing state uses exactly (r) core holes, so the fixed-core lower estimate has no such loss. The difference central to the new theorem is the construction of a core attaining the prescribed exponent profile. Fan's criterion can perform the final transfer once such a core has been constructed.

The sources inspected yielded neither the full joint theorem nor a direct consequence that supplies its missing profile realization. This is a scoped prior-art assessment. Priority and independent mathematical review remain open.

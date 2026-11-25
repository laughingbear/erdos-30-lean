# erdos-30-lean

Lean 4 proofs of four statements from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures). Together
they show that the largest Sidon set in $\{1, \ldots, N\}$ has size $h(N) \sim \sqrt N$:

| Statement | Content |
|---|---|
| `Erdos30.erdos_30.variants.erdos_turan` | $h(N) \le \sqrt N + C N^{1/4}$ (with $C = 4$) |
| `Erdos30.erdos_30.variants.singer` | $h(N) \ge (1 - \varepsilon)\sqrt N$ for all large $N$ |
| `Erdos30.erdos_30.variants.isEquivalent_sqrt` | $h(N) \sim \sqrt N$ |
| `Erdos241.erdos_241.variants.r_eq_2` | the Bose–Chowla conjecture for $r = 2$ |

The proofs are in [`Erdos30.lean`](Erdos30.lean).

- **Upper bound.** The Erdős–Turán window argument: count pairs of elements in windows of
  length $m \approx N^{3/4}$, bound the off-diagonal count by $m(m-1)$ via an injection that
  uses the Sidon property, then apply Cauchy–Schwarz.
- **Lower bound.** Bose's construction: discrete logarithms of $\theta + c$ in
  $\mathrm{GF}(p^2)^\times$. To get a prime $p$ just below $\sqrt N$, the proof uses
  `prime_between` from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd).
- **Erdős 241, $r = 2$.** The condition defining `f N 2` (distinct 2-element multiset sums) is
  exactly the Sidon property, so `f N 2 = h N`.

`IsSidon`, `Finset.maxSidonSubsetCard`, `Erdos30.h`, `Erdos241.f`,
`Erdos241.BoseChowlaConjecture` and all four statements are copied verbatim from
formal-conjectures. The project depends on PrimeNumberTheoremAnd at commit `a4fb698`
(Lean v4.35.0).

```
lake exe cache get
lake build
```

`#print axioms` for each of the four theorems gives `[propext, Classical.choice, Quot.sound]`.

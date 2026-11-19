# An asymptotic equivalent for Erdős Problem 878(v)

For each positive integer $n$, let $f(n)$ be the sum over primes dividing $n$ of the greatest power of that prime at most $n$. Write $`H(x)=\sum_{1\le n<x} f(n)/n`$. Set $`r_p(x)=\log x-\lfloor\log x/\log p\rfloor\log p`$. As $x\to\infty$ through the natural numbers, the theorem proves

```math
H(x)\sim x\sum_{p\le (\log x)^2}\frac{e^{-r_p(x)}}{p}
\left(r_p(x)+\frac{\log p}{p-1}\right).
```

The proof first groups the summands by prime divisor and then by the largest power of that prime. Harmonic sum bounds yield the weight above with a total error $o(x)$. A Selberg sieve estimate bounds the contribution from primes above the cutoff. The term for $p=2$ bounds the proposed equivalent below by a positive constant times $x$.

The statement is in `Challenge.lean`. The proof is `Erdos878.erdos_878.parts.v` in `Solution.lean`. Run `lake exe cache get` followed by `lake build`. The challenge deliberately contains the statement as a placeholder for Comparator. The solution uses only `propext`, `Classical.choice`, and `Quot.sound`.

Rivka Lipkovitz directed the investigation and maintains the formalization. OpenAI Codex developed the argument and Lean code. The source is licensed under Apache-2.0. See [Erdős Problem 878](https://www.erdosproblems.com/878) and the [existing Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/878.lean).

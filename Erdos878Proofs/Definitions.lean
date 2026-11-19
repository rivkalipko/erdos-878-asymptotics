/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib

/-!
# Definitions for Erdős Problem 878

The definitions of `f` and `H` are taken from the Apache-2.0-licensed
Formal Conjectures statement `FormalConjectures/ErdosProblems/878.lean`.
-/

@[expose] public section

namespace Erdos878

noncomputable def f (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, p ^ Nat.log p n

/-- The sum of `f n / n` over positive integers `n < x`. -/
noncomputable def H (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 x, (f n : ℝ) / n

noncomputable def residue (x p : ℕ) : ℝ :=
  Real.log x - (Nat.log p x : ℝ) * Real.log p

noncomputable def weight (x p : ℕ) : ℝ :=
  Real.exp (-residue x p) / p * (residue x p + Real.log p / ((p : ℝ) - 1))

noncomputable def primeCutoff (x : ℕ) : ℕ :=
  ⌊(Real.log (x : ℝ)) ^ 2⌋₊

/-- The primes at most `x`. -/
def primeBases (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter Nat.Prime

/-- The explicit leading term proposed for part (v). -/
noncomputable def harmonicAnswer (x : ℕ) : ℝ :=
  (x : ℝ) * ∑ p ∈ primeBases (primeCutoff x), weight x p

end Erdos878

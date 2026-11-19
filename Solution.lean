module

public import Erdos878Proofs.HAsymptotic

/-! # Verified solution for part (v) of Erdős Problem 878 -/

@[expose] public section

open Filter Asymptotics

namespace Erdos878

/-- The leading term in the asymptotic for the weighted sum from part (v). -/
noncomputable def erdos_878.parts.v.answer : ℕ → ℝ := harmonicAnswer

/-- The weighted sum is asymptotic to the explicit truncated prime sum. -/
theorem erdos_878.parts.v : H ~[atTop] erdos_878.parts.v.answer := part_v

end Erdos878

#print axioms Erdos878.erdos_878.parts.v

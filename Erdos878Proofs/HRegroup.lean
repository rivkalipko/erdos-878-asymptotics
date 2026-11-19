module

public import Erdos878Proofs.Definitions

/-!
# Prime-by-prime expansion of the average in Erdős Problem 878

The function `H` is the sum in part (v) of [Erdős Problem 878](https://www.erdosproblems.com/878).
The finite bound below replaces harmonic blocks by their logarithmic main terms.
-/

open scoped BigOperators

namespace Erdos878

private noncomputable def primeContribution (x p : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico 1 ⌈(x : ℝ) / p⌉₊, (p : ℝ) ^ Nat.log p m / m

private lemma one_div_succ_le_log_sub_le_one_div (m : ℕ) (hm : 0 < m) :
    1 / ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) - Real.log m ∧
      Real.log ((m : ℝ) + 1) - Real.log m ≤ 1 / (m : ℝ) := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm1' : 0 < (m : ℝ) + 1 := by positivity
  have h₁ := Real.log_le_sub_one_of_pos (div_pos hm' hm1')
  have h₂ := Real.log_le_sub_one_of_pos (div_pos hm1' hm')
  rw [Real.log_div hm'.ne' hm1'.ne'] at h₁
  rw [Real.log_div hm1'.ne' hm'.ne'] at h₂
  constructor
  · have he : (m : ℝ) / ((m : ℝ) + 1) - 1 = -(1 / ((m : ℝ) + 1)) := by
      field_simp
      ring
    linarith
  · have he : ((m : ℝ) + 1) / (m : ℝ) - 1 = 1 / (m : ℝ) := by
      field_simp
      ring
    linarith

private lemma harmonic_Ico_error {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ (∑ i ∈ Finset.Ico a b, 1 / (i : ℝ)) - (Real.log b - Real.log a) ∧
    (∑ i ∈ Finset.Ico a b, 1 / (i : ℝ)) - (Real.log b - Real.log a) ≤ 1 / (a : ℝ) := by
  have hl := Finset.sum_Ico_sub (fun i ↦ Real.log (i : ℝ)) hab
  have hi := Finset.sum_Ico_sub (fun i ↦ -(1 / (i : ℝ))) hab
  rw [← hl, ← Finset.sum_sub_distrib]
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    have hpos := ha.trans_le (Finset.mem_Ico.mp hi).1
    simpa only [Nat.cast_add, Nat.cast_one, sub_nonneg] using
      (one_div_succ_le_log_sub_le_one_div i hpos).2
  · calc
      _ ≤ ∑ i ∈ Finset.Ico a b, (-(1 / ((i + 1 : ℕ) : ℝ)) - -(1 / (i : ℝ))) := by
        apply Finset.sum_le_sum
        intro i hi
        have hpos := ha.trans_le (Finset.mem_Ico.mp hi).1
        have := (one_div_succ_le_log_sub_le_one_div i hpos).1
        push_cast
        linarith
      _ ≤ _ := by
        rw [hi]
        have : 0 ≤ 1 / (b : ℝ) := by positivity
        linarith

private lemma scaled_harmonic_error {a : ℕ} {y : ℝ} (ha : 0 < a) (hay : (a : ℝ) ≤ y) :
    |(a : ℝ) * (∑ i ∈ Finset.Ico a ⌈y⌉₊, 1 / (i : ℝ)) -
      (a : ℝ) * (Real.log y - Real.log a)| ≤ 2 := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hy : 0 < y := ha'.trans_le hay
  have hceil := Nat.le_ceil y
  have hceil' : y ≤ (⌈y⌉₊ : ℝ) := hceil
  have hceilpos : 0 < (⌈y⌉₊ : ℝ) := hy.trans_le hceil'
  have hca : a ≤ ⌈y⌉₊ := by exact_mod_cast hay.trans hceil'
  have hl₁ : 0 ≤ Real.log (⌈y⌉₊ : ℝ) - Real.log y :=
    sub_nonneg.mpr (Real.log_le_log hy hceil')
  have hl₂ : Real.log (⌈y⌉₊ : ℝ) - Real.log y ≤ 1 / (a : ℝ) := by
    have hl := Real.log_le_sub_one_of_pos (div_pos hceilpos hy)
    rw [Real.log_div hceilpos.ne' hy.ne'] at hl
    refine hl.trans ?_
    calc
      (⌈y⌉₊ : ℝ) / y - 1 = ((⌈y⌉₊ : ℝ) - y) / y := by rw [sub_div, div_self hy.ne']
      _ ≤ 1 / y := by gcongr; linarith [Nat.ceil_lt_add_one hy.le]
      _ ≤ 1 / (a : ℝ) := one_div_le_one_div_of_le ha' hay
  rcases harmonic_Ico_error ha hca with ⟨h₁, h₂⟩
  have h₃ : 0 ≤ (∑ i ∈ Finset.Ico a ⌈y⌉₊, 1 / (i : ℝ)) -
      (Real.log y - Real.log a) := by linarith
  have h₄ : (∑ i ∈ Finset.Ico a ⌈y⌉₊, 1 / (i : ℝ)) -
      (Real.log y - Real.log a) ≤ 2 / (a : ℝ) := by
    rw [show (2 : ℝ) / a = 1 / a + 1 / a by ring]
    linarith
  rw [← mul_sub, abs_of_nonneg (mul_nonneg ha'.le h₃)]
  simpa [mul_div_cancel₀ _ ha'.ne'] using mul_le_mul_of_nonneg_left h₄ ha'.le

private lemma H_eq_sum_primeContribution (x : ℕ) :
    H x = ∑ p ∈ primeBases x, primeContribution x p := by
  classical
  unfold H
  calc
    _ = ∑ n ∈ Finset.Ico 1 x, ∑ p ∈ primeBases x with p ∣ n,
        (p : ℝ) ^ Nat.log p n / n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnr := Finset.mem_Ico.mp hn
      have hn0 : n ≠ 0 := by omega
      have hset : n.primeFactors = (primeBases x).filter (· ∣ n) := by
        ext p
        simp only [Nat.mem_primeFactors, Finset.mem_filter, primeBases, Finset.mem_range]
        constructor
        · rintro ⟨hp, hpn, _⟩
          exact ⟨⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn).trans_lt
            (hnr.2.trans (Nat.lt_succ_self x)), hp⟩, hpn⟩
        · rintro ⟨⟨_, hp⟩, hpn⟩
          exact ⟨hp, hpn, hn0⟩
      simp only [f, Nat.cast_sum, Nat.cast_pow, Finset.sum_div, hset]
    _ = ∑ p ∈ primeBases x, ∑ n ∈ Finset.Ico 1 x with p ∣ n,
        (p : ℝ) ^ Nat.log p n / n := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hprime : p.Prime := (Finset.mem_filter.mp hp).2
      have hp' : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
      have hlt (m : ℕ) : m < ⌈(x : ℝ) / p⌉₊ ↔ m * p < x := by
        rw [Nat.lt_ceil, lt_div_iff₀ hp']
        exact_mod_cast Iff.rfl
      unfold primeContribution
      symm
      refine Finset.sum_bij (fun m _ ↦ m * p) ?_ ?_ ?_ ?_
      · intro m hm
        have hmr := Finset.mem_Ico.mp hm
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, (hlt m).mp hmr.2⟩, ?_⟩
        · exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_le_iff.mp hmr.1) hprime.pos)
        · exact ⟨m, Nat.mul_comm m p⟩
      · intro m _ n _ heq
        exact Nat.eq_of_mul_eq_mul_right hprime.pos heq
      · intro n hn
        rcases Finset.mem_filter.mp hn with ⟨hn, m, rfl⟩
        have hnr := Finset.mem_Ico.mp hn
        refine ⟨m, Finset.mem_Ico.mpr ⟨?_, (hlt m).mpr (by simpa [Nat.mul_comm] using hnr.2)⟩,
          Nat.mul_comm m p⟩
        by_contra! hneg
        have hm : m = 0 := by omega
        simp [hm] at hnr
      · intro m hm
        have hmpos : 0 < m := Nat.succ_le_iff.mp (Finset.mem_Ico.mp hm).1
        have hm' : 0 < (m : ℝ) := by exact_mod_cast hmpos
        rw [Nat.log_mul_base hprime.one_lt hmpos.ne', Nat.cast_mul, pow_succ]
        field_simp

private noncomputable def harmonicBlock (p j b : ℕ) : ℝ :=
  (p : ℝ) ^ j * (∑ m ∈ Finset.Ico (p ^ j) b, 1 / (m : ℝ))

private lemma sum_power_block {p j b : ℕ} (hb : b ≤ p ^ (j + 1)) :
    (∑ m ∈ Finset.Ico (p ^ j) b, (p : ℝ) ^ Nat.log p m / m) =
      harmonicBlock p j b := by
  rw [harmonicBlock, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rcases Finset.mem_Ico.mp hm with ⟨hlo, hhi⟩
  rw [Nat.log_eq_of_pow_le_of_lt_pow hlo (hhi.trans_le hb)]
  ring

private lemma sum_full_blocks (p : ℕ) (hp : 1 < p) (k : ℕ) :
    (∑ m ∈ Finset.Ico 1 (p ^ k), (p : ℝ) ^ Nat.log p m / m) =
      ∑ j ∈ Finset.range k, harmonicBlock p j (p ^ (j + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp0 : 0 < p := by omega
    have hmono : p ^ k ≤ p ^ (k + 1) :=
      Nat.pow_le_pow_right hp0 (Nat.le_succ k)
    rw [← Finset.sum_Ico_consecutive _ (Nat.one_le_pow k p hp0) hmono,
      Finset.sum_range_succ, ih, sum_power_block le_rfl]

private lemma full_block_error {p : ℕ} (hp : 1 < p) (j : ℕ) :
    |harmonicBlock p j (p ^ (j + 1)) - (p : ℝ) ^ j * Real.log p| ≤ 1 := by
  have hpos : 0 < p := by omega
  have hpow : p ^ j ≤ p ^ (j + 1) := Nat.pow_le_pow_right hpos (Nat.le_succ j)
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hpos
  have hpj : 0 < (p : ℝ) ^ j := pow_pos hp' _
  have hl : Real.log (↑(p ^ (j + 1)) : ℝ) - Real.log (↑(p ^ j) : ℝ) = Real.log p := by
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
    ring
  obtain ⟨hlow, hupp⟩ := harmonic_Ico_error (pow_pos hpos j) hpow
  rw [hl] at hlow hupp
  push_cast at hupp
  rw [harmonicBlock, ← mul_sub, abs_of_nonneg (mul_nonneg hpj.le hlow)]
  simpa [hpj.ne'] using mul_le_mul_of_nonneg_left hupp hpj.le

private lemma primeContribution_error {x p : ℕ} (hp : 1 < p) (hpx : p ≤ x) :
    |primeContribution x p - (x : ℝ) * weight x p| ≤ (Nat.log p x : ℝ) + 2 := by
  let k : ℕ := Nat.log p x - 1
  let y : ℝ := (x : ℝ) / p
  have hp' : 1 < (p : ℝ) := by exact_mod_cast hp
  have hp0 : 0 < (p : ℝ) := zero_lt_one.trans hp'
  have hx0 : 0 < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hK : 0 < Nat.log p x := Nat.log_pos hp hpx
  have hk : k + 1 = Nat.log p x := by dsimp [k]; omega
  have hylo : (↑(p ^ k) : ℝ) ≤ y := by
    apply (le_div_iff₀ hp0).2
    have hn : p ^ (k + 1) ≤ x := by
      rw [hk]
      exact Nat.pow_log_le_self p (by omega)
    rw [pow_succ] at hn
    exact_mod_cast hn
  have hyhi : y ≤ (↑(p ^ (k + 1)) : ℝ) := by
    apply (div_le_iff₀ hp0).2
    have hn : x < p ^ ((k + 1) + 1) := by
      rw [hk]
      exact Nat.lt_pow_succ_log_self hp _
    rw [pow_succ] at hn
    exact_mod_cast hn.le
  have hs : primeContribution x p =
      (∑ j ∈ Finset.range k, harmonicBlock p j (p ^ (j + 1))) +
        harmonicBlock p k ⌈y⌉₊ := by
    unfold primeContribution
    change (∑ m ∈ Finset.Ico 1 ⌈y⌉₊, (p : ℝ) ^ Nat.log p m / m) = _
    rw [← Finset.sum_Ico_consecutive _ (Nat.one_le_pow k p (by omega))
      (show p ^ k ≤ ⌈y⌉₊ by exact_mod_cast hylo.trans (Nat.le_ceil y)),
      sum_full_blocks p hp k, sum_power_block (Nat.ceil_le.mpr hyhi)]
  have hr : Real.log y - Real.log (↑(p ^ k) : ℝ) = residue x p := by
    rw [residue, ← hk, Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
    rw [show y = (x : ℝ) / p from rfl, Real.log_div hx0.ne' hp0.ne']
    ring
  have hpartial : |harmonicBlock p k ⌈y⌉₊ - (p : ℝ) ^ k * residue x p| ≤ 2 := by
    have h := scaled_harmonic_error (a := p ^ k) (pow_pos (by omega) k) hylo
    rw [hr, Nat.cast_pow] at h
    exact h
  have hfull : |(∑ j ∈ Finset.range k, harmonicBlock p j (p ^ (j + 1))) -
      ∑ j ∈ Finset.range k, (p : ℝ) ^ j * Real.log p| ≤ (k : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ ↦ full_block_error hp j
      _ = _ := by simp
  have hphase : (∑ j ∈ Finset.range k, (p : ℝ) ^ j * Real.log p) +
      (p : ℝ) ^ k * residue x p = (x : ℝ) * weight x p - Real.log p / ((p : ℝ) - 1) := by
    have hexp : Real.exp (-residue x p) = (p : ℝ) ^ (k + 1) / x := by
      have hlog : -residue x p = Real.log ((p : ℝ) ^ (k + 1) / x) := by
        rw [residue, ← hk, Real.log_div (pow_ne_zero _ hp0.ne') hx0.ne', Real.log_pow]
        ring
      rw [hlog, Real.exp_log (by positivity)]
    rw [← Finset.sum_mul, geom_sum_eq hp'.ne' k, weight, hexp, pow_succ]
    field_simp
    ring
  have hshift : |Real.log p / ((p : ℝ) - 1)| ≤ 1 := by
    have hpos : 0 < (p : ℝ) - 1 := sub_pos.mpr hp'
    rw [abs_of_nonneg (div_nonneg (Real.log_nonneg hp'.le) hpos.le), div_le_iff₀ hpos]
    simpa using Real.log_le_sub_one_of_pos hp0
  have htotal : |primeContribution x p - ((x : ℝ) * weight x p -
      Real.log p / ((p : ℝ) - 1))| ≤ (k : ℝ) + 2 := by
    rw [hs, ← hphase, add_sub_add_comm]
    exact (abs_add_le _ _).trans (add_le_add hfull hpartial)
  calc
    _ ≤ |primeContribution x p - ((x : ℝ) * weight x p -
        Real.log p / ((p : ℝ) - 1))| + |Real.log p / ((p : ℝ) - 1)| := by
      rw [show primeContribution x p - (x : ℝ) * weight x p =
        (primeContribution x p - ((x : ℝ) * weight x p - Real.log p / ((p : ℝ) - 1))) -
          Real.log p / ((p : ℝ) - 1) by ring]
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (primeContribution x p - ((x : ℝ) * weight x p -
          Real.log p / ((p : ℝ) - 1))) (-(Real.log p / ((p : ℝ) - 1)))
    _ ≤ (k : ℝ) + 2 + 1 := add_le_add htotal hshift
    _ = _ := by rw [← hk, Nat.cast_add, Nat.cast_one]; ring

/-- Expanding the harmonic sum into its full prime-range phase sum costs at most
    the number of prime-power blocks plus two terms per prime. -/
public theorem abs_H_sub_weight_le (x : ℕ) :
    |H x - (x : ℝ) * ∑ p ∈ primeBases x, weight x p| ≤
      ∑ p ∈ primeBases x, ((Nat.log p x : ℝ) + 2) := by
  rw [H_eq_sum_primeContribution, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
  have hmem := Finset.mem_filter.mp hp
  exact primeContribution_error hmem.2.one_lt
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem.1))

end Erdos878

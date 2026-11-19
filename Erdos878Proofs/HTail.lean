module

public import Erdos878Proofs.Definitions
import PrimeNumberTheoremAnd.BrunTitchmarsh

/-!
# Truncation of the normalized prime sum in Erdős problem 878(v)

The large primes are grouped by the integer parts of `L / log p` and of the
logarithmic remainder. The interval-count input is the Selberg sieve estimate
in `PrimeNumberTheoremAnd.BrunTitchmarsh`.
-/

open scoped BigOperators
open Filter Asymptotics
open Real Finset

noncomputable section

namespace Erdos878.Tail

/-- Exponent of the largest prime power in a logarithmic interval. -/
def exponent (L : ℝ) (p : ℕ) : ℕ := ⌊L / log p⌋₊

/-- Logarithm of the ratio between the endpoint and the largest prime power. -/
def phase (L : ℝ) (p : ℕ) : ℝ := L - (exponent L p : ℝ) * log p

private theorem phase_nonneg {L : ℝ} (hL : 0 ≤ L) {p : ℕ} (hp : 1 < p) :
    0 ≤ phase L p := by
  have hp' : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have h := Nat.floor_le (div_nonneg hL hp'.le : 0 ≤ L / log (p : ℝ))
  exact sub_nonneg.mpr ((le_div_iff₀ hp').mp h)

private theorem phase_le {L : ℝ} {p : ℕ} (hp : 1 < p) : phase L p ≤ L := by
  have hp' : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hp.le)
  exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hp')

private theorem exponent_pos {L : ℝ} {p : ℕ} (hp : 1 < p) (hpL : (p : ℝ) ≤ exp L) :
    0 < exponent L p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast (zero_lt_one.trans hp)
  have hlog : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have h : log (p : ℝ) ≤ L := by
    rw [← log_exp L]
    exact strictMonoOn_log.monotoneOn hp' (exp_pos _) hpL
  change 1 ≤ ⌊L / log (p : ℝ)⌋₊
  exact (Nat.le_floor_iff (div_nonneg (hlog.le.trans h) hlog.le)).mpr (by simpa using (le_div_iff₀ hlog).mpr (by simpa))

private theorem log_twice_le_log_prime {L : ℝ} (hL : 0 < L) {p : ℕ} (hp : L ^ 2 < p) :
    2 * log L < log (p : ℝ) := by
  have h := strictMonoOn_log (show 0 < L ^ 2 by positivity)
    (lt_trans (by positivity : 0 < L ^ 2) hp) hp
  simpa [log_pow] using h

private theorem exponent_le {L : ℝ} (hL : 1 < L) {p : ℕ} (hp : L ^ 2 < p) :
    exponent L p ≤ ⌊L / (2 * log L)⌋₊ := by
  have hh := log_twice_le_log_prime (zero_lt_one.trans hL) hp
  unfold exponent
  exact Nat.floor_mono (div_le_div_of_nonneg_left (zero_lt_one.trans hL).le (mul_pos (by norm_num) (log_pos hL)) hh.le)

/-- A uniform upper bound for the number of primes in a real interval. -/
theorem primeIntervalUpper :
    ∃ C > 0, ∃ A > 1, ∀ a h : ℝ, 0 < a → A ≤ h →
      (BrunTitchmarsh.primesBetween a (a + h) : ℝ) ≤ C * (h / log h) := by
  have hO := BrunTitchmarsh.err_isBigO
  obtain ⟨C, hCpos, hC⟩ := hO.exists_pos
  obtain ⟨A, hA⟩ := eventually_atTop.1 hC.bound
  refine ⟨4 + 6 * C, by positivity, max A 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro a h ha hah
  have hh : 1 < h := (lt_of_lt_of_le (by norm_num) (le_max_right A 2)).trans_le hah
  have hr : log (h ^ (1 / 2 : ℝ)) = 1 / 2 * log h := log_rpow (by positivity) _
  have hz : 1 < h ^ (1 / 2 : ℝ) := one_lt_rpow hh (by norm_num)
  have hB := BrunTitchmarsh.primesBetween_le a h (h ^ (1 / 2 : ℝ)) ha (by positivity) hz
  have hE := hA h ((le_max_left A 2).trans hah)
  have hhpos := zero_lt_one.trans hh
  have hlog := log_pos hh
  have hleft : 0 ≤ h ^ (1 / 2 : ℝ) * (1 + 1 / 2 * log h) ^ 3 := by positivity
  have hright : 0 ≤ h / log h := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright] at hE
  rw [hr] at hB
  rw [show 2 * h / (1 / 2 * log h) = 4 * (h / log h) by ring] at hB
  calc
    _ ≤ 4 * (h / log h) + 6 * (h ^ (1 / 2 : ℝ) * (1 + 1 / 2 * log h) ^ 3) := by
      simpa only [mul_assoc] using hB
    _ ≤ _ := by linarith

private theorem window_geometry {L j k : ℝ} (hL : exp 1 ≤ L)
    (hj : j ≤ L / 2) (hk : 1 ≤ k) (hkL : k ≤ L / (2 * log L))
    {p : ℝ} (hp : L ^ 2 < p) (hpu : p ≤ exp ((L - j) / k)) :
    let t := (L - j) / k
    let h := exp t - exp (t - 1 / k)
    L ≤ h ∧ h ≤ exp t / k ∧ t / 2 ≤ log h ∧ 0 < t := by
  dsimp only
  have hLpos := (exp_pos 1).trans_le hL
  have hL1 : 1 < L := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hL
  have hlog : 1 ≤ log L := by
    rw [← log_exp 1]
    exact strictMonoOn_log.monotoneOn (exp_pos _) hLpos hL
  have ht : 0 < (L - j) / k := div_pos (by linarith) (lt_of_lt_of_le zero_lt_one hk)
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  have hw : 0 < 1 / k := by positivity
  have hw1 : 1 / k ≤ 1 := (div_le_iff₀ hkpos).mpr (by simpa)
  have hkw : 2 * k ≤ L := by
    have h1 := (le_div_iff₀ (by positivity : 0 < 2 * log L)).mp hkL
    nlinarith [mul_nonneg hkpos.le (sub_nonneg.mpr hlog)]
  let t := (L - j) / k
  let w := 1 / k
  have hlower : w / 2 ≤ 1 - exp (-w) := by
    have hE := add_one_le_exp w
    have hE' : exp (-w) * (w + 1) ≤ 1 := by
      rw [exp_neg]
      exact (inv_mul_le_iff₀ (exp_pos _)).mpr (by simpa using hE)
    have hpoly : 0 ≤ w * (1 - w) := mul_nonneg hw.le (sub_nonneg.mpr hw1)
    by_contra! hcontra
    have hmul := mul_lt_mul_of_pos_right hcontra (show 0 < w + 1 by positivity)
    nlinarith
  have hupper : 1 - exp (-w) ≤ w := by linarith [add_one_le_exp (-w)]
  have hh_eq : exp t - exp (t - w) = exp t * (1 - exp (-w)) := by
    rw [sub_eq_add_neg t w, exp_add]
    ring
  change L ≤ exp t - exp (t - w) ∧ exp t - exp (t - w) ≤ exp t / k ∧
    t / 2 ≤ log (exp t - exp (t - w)) ∧ 0 < t
  have hhlo : exp t / (2 * k) ≤ exp t - exp (t - w) := by
    rw [hh_eq, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (exp_nonneg _)
    have hw_eq : (2 * k)⁻¹ = w / 2 := by
      dsimp [w]
      field_simp
    rw [hw_eq]
    exact hlower
  have hpU : L ^ 2 < exp t := hp.trans_le hpu
  have hLL : L ≤ exp t / (2 * k) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hkw hLpos.le]
  have htlog : 2 * log L ≤ t := by
    have h := strictMonoOn_log (show 0 < L ^ 2 by positivity) (exp_pos t) hpU
    simpa [log_pow] using h.le
  have hUL : exp t / L ≤ exp t - exp (t - w) :=
    (div_le_div_of_nonneg_left (exp_nonneg _) (by positivity) hkw).trans hhlo
  refine ⟨hLL.trans hhlo, ?_, ?_, ht⟩
  · rw [hh_eq, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hupper (exp_nonneg _)
  · have hcomp := strictMonoOn_log.monotoneOn (show 0 < exp t / L by positivity)
      (hLpos.trans_le (hLL.trans hhlo)) hUL
    rw [log_div (exp_pos _).ne' hLpos.ne', log_exp] at hcomp
    linarith

private theorem window_mem {L : ℝ} {j k p : ℕ} (hk : 0 < k)
    (hL : 0 ≤ L) (hp : 1 < p)
    (hej : ⌊phase L p⌋₊ = j) (hek : exponent L p = k) :
    let t := (L - j) / k
    exp (t - 1 / k) < (p : ℝ) ∧ (p : ℝ) ≤ exp t := by
  dsimp only
  have hp' : (0 : ℝ) < p := by exact_mod_cast (zero_lt_one.trans hp)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := Nat.floor_le (phase_nonneg hL hp)
  have h2 := Nat.lt_floor_add_one (phase L p)
  rw [hej, phase, hek] at h1 h2
  have h1' : log (p : ℝ) ≤ (L - j) / k := by
    apply (le_div_iff₀ hkr).mpr
    linarith
  have h2' : (L - j) / k - 1 / k < log (p : ℝ) := by
    rw [← sub_div]
    apply (div_lt_iff₀ hkr).mpr
    linarith
  exact ⟨by simpa [exp_log hp'] using exp_lt_exp.mpr h2',
    by simpa [exp_log hp'] using exp_le_exp.mpr h1'⟩

private theorem window_sum {C A : ℝ} (hC : 0 < C) (hA : 1 < A)
    (hB : ∀ a h : ℝ, 0 < a → A ≤ h →
      (BrunTitchmarsh.primesBetween a (a + h) : ℝ) ≤ C * (h / log h))
    {L : ℝ} (hL : exp 1 ≤ L) (hAL : A ≤ L)
    {j k : ℕ} (hj : (j : ℝ) ≤ L / 2)
    (hk : 0 < k) (hkL : (k : ℝ) ≤ L / (2 * log L))
    (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ L ^ 2 < (p : ℝ) ∧
      ⌊phase L p⌋₊ = j ∧ exponent L p = k) :
    ∑ p ∈ s, (p : ℝ)⁻¹ ≤ (4 * C * exp 1) / L := by
  have hLpos := (exp_pos 1).trans_le hL
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  let t := (L - j) / k
  let U := exp t
  let V := exp (t - 1 / k)
  let h := U - V
  have hinterval (p : ℕ) (hp : p ∈ s) : V < (p : ℝ) ∧ (p : ℝ) ≤ U := by
    obtain ⟨hpp, _, hpj, hpk⟩ := hs p hp
    exact window_mem hk hLpos.le hpp.one_lt hpj hpk
  by_cases hempty : s = ∅
  · simp [hempty]
    positivity
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨hhL, hhU, hlog, ht⟩ := window_geometry hL hj (by exact_mod_cast hk) hkL
    (hs p hp).2.1 (hinterval p hp).2
  change L ≤ h at hhL
  change h ≤ U / k at hhU
  change t / 2 ≤ log h at hlog
  change 0 < t at ht
  have hhpos : 0 < h := hLpos.trans_le hhL
  have hlogpos : 0 < log h := (by positivity : 0 < t / 2).trans_le hlog
  have hp_bound : ∀ p ∈ s, (p : ℝ)⁻¹ ≤ exp 1 / U := by
    intro p hp
    have hw1 : (1 : ℝ) / k ≤ 1 := (div_le_iff₀ hkr).mpr (by simpa using (show (1 : ℝ) ≤ k by exact_mod_cast hk))
    have hlow : exp (t - 1) ≤ (p : ℝ) :=
      (exp_le_exp.mpr (by linarith)).trans (hinterval p hp).1.le
    rw [show exp 1 / U = (exp (t - 1))⁻¹ by
      dsimp [U]
      rw [exp_sub, inv_div]]
    simp only [← one_div]
    exact one_div_le_one_div_of_le (exp_pos _) hlow
  have hscard : s.card ≤ BrunTitchmarsh.primesBetween V U := by
    unfold BrunTitchmarsh.primesBetween
    refine card_le_card (fun p hp ↦ ?_)
    rw [mem_filter, mem_Icc, Nat.ceil_le, Nat.le_floor_iff (exp_nonneg _)]
    exact ⟨⟨(hinterval p hp).1.le, (hinterval p hp).2⟩, (hs p hp).1⟩
  have hcard := hB V h (exp_pos _) (hAL.trans hhL)
  rw [show V + h = U by dsimp [h]; ring] at hcard
  have hratio : h / log h ≤ (U / k) / (t / 2) := by
    exact (div_le_div_of_nonneg_right hhU hlogpos.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hlog)
  have hlast : (C * ((U / k) / (t / 2))) * (exp 1 / U) ≤ (4 * C * exp 1) / L := by
    have hstep : (C * ((U / k) / (t / 2))) * (exp 1 / U) =
        (2 * C * exp 1) / (L - j) := by
      have hUpos : 0 < U := exp_pos _
      have hLj : 0 < L - j := by linarith
      dsimp [t]
      field_simp
    rw [hstep, show (4 * C * exp 1) / L = (2 * C * exp 1) / (L / 2) by ring]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  calc
    ∑ p ∈ s, (p : ℝ)⁻¹ ≤ ∑ _ ∈ s, exp 1 / U := Finset.sum_le_sum hp_bound
    _ = (s.card : ℝ) * (exp 1 / U) := by simp
    _ ≤ C * (h / log h) * (exp 1 / U) := by
      exact mul_le_mul_of_nonneg_right
        ((show (s.card : ℝ) ≤ BrunTitchmarsh.primesBetween V U by exact_mod_cast hscard).trans hcard)
        (by positivity)
    _ ≤ _ := (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio hC.le) (by positivity)).trans hlast

private theorem harmonic_bound {L : ℝ} (hL : 0 ≤ L) (s : Finset ℕ)
    (hs : ∀ p ∈ s, 0 < p ∧ (p : ℝ) ≤ exp L) :
    ∑ p ∈ s, (p : ℝ)⁻¹ ≤ 1 + L := by
  have hsubset : s ⊆ Icc 1 ⌊exp L⌋₊ := by
    intro p hp
    rw [mem_Icc, Nat.le_floor_iff (exp_nonneg _)]
    exact hs p hp
  calc
    ∑ p ∈ s, (p : ℝ)⁻¹ ≤ ∑ p ∈ Icc 1 ⌊exp L⌋₊, (p : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hsubset (fun p _ _ ↦ by positivity)
    _ = (harmonic ⌊exp L⌋₊ : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + L := by
      simpa using harmonic_floor_le_one_add_log (exp L) (one_le_exp_iff.mpr hL)

private theorem weight_summable :
    Summable (fun j : ℕ ↦ (j + 1 : ℝ) * exp (-(j : ℝ))) := by
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 1)
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 (by norm_num : (0 : ℝ) < 1)
  simpa only [add_mul, pow_one, pow_zero, one_mul, neg_one_mul] using h1.add h0

private theorem phase_sum_low {C A : ℝ} (hC : 0 < C) (hA : 1 < A)
    (hB : ∀ a h : ℝ, 0 < a → A ≤ h →
      (BrunTitchmarsh.primesBetween a (a + h) : ℝ) ≤ C * (h / log h))
    {L : ℝ} (hL : exp 1 ≤ L) (hAL : A ≤ L) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ L ^ 2 < (p : ℝ) ∧ (p : ℝ) ≤ exp L ∧
      (⌊phase L p⌋₊ : ℝ) ≤ L / 2) :
    ∑ p ∈ s, exp (-phase L p) * phase L p / p ≤
      (2 * C * exp 1 * (∑' j : ℕ, (j + 1 : ℝ) * exp (-(j : ℝ)))) / log L := by
  have hLpos := (exp_pos 1).trans_le hL
  have hL1 : 1 < L := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hL
  have hlog : 0 < log L := log_pos hL1
  let K := ⌊L / (2 * log L)⌋₊
  let J := ⌊L / 2⌋₊
  let a (j : ℕ) := (j + 1 : ℝ) * exp (-(j : ℝ))
  let g (p : ℕ) := exp (-phase L p) * phase L p / p
  have ha (j : ℕ) : 0 ≤ a j := by dsimp [a]; positivity
  have hsum : 0 ≤ ∑' j, a j := tsum_nonneg ha
  have hk_mem (p : ℕ) (hp : p ∈ s) : exponent L p ∈ Icc 1 K := by
    obtain ⟨hpp, hp', hpL, _⟩ := hs p hp
    exact mem_Icc.mpr ⟨exponent_pos hpp.one_lt hpL, exponent_le hL1 hp'⟩
  have hbound_k (k : ℕ) (hk : k ∈ Icc 1 K) :
      ∑ p ∈ s with exponent L p = k, g p ≤
        (4 * C * exp 1) / L * (∑' j, a j) := by
    have hk1 : 0 < k := (mem_Icc.mp hk).1
    have hkL : (k : ℝ) ≤ L / (2 * log L) :=
      (Nat.le_floor_iff (by positivity)).mp (mem_Icc.mp hk).2
    let S := s.filter (fun p ↦ exponent L p = k)
    change ∑ p ∈ S, g p ≤ _
    have hj_mem (p : ℕ) (hp : p ∈ S) : ⌊phase L p⌋₊ ∈ range (J + 1) := by
      rw [mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (by positivity)]
      exact (hs p (mem_filter.mp hp).1).2.2.2
    rw [← sum_fiberwise_of_maps_to hj_mem g]
    calc
      _ ≤ ∑ j ∈ range (J + 1), a j * ((4 * C * exp 1) / L) := by
        refine sum_le_sum (fun j hj ↦ ?_)
        let T := S.filter (fun p ↦ ⌊phase L p⌋₊ = j)
        change ∑ p ∈ T, g p ≤ _
        have hjL : (j : ℝ) ≤ L / 2 :=
          (Nat.le_floor_iff (show 0 ≤ L / 2 by positivity)).mp
            (Nat.lt_succ_iff.mp (mem_range.mp hj))
        have ht (p : ℕ) (hp : p ∈ T) :
            p.Prime ∧ L ^ 2 < (p : ℝ) ∧ ⌊phase L p⌋₊ = j ∧ exponent L p = k := by
          obtain ⟨hpS, hpj⟩ := mem_filter.mp hp
          obtain ⟨hps, hpk⟩ := mem_filter.mp hpS
          exact ⟨(hs p hps).1, (hs p hps).2.1, hpj, hpk⟩
        calc
          ∑ p ∈ T, g p ≤ ∑ p ∈ T, a j * (p : ℝ)⁻¹ := by
            refine sum_le_sum (fun p hp ↦ ?_)
            have h := ht p hp
            have hp0 : 0 ≤ phase L p := phase_nonneg hLpos.le h.1.one_lt
            have hjr : (j : ℝ) ≤ phase L p := by
              simpa only [h.2.2.1] using Nat.floor_le hp0
            have hrj : phase L p ≤ (j : ℝ) + 1 := by
              simpa only [h.2.2.1] using (Nat.lt_floor_add_one (phase L p)).le
            dsimp [g, a]
            rw [div_eq_mul_inv, mul_comm ((j : ℝ) + 1)]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul (exp_le_exp.mpr (by linarith)) hrj hp0 (by positivity))
              (by positivity)
          _ = a j * (∑ p ∈ T, (p : ℝ)⁻¹) := by rw [mul_sum]
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (window_sum hC hA hB hL hAL hjL hk1 hkL T ht) (ha _)
      _ = ((4 * C * exp 1) / L) * ∑ j ∈ range (J + 1), a j := by
        rw [mul_sum]
        exact sum_congr rfl (fun _ _ ↦ mul_comm _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (weight_summable.sum_le_tsum _ (fun j _ ↦ ha j)) (by positivity)
  have hK : (K : ℝ) ≤ L / (2 * log L) := Nat.floor_le (by positivity)
  change ∑ p ∈ s, g p ≤ _
  rw [← sum_fiberwise_of_maps_to hk_mem g]
  calc
    _ ≤ ∑ _ ∈ Icc 1 K, ((4 * C * exp 1) / L * (∑' j, a j)) := sum_le_sum hbound_k
    _ = (K : ℝ) * ((4 * C * exp 1) / L * (∑' j, a j)) := by simp [Nat.card_Icc]
    _ ≤ L / (2 * log L) * ((4 * C * exp 1) / L * (∑' j, a j)) :=
      mul_le_mul_of_nonneg_right hK (by positivity)
    _ = _ := by dsimp [a]; field_simp; ring

private theorem phase_sum_high {L : ℝ} (hL : 1 < L) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ exp L ∧ L / 2 ≤ phase L p) :
    ∑ p ∈ s, exp (-phase L p) * phase L p / p ≤ 96 / log L := by
  have hLpos := zero_lt_one.trans hL
  have hlog := log_pos hL
  have hstep : exp (-(L / 2)) * L * (1 + L) ≤ 96 / log L := by
    have hE := Real.pow_div_factorial_le_exp (L / 2) (by positivity) 3
    norm_num at hE
    have hp : L ^ 3 ≤ 48 * exp (L / 2) := by linarith
    have hlogL : log L ≤ L := Real.log_le_self hLpos.le
    rw [exp_neg]
    apply (le_div_iff₀ hlog).mpr
    have hpoly : L * (1 + L) * log L ≤ 2 * L ^ 3 := by
      calc
        _ ≤ L * (2 * L) * L := by gcongr; linarith
        _ = _ := by ring
    calc
      _ = (exp (L / 2))⁻¹ * (L * (1 + L) * log L) := by ring
      _ ≤ (exp (L / 2))⁻¹ * (96 * exp (L / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ p ∈ s, (exp (-(L / 2)) * L) * (p : ℝ)⁻¹ := by
      refine sum_le_sum (fun p hp ↦ ?_)
      have h := hs p hp
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (exp_le_exp.mpr (by linarith [h.2.2]))
          (phase_le h.1.one_lt) (phase_nonneg hLpos.le h.1.one_lt) (by positivity))
        (by positivity)
    _ = (exp (-(L / 2)) * L) * (∑ p ∈ s, (p : ℝ)⁻¹) := by rw [mul_sum]
    _ ≤ exp (-(L / 2)) * L * (1 + L) :=
      mul_le_mul_of_nonneg_left
        (harmonic_bound hLpos.le s (fun p hp ↦ ⟨(hs p hp).1.pos, (hs p hp).2.1⟩))
        (by positivity)
    _ ≤ _ := hstep

private theorem correction_sum {L : ℝ} (hL : 1 < L) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ L ^ 2 < (p : ℝ) ∧ (p : ℝ) ≤ exp L) :
    ∑ p ∈ s, exp (-phase L p) / p * (log (p : ℝ) / ((p : ℝ) - 1)) ≤
      32 / log L := by
  have hLpos := zero_lt_one.trans hL
  have hlog := log_pos hL
  have hLlog : 0 < L * log L := by positivity
  have hterm (p : ℕ) (hp : p ∈ s) :
      log (p : ℝ) / ((p : ℝ) - 1) ≤ 16 / (L * log L) := by
    obtain ⟨hpp, hpL, _⟩ := hs p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hplog : 0 < log (p : ℝ) := log_pos (by linarith)
    have hlog2 := log_twice_le_log_prime hLpos hpL
    let q := exp (log (p : ℝ) / 2)
    have hq : L ≤ q := by
      rw [← exp_log hLpos]
      exact exp_le_exp.mpr (by linarith)
    have hqpos : 0 < q := exp_pos _
    have hq2 : q * q = p := by
      dsimp [q]
      rw [← exp_add, show log (p : ℝ) / 2 + log (p : ℝ) / 2 = log (p : ℝ) by ring]
      exact exp_log (by linarith)
    have hE := Real.pow_div_factorial_le_exp (log (p : ℝ) / 2) (by positivity) 2
    change (log (p : ℝ) / 2) ^ 2 / (Nat.factorial 2 : ℝ) ≤ q at hE
    norm_num at hE
    have hpoly : log (p : ℝ) * (L * log L) ≤ 8 * (p : ℝ) := by
      calc
        _ = log (p : ℝ) * log L * L := by ring
        _ ≤ log (p : ℝ) * log (p : ℝ) * L :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) hplog.le) hLpos.le
        _ ≤ 8 * q * L :=
          mul_le_mul_of_nonneg_right (by nlinarith) hLpos.le
        _ ≤ 8 * q * q :=
          mul_le_mul_of_nonneg_left hq (by positivity)
        _ = _ := by rw [mul_assoc, hq2]
    exact (div_le_div_iff₀ (by linarith) hLlog).mpr (by linarith)
  calc
    _ ≤ ∑ p ∈ s, (16 / (L * log L)) * (p : ℝ)⁻¹ := by
      refine sum_le_sum (fun p hp ↦ ?_)
      have hpp := (hs p hp).1
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      have hphase := phase_nonneg hLpos.le hpp.one_lt
      have hexp : exp (-phase L p) ≤ 1 := exp_le_one_iff.mpr (by linarith)
      rw [div_eq_mul_inv, mul_right_comm]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using mul_le_mul hexp (hterm p hp)
        (by positivity : 0 ≤ log (p : ℝ) / ((p : ℝ) - 1)) (by positivity)
    _ = (16 / (L * log L)) * (∑ p ∈ s, (p : ℝ)⁻¹) := by rw [mul_sum]
    _ ≤ (16 / (L * log L)) * (1 + L) :=
      mul_le_mul_of_nonneg_left
        (harmonic_bound hLpos.le s (fun p hp ↦ ⟨(hs p hp).1.pos, (hs p hp).2.2⟩))
        (by positivity)
    _ ≤ (16 / (L * log L)) * (2 * L) := by gcongr; linarith
    _ = _ := by field_simp; ring

private theorem all_tail_bound :
    ∃ C > 0, ∃ A : ℝ, ∀ L ≥ A, ∀ (s : Finset ℕ),
      (∀ p ∈ s, p.Prime ∧ L ^ 2 < (p : ℝ) ∧ (p : ℝ) ≤ exp L) →
      ∑ p ∈ s, exp (-phase L p) / p * (phase L p + log (p : ℝ) / ((p : ℝ) - 1)) ≤
        C / log L := by
  obtain ⟨C, hC, A, hA, hB⟩ := primeIntervalUpper
  let B := 2 * C * exp 1 * (∑' j : ℕ, (j + 1 : ℝ) * exp (-(j : ℝ)))
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ∑' j : ℕ, (j + 1 : ℝ) * exp (-(j : ℝ)) := tsum_nonneg (fun j ↦ by positivity)
    dsimp [B]
    positivity
  refine ⟨B + 128, by positivity, max A (exp 1), ?_⟩
  intro L hL s hs
  have hAL := (le_max_left A (exp 1)).trans hL
  have hL1 := (le_max_right A (exp 1)).trans hL
  have hLgt : 1 < L := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hL1
  have hLpos := zero_lt_one.trans hLgt
  let P (p : ℕ) := (⌊phase L p⌋₊ : ℝ) ≤ L / 2
  let g (p : ℕ) := exp (-phase L p) * phase L p / p
  have hlo : ∀ p ∈ s.filter P, p.Prime ∧ L ^ 2 < (p : ℝ) ∧
      (p : ℝ) ≤ exp L ∧ (⌊phase L p⌋₊ : ℝ) ≤ L / 2 := by
    intro p hp
    obtain ⟨hps, hpP⟩ := mem_filter.mp hp
    obtain ⟨ha, hb, hc⟩ := hs p hps
    exact ⟨ha, hb, hc, hpP⟩
  have hhi : ∀ p ∈ s.filter (fun p ↦ ¬ P p),
      p.Prime ∧ (p : ℝ) ≤ exp L ∧ L / 2 ≤ phase L p := by
    intro p hp
    obtain ⟨hps, hpP⟩ := mem_filter.mp hp
    obtain ⟨ha, _, hc⟩ := hs p hps
    exact ⟨ha, hc, (lt_of_not_ge hpP).le.trans (Nat.floor_le (phase_nonneg hLpos.le ha.one_lt))⟩
  have hsplit : ∑ p ∈ s, g p ≤ (B + 96) / log L := by
    rw [← sum_filter_add_sum_filter_not s P g, add_div]
    exact add_le_add (phase_sum_low hC hA hB hL1 hAL _ hlo) (phase_sum_high hLgt _ hhi)
  calc
    ∑ p ∈ s, exp (-phase L p) / p * (phase L p + log (p : ℝ) / ((p : ℝ) - 1)) =
        ∑ p ∈ s, g p + ∑ p ∈ s, exp (-phase L p) / p * (log (p : ℝ) / ((p : ℝ) - 1)) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun _ _ ↦ by dsimp [g]; ring)
    _ ≤ (B + 96) / log L + 32 / log L := add_le_add hsplit (correction_sum hLgt s hs)
    _ = _ := by ring

private theorem phase_eq_residue (x p : ℕ) : phase (log (x : ℝ)) p = residue x p := by
  unfold phase residue exponent
  rw [← Real.logb, Real.natFloor_logb_natCast]

end Erdos878.Tail

namespace Erdos878

/-- The normalized contribution from primes above the square-logarithm cutoff. -/
public theorem primeTail_isBigO :
    (fun x : ℕ ↦ ∑ p ∈ (primeBases x).filter (primeCutoff x < ·), weight x p)
      =O[atTop] (fun x : ℕ ↦ (Real.log (Real.log (x : ℝ)))⁻¹) := by
  obtain ⟨C, hC, A, hA⟩ := Tail.all_tail_bound
  refine Asymptotics.IsBigO.of_bound C ?_
  have hlog : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hlog.eventually_ge_atTop (max A 2)
  filter_upwards [hlarge, Filter.eventually_ge_atTop 1] with x hx hx1
  let L := Real.log (x : ℝ)
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x from hx1)
  have hL : 1 < L := (by norm_num : (1 : ℝ) < 2).trans_le ((le_max_right A 2).trans hx)
  let s := (primeBases x).filter (primeCutoff x < ·)
  have hs (p : ℕ) (hp : p ∈ s) : p.Prime ∧ L ^ 2 < (p : ℝ) ∧ (p : ℝ) ≤ exp L := by
    obtain ⟨hp', hpC⟩ := mem_filter.mp hp
    have hpx : p ≤ x := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp').1)
    obtain ⟨_, hpp⟩ := mem_filter.mp hp'
    refine ⟨hpp, (Nat.floor_lt (sq_nonneg L)).mp hpC, ?_⟩
    rw [show exp L = (x : ℝ) from Real.exp_log hxpos]
    exact_mod_cast hpx
  have h := hA L ((le_max_left A 2).trans hx) s hs
  dsimp only [L] at h
  simp_rw [Tail.phase_eq_residue] at h
  change ‖∑ p ∈ s, weight x p‖ ≤ C * ‖(Real.log L)⁻¹‖
  have hnonneg : 0 ≤ ∑ p ∈ s, weight x p := by
    refine sum_nonneg (fun p hp ↦ ?_)
    have hpp := (hs p hp).1.one_lt
    have hpp' : (1 : ℝ) < p := by exact_mod_cast hpp
    have hr : 0 ≤ residue x p := by
      rw [← Tail.phase_eq_residue]
      exact Tail.phase_nonneg (zero_lt_one.trans hL).le hpp
    unfold weight
    positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_nonneg (inv_nonneg.mpr (log_pos hL).le), ← div_eq_mul_inv]
  exact h

#print axioms primeTail_isBigO

end Erdos878

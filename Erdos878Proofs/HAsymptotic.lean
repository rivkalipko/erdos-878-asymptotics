module

public import Erdos878Proofs.Definitions
import Erdos878Proofs.HRegroup
import Erdos878Proofs.HTail
import PrimeNumberTheoremAnd.BrunTitchmarsh

/-! # The asymptotic equivalent for part (v) of Erdős Problem 878 -/

open Filter Asymptotics
open scoped Topology

namespace Erdos878

private lemma mem_primeBases {x p : ℕ} : p ∈ primeBases x ↔ p.Prime ∧ p ≤ x := by
  unfold primeBases
  simp [and_comm]

private lemma sum_log_le_card_primePowers (x : ℕ) :
    ∑ p ∈ primeBases x, Nat.log p x ≤ ((Finset.range (x + 1)).filter IsPrimePow).card := by
  classical
  let pairs : Finset (Σ _ : ℕ, ℕ) :=
    (primeBases x).sigma (fun p ↦ Finset.Icc 1 (Nat.log p x))
  have hc : pairs.card = ∑ p ∈ primeBases x, Nat.log p x := by
    simp [pairs, Finset.card_sigma, Nat.card_Icc]
  rw [← hc]
  apply Finset.card_le_card_of_injOn (fun z : Σ _ : ℕ, ℕ ↦ z.1 ^ z.2)
  · rintro ⟨p, k⟩ hz
    simp only [pairs, Finset.mem_coe, Finset.mem_sigma, mem_primeBases, Finset.mem_Icc] at hz
    have hpow : p ^ k ≤ x := Nat.pow_le_of_le_log (hz.1.1.pos.trans_le hz.1.2).ne' hz.2.2
    change p ^ k ∈ (Finset.range (x + 1)).filter IsPrimePow
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), (isPrimePow_nat_iff _).2 ⟨p, k, hz.1.1, hz.2.1, rfl⟩⟩
  · rintro ⟨p, j⟩ h₁ ⟨q, k⟩ h₂ he
    simp only [pairs, Finset.mem_coe, Finset.mem_sigma, mem_primeBases, Finset.mem_Icc] at h₁ h₂
    change p ^ j = q ^ k at he
    have hd : p ∣ q ^ k := he ▸ dvd_pow_self _ (by omega)
    have hpq : p = q := (Nat.dvd_prime h₂.1.1).mp (h₁.1.1.dvd_of_dvd_pow hd) |>.resolve_left h₁.1.1.ne_one
    subst q
    have hjk : j = k := (pow_right_strictMono₀ h₁.1.1.one_lt).injective he
    subst k
    rfl

private lemma regroup_error_isLittleO :
    (fun x : ℕ ↦ ∑ p ∈ primeBases x, ((Nat.log p x : ℝ) + 2)) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ)) := by
  have hsucc : Tendsto (fun x : ℕ ↦ x + 1) atTop atTop :=
    tendsto_atTop_mono (fun x ↦ Nat.le_succ x) tendsto_id
  have hp := BrunTitchmarsh.card_isPrimePow_isBigO.comp_tendsto hsucc
  have hl : (fun x : ℕ ↦ ((x + 1 : ℕ) : ℝ) / Real.log ((x + 1 : ℕ) : ℝ)) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ)) := by
    have hcast : Tendsto (fun x : ℕ ↦ ((x + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hsucc
    have hinv : (fun x : ℕ ↦ (Real.log ((x + 1 : ℕ) : ℝ))⁻¹) =o[atTop] (fun _ ↦ (1 : ℝ)) := by
      have ht := (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hcast))
      exact (isLittleO_one_iff ℝ).2 (by simpa [Function.comp_def] using ht)
    have hlin : (fun x : ℕ ↦ ((x + 1 : ℕ) : ℝ)) =O[atTop] (fun x : ℕ ↦ (x : ℝ)) := by
      apply Asymptotics.IsBigO.of_bound 2
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
      simp only [Real.norm_natCast, Nat.cast_add, Nat.cast_one]
      rw [Real.norm_of_nonneg (by positivity)]
      have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
      linarith
    simpa [div_eq_mul_inv] using hlin.mul_isLittleO hinv
  have hsum : (fun x : ℕ ↦ ∑ p ∈ primeBases x, ((Nat.log p x : ℝ) + 2)) =O[atTop]
      (fun x : ℕ ↦ (((Finset.range (x + 1)).filter IsPrimePow).card : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 3
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity), Real.norm_natCast]
    calc
      _ ≤ ∑ p ∈ primeBases x, 3 * (Nat.log p x : ℝ) := by
        apply Finset.sum_le_sum
        intro p hmem
        obtain ⟨hp', hpx⟩ := mem_primeBases.mp hmem
        have hle : 1 ≤ Nat.log p x := Nat.log_pos_iff.mpr ⟨hpx, hp'.one_lt⟩
        have : (1 : ℝ) ≤ Nat.log p x := by exact_mod_cast hle
        linarith
      _ ≤ _ := by
        rw [← Finset.mul_sum, ← Nat.cast_sum]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast sum_log_le_card_primePowers x) (by norm_num)
  exact hsum.trans_isLittleO (hp.trans_isLittleO hl)

private lemma residue_bounds {x p : ℕ} (hp : p.Prime) (hpx : p ≤ x) :
    0 ≤ residue x p ∧ residue x p < Real.log p := by
  have hx : 0 < x := hp.pos.trans_le hpx
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hl := Nat.pow_log_le_self p hx.ne'
  have hu := Nat.lt_pow_succ_log_self hp.one_lt x
  have hl' : (p : ℝ) ^ Nat.log p x ≤ x := by exact_mod_cast hl
  have hu' : (x : ℝ) < (p : ℝ) ^ (Nat.log p x + 1) := by exact_mod_cast hu
  have ha := Real.log_le_log (by positivity) hl'
  have hb := Real.log_lt_log (by exact_mod_cast hx) hu'
  rw [Real.log_pow] at ha hb
  push_cast at ha hb
  unfold residue
  constructor <;> linarith

private lemma eventually_cutoff_bounds : ∀ᶠ x : ℕ in atTop, 2 ≤ primeCutoff x ∧ primeCutoff x ≤ x := by
  have ht := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog := (isLittleO_log_rpow_atTop (show 0 < (1 / 2 : ℝ) by norm_num)).comp_tendsto
    (show Tendsto (fun x : ℕ ↦ (x : ℝ)) atTop atTop from tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually (eventually_ge_atTop (2 : ℝ)), hlog.bound (by norm_num : (0 : ℝ) < 1)] with x hx h
  change 2 ≤ Real.log (x : ℝ) at hx
  have hpos : 0 ≤ Real.log (x : ℝ) := by linarith
  simp only [Function.comp_apply, Real.norm_eq_abs, one_mul, ← Real.sqrt_eq_rpow,
    abs_of_nonneg hpos, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  unfold primeCutoff
  constructor
  · apply (Nat.le_floor_iff (by positivity)).2
    norm_num
    nlinarith
  · exact_mod_cast (Nat.floor_le (sq_nonneg (Real.log (x : ℝ)))).trans
      (calc Real.log (x : ℝ) ^ 2 ≤ Real.sqrt x ^ 2 := by gcongr
            _ = (x : ℝ) := Real.sq_sqrt (by positivity))

private lemma id_isBigO_harmonicAnswer :
    (fun x : ℕ ↦ (x : ℝ)) =O[atTop] harmonicAnswer := by
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply Asymptotics.IsBigO.of_bound (4 / Real.log 2)
  filter_upwards [eventually_cutoff_bounds] with x hx
  have ht : 2 ∈ primeBases (primeCutoff x) := mem_primeBases.mpr ⟨Nat.prime_two, hx.1⟩
  have hn : ∀ p ∈ primeBases (primeCutoff x), 0 ≤ weight x p := by
    intro p hp
    obtain ⟨hpp, hpx⟩ := mem_primeBases.mp hp
    have hp₀ : 0 < (p : ℝ) := by exact_mod_cast hpp.pos
    have hp₁ : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hr := (residue_bounds hpp (hpx.trans hx.2)).1
    unfold weight
    positivity
  have hr := residue_bounds Nat.prime_two (hx.1.trans hx.2)
  have hres : residue x 2 < Real.log 2 := by exact_mod_cast hr.2
  have hexp : (1 / 2 : ℝ) ≤ Real.exp (-residue x 2) := by
    have hl := Real.exp_le_exp.mpr (show -Real.log 2 ≤ -residue x 2 by linarith)
    rwa [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), inv_eq_one_div] at hl
  have htwo : Real.log 2 / 4 ≤ weight x 2 := by
    unfold weight
    norm_num
    calc
      Real.log 2 / 4 = ((1 / 2 : ℝ) / 2) * Real.log 2 := by ring
      _ ≤ _ := by gcongr; linarith [hr.1]
  have hsum : (x : ℝ) * (Real.log 2 / 4) ≤ harmonicAnswer x := by
    unfold harmonicAnswer
    exact mul_le_mul_of_nonneg_left (htwo.trans (Finset.single_le_sum hn ht)) (by positivity)
  have hnonneg : 0 ≤ harmonicAnswer x := le_trans (by positivity) hsum
  rw [Real.norm_natCast, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog₂]
  linarith

/-- The truncated prime sum is an asymptotic equivalent for the average in part (v). -/
public theorem part_v : H ~[atTop] harmonicAnswer := by
  change (H - harmonicAnswer) =o[atTop] harmonicAnswer
  apply IsLittleO.trans_isBigO _ id_isBigO_harmonicAnswer
  let full (x : ℕ) : ℝ := (x : ℝ) * ∑ p ∈ primeBases x, weight x p
  have hregroup : (H - full) =o[atTop] (fun x : ℕ ↦ (x : ℝ)) := by
    apply IsBigO.trans_isLittleO _ regroup_error_isLittleO
    apply isBigO_of_le
    intro x
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    exact (abs_H_sub_weight_le x).trans (le_abs_self _)
  have hinv : (fun x : ℕ ↦ (Real.log (Real.log (x : ℝ)))⁻¹) =o[atTop]
      (fun _ : ℕ ↦ (1 : ℝ)) := by
    have ht := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact (isLittleO_one_iff ℝ).2 (by simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp ht)
  have htail := (isBigO_refl (fun x : ℕ ↦ (x : ℝ)) atTop).mul_isLittleO
    (primeTail_isBigO.trans_isLittleO hinv)
  have heq : (full - harmonicAnswer) =ᶠ[atTop]
      (fun x : ℕ ↦ (x : ℝ) * ∑ p ∈ (primeBases x).filter (primeCutoff x < ·), weight x p) := by
    classical
    filter_upwards [eventually_cutoff_bounds] with x hx
    have hfilter : (primeBases x).filter (fun p ↦ ¬primeCutoff x < p) = primeBases (primeCutoff x) := by
      ext p
      simp only [Finset.mem_filter, mem_primeBases, not_lt]
      exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.trans hx.2⟩, h.2⟩⟩
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := primeBases x)
      (p := (primeCutoff x < ·)) (f := weight x)
    rw [hfilter] at hsplit
    simp only [Pi.sub_apply, full, harmonicAnswer]
    rw [← hsplit]
    ring
  have hadd : (fun x ↦ (H - full) x + (full - harmonicAnswer) x) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ)) := by
    apply hregroup.add
    simpa using (htail.congr' heq.symm EventuallyEq.rfl)
  change (fun x ↦ H x - harmonicAnswer x) =o[atTop] (fun x : ℕ ↦ (x : ℝ))
  simpa [sub_add_sub_cancel] using hadd

end Erdos878

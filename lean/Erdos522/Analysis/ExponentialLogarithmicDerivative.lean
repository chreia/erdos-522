/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.CauchySums
import Erdos522.Analysis.ExponentialPotential
import Erdos522.Analysis.ExponentialPruning
import Erdos522.Analysis.MultiplicityLabels

/-!
# Weak bounds for logarithmic derivatives of exponential polynomials

The zeros in a fixed disk give a finite Cauchy sum. Blaschke factorization
bounds the remaining logarithmic derivative by the spectral radius and the
number of terms. The weak Cauchy estimate then controls logarithmic derivatives
and normalized differential pruning on a unit interval.
-/

noncomputable section

open Complex MeasureTheory MeromorphicOn Metric Set
open scoped BigOperators

namespace Erdos522

/-- Adding a bounded term to a finite Cauchy sum preserves a weak first-order
    estimate on a set of measure at most one. -/
theorem measure_norm_le_cauchySum_add_bound {ι : Type*} [Fintype ι]
    (poles : ι → ℂ) {g : ℝ → ℂ} {s : Set ℝ} {B u : ℝ}
    (hs : volume s ≤ 1) (hB : 0 ≤ B) (hu : 0 < u)
    (hg : ∀ x ∈ s, ‖g x‖ ≤ ‖CauchySums.cauchySum poles (x : ℂ)‖ + B) :
    volume {x : ℝ | x ∈ s ∧ u ≤ ‖g x‖} ≤
      ENNReal.ofReal ((32 * Fintype.card ι + 2 * B) / u) := by
  by_cases huB : u ≤ 2 * B
  · calc
      _ ≤ volume s := measure_mono (fun _ hx ↦ hx.1)
      _ ≤ 1 := hs
      _ ≤ _ := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        apply (le_div_iff₀ hu).mpr
        have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
        nlinarith
  · have hBu : 2 * B < u := lt_of_not_ge huB
    calc
      _ ≤ volume {x : ℝ | u / 2 ≤ ‖CauchySums.cauchySum poles (x : ℂ)‖} := by
        apply measure_mono
        intro x hx
        have h := hg x hx.1
        change u / 2 ≤ ‖CauchySums.cauchySum poles (x : ℂ)‖
        linarith [hx.2]
      _ ≤ ENNReal.ofReal (16 * Fintype.card ι / (u / 2)) :=
        CauchySums.measure_cauchySum_levelset_global_le poles (by positivity)
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [show 16 * (Fintype.card ι : ℝ) / (u / 2) =
          32 * Fintype.card ι / u by ring]
        exact div_le_div_of_nonneg_right (by linarith) hu.le

/-- The interior zeros give a finite pole family of linear cardinality; the
    remaining logarithmic derivative has an explicit linear bound. -/
theorem exists_complexExponentialSum_logDeriv_pole_bound {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ)
    (hne : complexExponentialSum s c ζ ≠ 0) {σ : ℝ}
    (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, ‖ζ j‖ ≤ σ) :
    ∃ N : ℕ, ∃ poles : Fin N → ℂ,
      (N : ℝ) ≤ 48 * σ + 18 * ((s.card : ℝ) - 1) ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → complexExponentialSum s c ζ z ≠ 0 →
        ‖logDeriv (complexExponentialSum s c ζ) z‖ ≤
          ‖CauchySums.cauchySum poles z‖ +
            (816 * σ + 1206 * ((s.card : ℝ) - 1)) := by
  let f := complexExponentialSum s c ζ
  have hf := analyticOnNhd_complexExponentialSum s c ζ
  let Z := (hf.meromorphicOn.mono_set
    (subset_univ (closedBall (0 : ℂ) 4))).divisor_ball_support_finite.toFinset
  let n := fun z ↦ (divisor f (ball 0 4) z).toNat
  let N := multiplicityLabelCount Z n
  let poles := multiplicityLabel Z n
  have hmass : (∑ z ∈ Z, (n z : ℝ)) ≤ 48 * σ + 18 * ((s.card : ℝ) - 1) :=
    interior_four_zero_mass_complexExponentialSum_le s hs c ζ hne hσ hζ
  have hN : (N : ℝ) = ∑ z ∈ Z, (n z : ℝ) := by
    dsimp only [N]
    rw [multiplicityLabelCount_eq_sum, Nat.cast_sum]
  have hpoles (z : ℂ) : CauchySums.cauchySum poles z =
      ∑ w ∈ Z, (n w : ℂ) / (z - w) := by
    dsimp only [CauchySums.cauchySum, poles]
    simpa only [nsmul_eq_mul, div_eq_mul_inv] using
      sum_multiplicityLabel Z n (fun w : ℂ ↦ (z - w)⁻¹)
  have hm : 1 ≤ (s.card : ℝ) := by exact_mod_cast Finset.one_le_card.mpr hs
  have hlog32 : Real.log (32 * Real.exp 1) ≤ 6 := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp,
      show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
    linarith
  let M₁ := diskNorm f 0 1
  have hM₁ : 0 < M₁ := diskNorm_pos_of_entire hf hne 0 (by norm_num)
  let M := Real.exp (4 * σ) * M₁ * (32 * Real.exp 1) ^ (s.card - 1)
  have hM : 0 < M := by dsimp [M]; positivity
  have hbound : ∀ z ∈ sphere (0 : ℂ) 4, ‖f z‖ ≤ M := by
    intro z hz
    have h := norm_complexExponentialSum_le_disk_universal s hs c ζ hσ hζ
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 4) hM₁.le 0 z
      (fun w hw ↦ norm_le_diskNorm (hf.continuousOn.mono (subset_univ _)) hw)
      (sphere_subset_closedBall hz)
    simpa only [M, mul_one, div_one, show 8 * Real.exp 1 * 4 = 32 * Real.exp 1 by ring,
      show σ * 4 = 4 * σ by ring] using h
  have hgrowth : Real.log (M / diskNorm f 0 1) ≤
      4 * σ + 6 * ((s.card : ℝ) - 1) := by
    have heq : M / diskNorm f 0 1 =
        Real.exp (4 * σ) * (32 * Real.exp 1) ^ (s.card - 1) := by
      dsimp [M, M₁]
      field_simp [hM₁.ne']
      exact div_self hM₁.ne'
    rw [heq, Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ (by positivity)),
      Real.log_exp, Real.log_pow, Nat.cast_sub (Finset.one_le_card.mpr hs), Nat.cast_one]
    nlinarith
  refine ⟨N, poles, hN.trans_le hmass, fun z hz hfz ↦ ?_⟩
  have hb := norm_logDeriv_le_pole_sum_add_growth hf hne (R := 4) (r := 1)
    (by norm_num) (by norm_num) hM hbound hgrowth (mem_closedBall_zero_iff.mpr hz) hfz
  change ‖logDeriv f z‖ ≤ ‖∑ w ∈ Z, (n w : ℂ) / (z - w)‖ +
    (∑ w ∈ Z, (n w : ℝ)) / (4 - 1) +
    200 * (4 * σ + 6 * ((s.card : ℝ) - 1)) / 1 at hb
  rw [hpoles]
  nlinarith

/-- A nonzero exponential polynomial has a weak logarithmic-derivative bound
    linear in its spectral radius and number of terms. -/
theorem measure_complexExponentialSum_logDeriv_levelset_le {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ)
    (hne : complexExponentialSum s c ζ ≠ 0) {σ u : ℝ}
    (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, ‖ζ j‖ ≤ σ) (hu : 0 < u) :
    volume {x : ℝ | x ∈ Icc (-1 / 2) (1 / 2) ∧
      complexExponentialSum s c ζ (x : ℂ) ≠ 0 ∧
      u ≤ ‖logDeriv (complexExponentialSum s c ζ) (x : ℂ)‖} ≤
      ENNReal.ofReal (4096 * ((s.card : ℝ) + σ) / u) := by
  obtain ⟨N, poles, hN, hp⟩ :=
    exists_complexExponentialSum_logDeriv_pole_bound s hs c ζ hne hσ hζ
  let S := {x : ℝ | x ∈ Icc (-1 / 2) (1 / 2) ∧
    complexExponentialSum s c ζ (x : ℂ) ≠ 0}
  have hS : volume S ≤ 1 := by
    calc
      _ ≤ volume (Icc (-1 / 2 : ℝ) (1 / 2)) := measure_mono (fun _ hx ↦ hx.1)
      _ = 1 := by rw [Real.volume_Icc]; norm_num
  have hm : 1 ≤ (s.card : ℝ) := by exact_mod_cast Finset.one_le_card.mpr hs
  have hb := measure_norm_le_cauchySum_add_bound poles (s := S)
    (g := fun x : ℝ ↦ logDeriv (complexExponentialSum s c ζ) (x : ℂ)) hS
    (B := 816 * σ + 1206 * ((s.card : ℝ) - 1)) (by positivity) hu (by
      intro x hx
      apply hp x ?_ hx.2
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩)
  have heq : {x : ℝ | x ∈ Icc (-1 / 2) (1 / 2) ∧
      complexExponentialSum s c ζ (x : ℂ) ≠ 0 ∧
      u ≤ ‖logDeriv (complexExponentialSum s c ζ) (x : ℂ)‖} =
      {x : ℝ | x ∈ S ∧ u ≤ ‖logDeriv (complexExponentialSum s c ζ) (x : ℂ)‖} := by
    ext x
    exact and_assoc.symm
  rw [heq]
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  apply div_le_div_of_nonneg_right _ hu.le
  simp only [Fintype.card_fin]
  nlinarith

/-- At a nonzero value, shifting the chosen frequency to zero identifies the
    pruning quotient with the normalized logarithmic derivative. -/
theorem exponentialPruning_div_eq_shifted_logDeriv {ι : Type*}
    (s : Finset ι) (c ζ : ι → ℂ) (a : ℂ) (ρ : ℝ) (z : ℂ)
    (hz : complexExponentialSum s c ζ z ≠ 0) :
    exponentialPruning s c ζ a ρ z / complexExponentialSum s c ζ z =
      logDeriv (complexExponentialSum s c (fun j ↦ ζ j - a)) z / (ρ : ℂ) := by
  have hshift : complexExponentialSum s c (fun j ↦ ζ j - a) z ≠ 0 := by
    intro h
    apply hz
    rw [complexExponentialSum_spectral_shift s c ζ a, h, mul_zero]
  rw [exponentialPruning_spectral_shift s c ζ a a,
    complexExponentialSum_spectral_shift s c ζ a, mul_div_mul_left _ _ (Complex.exp_ne_zero _),
    sub_self, exponentialPruning_div _ _ _ _ _ _ hshift]
  simp only [sub_zero, logDeriv_apply]

/-- When the spectrum lies within distance `ρ` of the pruned frequency and
    `ρ` dominates the term count, the pruning quotient has a universal weak bound. -/
theorem measure_exponentialPruning_quotient_levelset_le {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ) (a : ℂ)
    (hne : complexExponentialSum s c ζ ≠ 0) {ρ u : ℝ}
    (hρ : 0 < ρ) (hmρ : (s.card : ℝ) ≤ ρ)
    (hζ : ∀ j ∈ s, ‖ζ j - a‖ ≤ ρ) (hu : 0 < u) :
    volume {x : ℝ | x ∈ Icc (-1 / 2) (1 / 2) ∧
      complexExponentialSum s c ζ (x : ℂ) ≠ 0 ∧
      u ≤ ‖exponentialPruning s c ζ a ρ (x : ℂ)‖ /
        ‖complexExponentialSum s c ζ (x : ℂ)‖} ≤ ENNReal.ofReal (8192 / u) := by
  have hshift : complexExponentialSum s c (fun j ↦ ζ j - a) ≠ 0 := by
    intro h
    apply hne
    funext z
    rw [complexExponentialSum_spectral_shift s c ζ a, h]
    simp
  have hw := measure_complexExponentialSum_logDeriv_levelset_le s hs c
    (fun j ↦ ζ j - a) hshift hρ.le hζ (mul_pos hu hρ)
  have hsub : {x : ℝ | x ∈ Icc (-1 / 2) (1 / 2) ∧
      complexExponentialSum s c ζ (x : ℂ) ≠ 0 ∧
      u ≤ ‖exponentialPruning s c ζ a ρ (x : ℂ)‖ /
        ‖complexExponentialSum s c ζ (x : ℂ)‖} ⊆
      {x : ℝ | x ∈ Icc (-1 / 2) (1 / 2) ∧
        complexExponentialSum s c (fun j ↦ ζ j - a) (x : ℂ) ≠ 0 ∧
        u * ρ ≤ ‖logDeriv (complexExponentialSum s c (fun j ↦ ζ j - a)) (x : ℂ)‖} := by
    intro x hx
    have hfx : complexExponentialSum s c (fun j ↦ ζ j - a) (x : ℂ) ≠ 0 := by
      intro h
      apply hx.2.1
      rw [complexExponentialSum_spectral_shift s c ζ a, h, mul_zero]
    refine ⟨hx.1, hfx, ?_⟩
    have heq := congrArg norm (exponentialPruning_div_eq_shifted_logDeriv s c ζ a ρ x hx.2.1)
    rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] at heq
    have hxq := hx.2.2
    rw [heq] at hxq
    exact (le_div_iff₀ hρ).mp hxq
  refine (measure_mono hsub).trans (hw.trans (ENNReal.ofReal_le_ofReal ?_))
  apply (div_le_div_iff₀ (mul_pos hu hρ) hu).mpr
  nlinarith

end Erdos522

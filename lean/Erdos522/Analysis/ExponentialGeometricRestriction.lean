/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ExponentialPotential
import Erdos522.Analysis.PotentialRestriction

/-!
# Geometric restriction for bounded exponential spectra

The zeros of an exponential polynomial give an effective logarithmic
potential of degree one less than its number of terms. Integrating this
potential on a measurable real set yields a geometric-mean restriction
inequality with that same exponent.
-/

noncomputable section

open MeasureTheory MeromorphicOn Metric Set
open scoped BigOperators ENNReal

namespace Erdos522

/-- The real zeros of a nonzero entire function in a bounded interval form a
finite set. -/
theorem finite_real_zeros_of_entire {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : f ≠ 0) (R : ℝ) :
    {x : ℝ | |x| ≤ R ∧ f x = 0}.Finite := by
  have hs := (divisor f (closedBall (0 : ℂ) R)).finiteSupport (isCompact_closedBall _ _)
  have hp : (Complex.ofReal ⁻¹' (divisor f (closedBall (0 : ℂ) R)).support).Finite :=
    Set.Finite.preimage Complex.ofReal_injective.injOn hs
  apply hp.subset
  rintro x ⟨hx, hfx⟩
  change divisor f (closedBall (0 : ℂ) R) (x : ℂ) ≠ 0
  rw [divisor_eq_analyticOrderNatAt hf hne (by
    simpa only [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hx)]
  intro ho
  have hn : analyticOrderNatAt f (x : ℂ) = 0 := by exact_mod_cast ho
  have ht := Nat.cast_analyticOrderNatAt (analyticOrderAt_ne_top_of_entire hf hne x)
  rw [hn, Nat.cast_zero] at ht
  exact ((hf x (mem_univ _)).analyticOrderAt_eq_zero.mp ht.symm) hfx

/-- Restricting a nonzero entire function to a bounded measurable real set
preserves almost-everywhere nonvanishing. -/
theorem ae_ne_zero_of_entire_on_real_set {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : f ≠ 0) (E : Set ℝ)
    (hE : MeasurableSet E) {R : ℝ} (hsub : ∀ x ∈ E, |x| ≤ R) :
    ∀ᵐ x : ℝ ∂volume.restrict E, f (x : ℂ) ≠ 0 := by
  have hnull := (finite_real_zeros_of_entire hf hne R).measure_zero (μ := volume)
  have hae : ∀ᵐ x : ℝ ∂volume, ¬ (|x| ≤ R ∧ f x = 0) := ae_iff.mpr (by simpa using hnull)
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hE] with x hx hxE hfx
  exact hx ⟨hsub x hxE, hfx⟩

/-- A nonzero exponential polynomial is nonzero almost everywhere on every
measurable subset of the centered unit interval. -/
theorem ae_complexExponentialSum_ne_zero {ι : Type*}
    (s : Finset ι) (c ζ : ι → ℂ) (hne : complexExponentialSum s c ζ ≠ 0)
    (E : Set ℝ) (hE : MeasurableSet E)
    (hsub : E ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    ∀ᵐ x : ℝ ∂volume.restrict E, complexExponentialSum s c ζ (x : ℂ) ≠ 0 :=
  ae_ne_zero_of_entire_on_real_set (analyticOnNhd_complexExponentialSum s c ζ)
    hne E hE (fun _ hx => abs_le.mpr (hsub hx))

/-- The logarithm of the modulus of a nonzero exponential polynomial is
integrable on every measurable subset of the centered unit interval. -/
theorem integrableOn_log_norm_complexExponentialSum {ι : Type*}
    (s : Finset ι) (c ζ : ι → ℂ) (hne : complexExponentialSum s c ζ ≠ 0)
    (E : Set ℝ) (hE : MeasurableSet E)
    (hsub : E ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    IntegrableOn (fun x : ℝ => Real.log ‖complexExponentialSum s c ζ (x : ℂ)‖) E := by
  classical
  have hs : s.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    apply hne
    funext z
    simp [he, complexExponentialSum]
  let σ : ℝ := ∑ j ∈ s, ‖ζ j‖
  have hσ : 0 ≤ σ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hζ : ∀ j ∈ s, ‖ζ j‖ ≤ σ := fun j hj =>
    Finset.single_le_sum (fun _ _ => norm_nonneg _) hj
  obtain ⟨N, w, _, hdef, _⟩ :=
    exists_complexExponentialSum_zero_potential_labels s hs c ζ hne hσ hζ
  have hf := analyticOnNhd_complexExponentialSum s c ζ
  have hfm : Measurable (fun x : ℝ => complexExponentialSum s c ζ (x : ℂ)) :=
    (hf.continuous.comp Complex.continuous_ofReal).measurable
  have hfinite : volume E ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hsub)
  have hnz := ae_complexExponentialSum_ne_zero s c ζ hne E hE hsub
  apply integrable_log_norm_of_potential_bounds w N E hfinite _ hfm
    (Real.log (diskNorm (complexExponentialSum s c ζ) 0 1))
    (25 * (4 * σ + ((s.card : ℝ) - 1) * Real.log (32 * Real.exp 1)) + N * Real.log 5)
  · filter_upwards [ae_restrict_mem hE, hnz] with x hx hfx
    apply Real.log_le_log (norm_pos_iff.mpr hfx)
    apply norm_le_diskNorm (hf.continuousOn.mono (subset_univ _))
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_le.mpr (hsub hx)).trans (by norm_num)
  · filter_upwards [ae_restrict_mem hE, hnz] with x hx hfx
    exact (hdef x ((abs_le.mpr (hsub hx)).trans (by norm_num)) hfx).trans
      (add_le_add (le_refl _) (sum_negativeLogPotential_le_largest w N Finset.univ
        (by simp) x))

/-- A convenient linear majorant for a logarithmic growth constant. -/
theorem log_mul_exp_one_le {a : ℝ} (ha : 0 < a) :
    Real.log (a * Real.exp 1) ≤ a := by
  rw [Real.log_mul ha.ne' (Real.exp_ne_zero _), Real.log_exp]
  linarith [Real.log_le_sub_one_of_pos ha]

/-- When the spectral radius is at most the number of terms, all zero-count
and disk-growth costs are bounded by a universal multiple of the effective
degree. -/
theorem exponential_potential_cost_le {m N : ℕ} {σ : ℝ}
    (hm : 2 ≤ m) (hσm : σ ≤ m)
    (hN : (N : ℝ) ≤ 48 * σ + 18 * ((m : ℝ) - 1)) :
    25 * (4 * σ + ((m : ℝ) - 1) * Real.log (32 * Real.exp 1)) +
      N * Real.log 5 + (5 * σ + ((m : ℝ) - 1) * Real.log (40 * Real.exp 1)) +
        2 * N ≤ 2000 * (m - 1 : ℕ) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : 0 ≤ (m : ℝ) - 1 := by linarith
  have h32 := mul_le_mul_of_nonneg_left (log_mul_exp_one_le (by norm_num : (0 : ℝ) < 32)) hd
  have h40 := mul_le_mul_of_nonneg_left (log_mul_exp_one_le (by norm_num : (0 : ℝ) < 40)) hd
  have h5 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)) (Nat.cast_nonneg N)
  rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  nlinarith

/-- An exponential polynomial whose spectral radius is at most its number
of terms satisfies a geometric restriction inequality with exponent `m-1`.
The spectrum may be complex and need not consist of distinct points. -/
theorem norm_complexExponentialSum_le_geometricMean_of_bounded_spectrum {ι : Type*}
    (s : Finset ι) (hs₂ : 2 ≤ s.card) (c ζ : ι → ℂ)
    (hne : complexExponentialSum s c ζ ≠ 0) {σ : ℝ}
    (hσ : 0 ≤ σ) (hσm : σ ≤ (s.card : ℝ)) (hζ : ∀ j ∈ s, ‖ζ j‖ ≤ σ)
    (E : Set ℝ) (hE : MeasurableSet E)
    (hsub : E ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (hpos : 0 < volume.real E)
    (x : ℝ) (hx : |x| ≤ 1 / 2) :
    ‖complexExponentialSum s c ζ (x : ℂ)‖ ≤
      (Real.exp 2000 / volume.real E) ^ (s.card - 1) *
        geometricMean (volume.restrict E)
          (fun y : ℝ => complexExponentialSum s c ζ (y : ℂ)) := by
  have hs : s.Nonempty := Finset.card_pos.mp (by omega)
  have hf := analyticOnNhd_complexExponentialSum s c ζ
  have hfm : Measurable (fun y : ℝ => complexExponentialSum s c ζ (y : ℂ)) :=
    (hf.continuous.comp Complex.continuous_ofReal).measurable
  have hfinite : volume E ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hsub)
  have hle : volume.real E ≤ 1 := by
    calc
      volume.real E ≤ volume.real (Icc (-(1 / 2 : ℝ)) (1 / 2)) := measureReal_mono hsub (by simp)
      _ = 1 := by norm_num
  have hcast : ((s.card - 1 : ℕ) : ℝ) = (s.card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ s.card), Nat.cast_one]
  have hd : 0 ≤ (s.card : ℝ) - 1 := by rw [← hcast]; positivity
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hH : 0 ≤ 5 * σ + ((s.card : ℝ) - 1) * Real.log (40 * Real.exp 1) :=
    add_nonneg (mul_nonneg (by norm_num) hσ)
      (mul_nonneg hd (Real.log_nonneg (by nlinarith)))
  obtain ⟨N, w, hN, hdef, hclip⟩ :=
    exists_complexExponentialSum_zero_potential_labels s hs c ζ hne hσ hζ
  let S := 25 * (4 * σ + ((s.card : ℝ) - 1) * Real.log (32 * Real.exp 1)) +
    N * Real.log 5 + (5 * σ + ((s.card : ℝ) - 1) * Real.log (40 * Real.exp 1))
  have hnz := ae_complexExponentialSum_ne_zero s c ζ hne E hE hsub
  have hupper : ∀ᵐ y : ℝ ∂volume.restrict E,
      Real.log ‖complexExponentialSum s c ζ (y : ℂ)‖ ≤
        Real.log (diskNorm (complexExponentialSum s c ζ) 0 1) := by
    filter_upwards [ae_restrict_mem hE, hnz] with y hy hfy
    apply Real.log_le_log (norm_pos_iff.mpr hfy)
    apply norm_le_diskNorm (hf.continuousOn.mono (subset_univ _))
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_le.mpr (hsub hy)).trans (by norm_num)
  have hpot : ∀ᵐ y : ℝ ∂volume.restrict E,
      Real.log (diskNorm (complexExponentialSum s c ζ) 0 1) -
        Real.log ‖complexExponentialSum s c ζ (y : ℂ)‖ ≤
          S + largestLogarithmicPotential w (s.card - 1) y := by
    filter_upwards [ae_restrict_mem hE, hnz] with y hy hfy
    have hy' := abs_le.mpr (hsub hy)
    have hc := sum_negativeLogPotential_le_largest_add w
      (by omega : 0 < s.card - 1) hH y (fun T hT => by
        rw [hcast]
        exact hclip y hy' hfy T hT)
    have hb := hdef y (hy'.trans (by norm_num)) hfy
    dsimp [S]
    linarith
  have hrestriction := geometric_restriction_of_potential_bound w (s.card - 1)
    E hfinite hpos hle _ hfm (Real.log (diskNorm (complexExponentialSum s c ζ) 0 1))
    S hupper hpot
  rw [Real.exp_log (diskNorm_pos_of_entire hf hne 0 (by norm_num))] at hrestriction
  have hcost : Real.exp (S + 2 * N) ≤ (Real.exp 2000) ^ (s.card - 1) := by
    have h := Real.exp_le_exp.mpr (exponential_potential_cost_le hs₂ hσm hN)
    rw [mul_comm (2000 : ℝ), Real.exp_nat_mul] at h
    exact h
  have hnorm : ‖complexExponentialSum s c ζ (x : ℂ)‖ ≤
      diskNorm (complexExponentialSum s c ζ) 0 1 := by
    apply norm_le_diskNorm (hf.continuousOn.mono (subset_univ _))
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact hx.trans (by norm_num)
  refine hnorm.trans (hrestriction.trans ?_)
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcost (by positivity : 0 ≤ (1 / volume.real E) ^ (s.card - 1)))
    (geometricMean_pos (volume.restrict E)
      (fun y : ℝ => complexExponentialSum s c ζ (y : ℂ))).le
  simpa only [← mul_pow, div_eq_mul_inv, one_mul] using hm

end Erdos522

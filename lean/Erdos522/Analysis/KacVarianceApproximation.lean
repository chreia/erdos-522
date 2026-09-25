/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.LogarithmicRadiusBounds
import Erdos522.Analysis.KacVarianceIntegral

/-!
# Finite approximation of the radial variance profile

Comparing the sampled and continuum exponents multiplicatively avoids
losses near the inside edge of a growing annulus. The constant coefficient
contributes a separate relative error of at most `exp(2K)/N`.
-/

noncomputable section
open MeasureTheory Set
namespace Erdos522

/-- Multiplicative comparison of the sampled radial variance and its profile. -/
theorem radialVariance_profile_comparison {N : ℕ} (hN : 0 < N) {K x : ℝ}
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N) (hx : |x| ≤ K) :
    Real.exp (-(2 * (K ^ 2 + K) / N)) * kacVarianceProfile x ≤
        radialVariance N (1 + x / N) / N ∧
      radialVariance N (1 + x / N) / N ≤
        Real.exp (2 * (K ^ 2 + K) / N) * kacVarianceProfile x + 1 / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < 1 + x / N := by
    have hu : -(1 / 2 : ℝ) ≤ x / N := (le_div_iff₀ hn).mpr (by have := (abs_le.mp hx).1; linarith)
    linarith
  let δ := 2 * (K ^ 2 + K) / N
  let f := fun t : ℝ => Real.exp (2 * x * t)
  let g := fun t : ℝ => Real.exp (2 * ((N : ℝ) * Real.log (1 + x / N)) * rightEndpointSample N t)
  have hf : Integrable f unitIntervalMeasure := integrable_kac_exponential x
  have hg : Integrable g unitIntervalMeasure :=
    integrableOn_rightEndpointSample hN (fun t => Real.exp (2 * ((N : ℝ) * Real.log (1 + x / N)) * t))
  have hpoint : ∀ᵐ t ∂unitIntervalMeasure,
      Real.exp (-δ) * f t ≤ g t ∧ g t ≤ Real.exp δ * f t := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    have h := abs_le.mp (abs_sampled_radial_exponent_sub_le hN hK hNK hx ht)
    constructor
    · change Real.exp (-δ) * Real.exp (2 * x * t) ≤ _
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by dsimp [δ, g]; linarith [h.1])
    · change _ ≤ Real.exp δ * Real.exp (2 * x * t)
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by dsimp [δ, g]; linarith [h.2])
  have hlo := integral_mono_ae (hf.const_mul (Real.exp (-δ))) hg (hpoint.mono (fun _ h => h.1))
  have hhi := integral_mono_ae hg (hf.const_mul (Real.exp δ)) (hpoint.mono (fun _ h => h.2))
  rw [integral_const_mul] at hlo hhi
  have hprofile : (∫ t, f t ∂unitIntervalMeasure) = kacVarianceProfile x :=
    (kacVarianceProfile_eq_integral x).symm
  rw [hprofile] at hlo hhi
  rw [radialVariance_eq_sampled_integral hN hr]
  exact ⟨by dsimp [δ, g] at hlo; linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hn.le],
    by dsimp [δ, g] at hhi; linarith⟩

/-- Relative exponential bounds give a logarithmic error with a linear
contribution from an additional nonnegative relative mass. -/
theorem abs_log_sub_le_of_exponential_bounds {a b δ E : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 ≤ δ) (hE : 0 ≤ E)
    (hlo : Real.exp (-δ) * b ≤ a) (hhi : a ≤ Real.exp δ * b + E * b) :
    |Real.log a - Real.log b| ≤ δ + E := by
  have hupper : a ≤ Real.exp (δ + E) * b := by
    have hd : 1 ≤ Real.exp δ := Real.one_le_exp_iff.mpr hδ
    have he : 1 + E ≤ Real.exp E := by linarith [Real.add_one_le_exp E]
    calc
      a ≤ (Real.exp δ + E) * b := by nlinarith only [hhi]
      _ ≤ (Real.exp δ * (1 + E)) * b := by
        apply mul_le_mul_of_nonneg_right _ hb.le
        nlinarith [mul_nonneg hE (sub_nonneg.mpr hd)]
      _ ≤ (Real.exp δ * Real.exp E) * b :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (Real.exp_nonneg _)) hb.le
      _ = Real.exp (δ + E) * b := by rw [Real.exp_add]
  have hl := Real.log_le_log (mul_pos (Real.exp_pos _) hb) hlo
  have hu := Real.log_le_log ha hupper
  rw [Real.log_mul (Real.exp_ne_zero _) hb.ne', Real.log_exp] at hl hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A finite-degree logarithmic variance estimate, uniform over the whole width. -/
theorem abs_log_radialVariance_profile_le {N : ℕ} (hN : 0 < N) {K x : ℝ}
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N) (hx : |x| ≤ K) :
    |Real.log (radialVariance N (1 + x / N) / N) - Real.log (kacVarianceProfile x)| ≤
      (2 * (K ^ 2 + K) + Real.exp (2 * K)) / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h := radialVariance_profile_comparison hN hK hNK hx
  have hv := exp_neg_two_width_le_kacVarianceProfile hK hx
  have he : Real.exp (2 * K) * Real.exp (-2 * K) = 1 := by
    rw [← Real.exp_add]
    simp
  have hconstant : 1 / (N : ℝ) ≤ (Real.exp (2 * K) / N) * kacVarianceProfile x := by
    calc
      _ = (Real.exp (2 * K) / N) * Real.exp (-2 * K) := by rw [div_mul_eq_mul_div, he]
      _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
  have hlog := abs_log_sub_le_of_exponential_bounds
    (div_pos (radialVariance_pos N _) hn) (kacVarianceProfile_pos x)
    (show 0 ≤ 2 * (K ^ 2 + K) / N by positivity)
    (show 0 ≤ Real.exp (2 * K) / N by positivity) h.1
    (h.2.trans (add_le_add (le_refl _) hconstant))
  convert hlog using 1
  ring

/-- The centered log standard deviation admits a finite quantitative profile bound. -/
theorem abs_log_radialSigma_profile_le {N : ℕ} (hN : 0 < N) {K x : ℝ}
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N) (hx : |x| ≤ K) :
    |Real.log (radialSigma N (1 + x / N)) - (1 / 2 : ℝ) * Real.log N -
      kacLogVarianceProfile x| ≤ (K ^ 2 + K + Real.exp (2 * K) / 2) / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he : Real.log (radialSigma N (1 + x / N)) - (1 / 2 : ℝ) * Real.log N -
      kacLogVarianceProfile x = (1 / 2 : ℝ) *
        (Real.log (radialVariance N (1 + x / N) / N) - Real.log (kacVarianceProfile x)) := by
    rw [radialSigma, Real.log_sqrt (radialVariance_pos N _).le,
      Real.log_div (radialVariance_pos N _).ne' hn.ne', kacLogVarianceProfile]
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * ((2 * (K ^ 2 + K) + Real.exp (2 * K)) / N) :=
      mul_le_mul_of_nonneg_left (abs_log_radialVariance_profile_le hN hK hNK hx) (by norm_num)
    _ = _ := by ring

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.KacProfileQuadraticBound
import Erdos522.Analysis.LogarithmicRadiusBounds
import Erdos522.Analysis.FiniteAnnularMass
import Erdos522.Probability.SparseLogarithmicConcentration

/-!
# Quantitative radial counts near the unit circle

The quadratic profile bound and four Jensen probes control the root fraction
by the probe width and the logarithmic error divided by that width.
-/

noncomputable section
open Polynomial
namespace Erdos522

/-- The scaled logarithmic spacing has a uniform quadratic approximation. -/
theorem abs_scaled_log_radius_ratio_sub_le {N : ℕ} (hN : 0 < N) {K a b : ℝ}
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N) (ha : |a| ≤ K) (hb : |b| ≤ K) :
    |(N : ℝ) * Real.log ((1 + b / N) / (1 + a / N)) - (b - a)| ≤ 2 * K ^ 2 / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos {x : ℝ} (hx : |x| ≤ K) : 0 < 1 + x / (N : ℝ) := by
    have hu : -(1 / 2 : ℝ) ≤ x / N := (le_div_iff₀ hn).mpr (by have := (abs_le.mp hx).1; linarith)
    linarith
  rw [Real.log_div (hpos hb).ne' (hpos ha).ne']
  calc
    _ = |((N : ℝ) * Real.log (1 + b / N) - b) -
        ((N : ℝ) * Real.log (1 + a / N) - a)| := by congr 1; ring
    _ ≤ |(N : ℝ) * Real.log (1 + b / N) - b| +
        |(N : ℝ) * Real.log (1 + a / N) - a| := abs_sub _ _
    _ ≤ K ^ 2 / N + K ^ 2 / N := add_le_add
      (abs_scaled_log_radius_sub_le hN hK hNK hb) (abs_scaled_log_radius_sub_le hN hK hNK ha)
    _ = _ := by ring

/-- Perturbed half-slope secants retain a quantitative error bound. -/
theorem abs_secant_sub_half_le {N : ℕ} (hN : 0 < N) {K E A D : ℝ}
    (hK : 0 < K) (hE : 0 ≤ E) (hNK : 8 * K ≤ N)
    (hA : |A - K / 4| ≤ 2 * E + K ^ 2 / 2)
    (hD : |D - K / 2| ≤ 2 * K ^ 2 / N) :
    |A / D - 1 / 2| ≤ 6 * K + 8 * E / K := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsmall : 2 * K ^ 2 / N ≤ K / 4 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith [mul_nonneg hK.le (sub_nonneg.mpr hNK)]
  have hd : K / 4 ≤ D := by have := (abs_le.mp hD).1; linarith
  have hd0 : 0 < D := lt_of_lt_of_le (by positivity) hd
  have hcenter : |A - D / 2| ≤ 2 * E + K ^ 2 / 2 + K ^ 2 / N := by
    calc
      _ = |(A - K / 4) - (D - K / 2) / 2| := by congr 1; ring
      _ ≤ |A - K / 4| + |D - K / 2| / 2 := by
        simpa only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
          abs_sub (A - K / 4) ((D - K / 2) / 2)
      _ ≤ _ := by
        have he : (2 * K ^ 2 / (N : ℝ)) / 2 = K ^ 2 / N := by ring
        have h := add_le_add hA (div_le_div_of_nonneg_right hD (by norm_num : (0 : ℝ) ≤ 2))
        rwa [he] at h
  calc
    _ = |A - D / 2| / D := by
      have he : A / D - (1 / 2 : ℝ) = (A - D / 2) / D := by field_simp
      rw [he, abs_div, abs_of_pos hd0]
    _ ≤ (2 * E + K ^ 2 / 2 + K ^ 2 / N) / D := div_le_div_of_nonneg_right hcenter hd0.le
    _ ≤ (2 * E + K ^ 2 / 2 + K ^ 2 / N) / (K / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ ≤ (2 * E + K ^ 2 / 2 + K ^ 2) / (K / 4) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith [div_le_self (sq_nonneg K) hn1]
    _ = _ := by field_simp; ring

/-- A finite log-integral error around the profile gives the corresponding
linear-profile error. -/
theorem abs_logCircleAverage_linear_profile_le (P : ℂ[X]) (N : ℕ) {K x E c : ℝ}
    (hK : 0 ≤ K) (hx : |x| ≤ K)
    (hlog : |logCircleAverage P (1 + x / N) - (kacLogVarianceProfile x + c)| ≤ E) :
    |logCircleAverage P (1 + x / N) - (x / 2 + c)| ≤ E + K ^ 2 / 4 := by
  have hsq : x ^ 2 ≤ K ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hK).mpr hx
  calc
    _ = |(logCircleAverage P (1 + x / N) - (kacLogVarianceProfile x + c)) +
        (kacLogVarianceProfile x - x / 2)| := by congr 1; ring
    _ ≤ |logCircleAverage P (1 + x / N) - (kacLogVarianceProfile x + c)| +
        |kacLogVarianceProfile x - x / 2| := abs_add_le _ _
    _ ≤ E + K ^ 2 / 4 := add_le_add hlog
      ((abs_kacLogVarianceProfile_sub_half_le x).trans (div_le_div_of_nonneg_right hsq (by norm_num)))

/-- Two profile probes a half-width apart approximate the root-density half-slope. -/
theorem abs_profile_logarithmic_secant_sub_half_le (P : ℂ[X]) {N : ℕ} (hN : 0 < N)
    {K E c a b : ℝ} (hK : 0 < K) (hE : 0 ≤ E) (hNK : 8 * K ≤ N)
    (ha : |a| ≤ K) (hb : |b| ≤ K) (hab : b - a = K / 2)
    (hloga : |logCircleAverage P (1 + a / N) - (kacLogVarianceProfile a + c)| ≤ E)
    (hlogb : |logCircleAverage P (1 + b / N) - (kacLogVarianceProfile b + c)| ≤ E) :
    |(logCircleAverage P (1 + b / N) - logCircleAverage P (1 + a / N)) /
      ((N : ℝ) * Real.log ((1 + b / N) / (1 + a / N))) - 1 / 2| ≤ 6 * K + 8 * E / K := by
  apply abs_secant_sub_half_le hN hK hE hNK
  · have he : logCircleAverage P (1 + b / N) - logCircleAverage P (1 + a / N) - K / 4 =
        (logCircleAverage P (1 + b / N) - (b / 2 + c)) -
        (logCircleAverage P (1 + a / N) - (a / 2 + c)) := by linarith only [hab]
    rw [he]
    have h := (abs_sub _ _).trans (add_le_add
      (abs_logCircleAverage_linear_profile_le P N hK.le hb hlogb)
      (abs_logCircleAverage_linear_profile_le P N hK.le ha hloga))
    convert h using 1
    ring
  · simpa only [hab] using abs_scaled_log_radius_ratio_sub_le hN hK.le (by linarith) ha hb

/-- Four logarithmic profile probes bound every closed-disk root count between
the two middle radii, retaining multiplicities. -/
theorem radial_fraction_half_error_le (P : ℂ[X]) (N : ℕ) {K E c r : ℝ}
    (hK : 0 < K) (hE : 0 ≤ E) (hNK : 8 * K ≤ N)
    (hrl : 1 - K / (2 * N) ≤ r) (hru : r ≤ 1 + K / (2 * N))
    (hlog : ∀ i : Fin 4, |logCircleAverage P (radialSecantRadii K N i) -
      (kacLogVarianceProfile (![-K, -K / 2, K / 2, K] i) + c)| ≤ E) :
    |(closedZeroCount P r : ℝ) / N - 1 / 2| ≤ 6 * K + 8 * E / K := by
  have hn : (0 : ℝ) < N := by linarith
  have hn' : 0 < N := by exact_mod_cast hn
  have ht : 0 < K / (N : ℝ) := div_pos hK hn
  have hu : K / (N : ℝ) ≤ 1 / 8 := (div_le_iff₀ hn).mpr (by linarith)
  have hhalf : K / (2 * N : ℝ) = (K / N) / 2 := by ring
  have h₀ : 0 < 1 - K / (N : ℝ) := by linarith
  have h₀₁ : 1 - K / (N : ℝ) < 1 - K / (2 * N) := by rw [hhalf]; linarith
  have h₂ : 0 < 1 + K / (2 * N : ℝ) := by rw [hhalf]; linarith
  have h₂₃ : 1 + K / (2 * N : ℝ) < 1 + K / N := by rw [hhalf]; linarith
  have hlow := ((radial_zero_count_bound P h₀ h₀₁).2).trans
    (Nat.cast_le.mpr (closedZeroCount_mono P hrl))
  have hupp := (Nat.cast_le.mpr (closedZeroCount_mono P hru)).trans
    (radial_zero_count_bound P h₂ h₂₃).1
  have hin := abs_profile_logarithmic_secant_sub_half_le P hn' hK hE hNK
    (a := -K) (b := -K / 2) (by simp [abs_of_pos hK])
    (by rw [abs_div, abs_neg, abs_of_pos hK]; norm_num; linarith) (by ring)
    (hlog 0) (hlog 1)
  have hout := abs_profile_logarithmic_secant_sub_half_le P hn' hK hE hNK
    (a := K / 2) (b := K) (by rw [abs_div, abs_of_pos hK]; norm_num; linarith)
    (by simp [abs_of_pos hK]) (by ring) (hlog 2) (hlog 3)
  have hinner : 1 + (-K / 2) / (N : ℝ) = 1 - K / (2 * N) := by ring
  have houter : 1 + (K / 2) / (N : ℝ) = 1 + K / (2 * N) := by ring
  rw [hinner, neg_div, ← sub_eq_add_neg] at hin
  rw [houter] at hout
  have hlow' := div_le_div_of_nonneg_right hlow hn.le
  have hupp' := div_le_div_of_nonneg_right hupp hn.le
  rw [div_div, mul_comm (Real.log _) (N : ℝ)] at hlow' hupp'
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hin).1], by linarith [(abs_le.mp hout).2]⟩

end Erdos522

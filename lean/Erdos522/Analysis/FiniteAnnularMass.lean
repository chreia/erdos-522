/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.JensenSecants
import Erdos522.Analysis.KacVarianceProfile

/-!
# Finite annular mass from four profile probes

The inner logarithmic spacing is at least its linear spacing and the outer
spacing is at most its linear spacing. Monotonicity of the Jensen average
therefore preserves the exact coefficient `2 log 2 / K` at finite degree.
With probes at `±(K - h)` and `±K`, the same argument gives the coefficient
`log (K / (K - h)) / h`, which is at most `1 / (K - 1)` for the gap `h = 1`.
-/

noncomputable section
open Polynomial Set
namespace Erdos522

/-- Positive radial Jensen averages increase with the radius. -/
theorem logCircleAverage_mono_radius (P : ℂ[X]) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    logCircleAverage P r ≤ logCircleAverage P R := by
  rcases hrR.eq_or_lt with h | h
  · rw [h]
  · have hl := (radial_zero_count_bound P hr h).1
    have hp : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr h)
    have hn : 0 ≤ (logCircleAverage P R - logCircleAverage P r) / Real.log (R / r) :=
      (Nat.cast_nonneg _).trans hl
    have hnum := (le_div_iff₀ hp).mp hn
    simp only [zero_mul] at hnum
    exact sub_nonneg.mp hnum

/-- Logarithmic spacing lies between the endpoint reciprocal slopes. -/
theorem log_radius_ratio_bounds {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    (R - r) / R ≤ Real.log (R / r) ∧ Real.log (R / r) ≤ (R - r) / r := by
  have hp := div_pos hR hr
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hp
    convert h using 1
    field_simp
  · have h := Real.log_le_sub_one_of_pos hp
    convert h using 1
    field_simp

/-- Equal linear secants bound the annular mass whenever the inner logarithmic
spacing is larger and the outer logarithmic spacing is smaller. -/
theorem radial_mass_le_linear_secants (P : ℂ[X]) {N d r₁ r₂ r₃ r₄ : ℝ}
    (hN : 0 < N) (hd : 0 < d) (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (h₃ : 0 < r₃) (h₃₄ : r₃ < r₄)
    (hin : d ≤ N * Real.log (r₂ / r₁)) (hout : N * Real.log (r₄ / r₃) ≤ d) :
    (zeroCountIn P {z | ‖z‖ < r₁ ∨ r₄ < ‖z‖} : ℝ) / N ≤
      P.natDegree / N + ((logCircleAverage P r₂ - logCircleAverage P r₁) -
        (logCircleAverage P r₄ - logCircleAverage P r₃)) / d := by
  have hin0 := sub_nonneg.mpr (logCircleAverage_mono_radius P h₁ h₁₂.le)
  have hout0 := sub_nonneg.mpr (logCircleAverage_mono_radius P h₃ h₃₄.le)
  have hlout : 0 < N * Real.log (r₄ / r₃) :=
    mul_pos hN (Real.log_pos ((one_lt_div h₃).mpr h₃₄))
  have hleft := div_le_div_of_nonneg_left hin0 hd hin
  have hright := div_le_div_of_nonneg_left hout0 hlout hout
  have hmass := div_le_div_of_nonneg_right (radial_mass_four_radii P h₁ h₁₂ h₃ h₃₄) hN.le
  have heq : ((P.natDegree : ℝ) +
      (logCircleAverage P r₂ - logCircleAverage P r₁) / Real.log (r₂ / r₁) -
      (logCircleAverage P r₄ - logCircleAverage P r₃) / Real.log (r₄ / r₃)) / N =
      P.natDegree / N + (logCircleAverage P r₂ - logCircleAverage P r₁) /
        (N * Real.log (r₂ / r₁)) -
      (logCircleAverage P r₄ - logCircleAverage P r₃) / (N * Real.log (r₄ / r₃)) := by
    ring
  rw [heq] at hmass
  rw [sub_div]
  linarith

/-- Four logarithmic profile errors give the finite annular tail coefficient. -/
theorem radial_mass_le_kac_profile_bound (P : ℂ[X]) (N : ℕ) (hdegree : P.natDegree = N)
    {K E c : ℝ} (hK : 0 < K) (hNK : 2 * K < N)
    (h₀ : |logCircleAverage P (1 - K / N) - (kacLogVarianceProfile (-K) + c)| ≤ E)
    (h₁ : |logCircleAverage P (1 - K / (2 * N)) - (kacLogVarianceProfile (-K / 2) + c)| ≤ E)
    (h₂ : |logCircleAverage P (1 + K / (2 * N)) - (kacLogVarianceProfile (K / 2) + c)| ≤ E)
    (h₃ : |logCircleAverage P (1 + K / N) - (kacLogVarianceProfile K + c)| ≤ E) :
    (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) / N ≤
      2 * Real.log 2 / K + 8 * E / K := by
  have hn : (0 : ℝ) < N := by linarith
  have ht : 0 < K / (N : ℝ) := div_pos hK hn
  have ht1 : K / (N : ℝ) < 1 / 2 := (div_lt_iff₀ hn).mpr (by linarith)
  have hhalf : K / (2 * N : ℝ) = (K / N) / 2 := by ring
  have hri : 0 < 1 - K / (N : ℝ) := by linarith
  have hri' : 1 - K / (N : ℝ) < 1 - K / (2 * N) := by rw [hhalf]; linarith
  have hro : 0 < 1 + K / (2 * N : ℝ) := by rw [hhalf]; linarith
  have hro' : 1 + K / (2 * N : ℝ) < 1 + K / N := by rw [hhalf]; linarith
  have hinner := (log_radius_ratio_bounds hri (hri.trans hri')).1
  have houter := (log_radius_ratio_bounds hro (hro.trans hro')).2
  have hin : K / 2 ≤ (N : ℝ) * Real.log ((1 - K / (2 * N)) / (1 - K / N)) := by
    have he : ((1 - K / (2 * N : ℝ)) - (1 - K / N)) = K / (2 * N) := by ring
    rw [he] at hinner
    have hden : 1 - K / (2 * N : ℝ) ≤ 1 := by
      have : 0 ≤ K / (2 * N : ℝ) := by positivity
      linarith
    have hl : K / (2 * N : ℝ) ≤ (K / (2 * N)) / (1 - K / (2 * N)) := by
      exact le_div_self (by positivity) (by rw [hhalf]; linarith) hden
    have h := mul_le_mul_of_nonneg_left (hl.trans hinner) hn.le
    convert h using 1
    field_simp
  have hout : (N : ℝ) * Real.log ((1 + K / N) / (1 + K / (2 * N))) ≤ K / 2 := by
    have he : ((1 + K / (N : ℝ)) - (1 + K / (2 * N))) = K / (2 * N) := by ring
    rw [he] at houter
    have hd : 1 ≤ 1 + K / (2 * N : ℝ) := by
      have : 0 ≤ K / (2 * N : ℝ) := by positivity
      linarith
    have hu : (K / (2 * N : ℝ)) / (1 + K / (2 * N)) ≤ K / (2 * N) :=
      div_le_self (by positivity) hd
    have h := mul_le_mul_of_nonneg_left (houter.trans hu) hn.le
    convert h using 1
    field_simp
  have hmass := radial_mass_le_linear_secants P hn (by linarith : 0 < K / 2)
    hri hri' hro hro' hin hout
  have hset : {z : ℂ | ‖z‖ < 1 - K / N ∨ 1 + K / N < ‖z‖} =
      {z : ℂ | |‖z‖ - 1| ≤ K / N}ᶜ := by
    ext z
    simp only [mem_ofPred_eq, mem_compl_iff, not_le, lt_abs]
    constructor <;> rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  rw [hset, hdegree, div_self hn.ne'] at hmass
  have herror : (logCircleAverage P (1 - K / (2 * N)) - logCircleAverage P (1 - K / N)) -
      (logCircleAverage P (1 + K / N) - logCircleAverage P (1 + K / (2 * N))) ≤
      (kacLogVarianceProfile (-K / 2) - kacLogVarianceProfile (-K)) -
        (kacLogVarianceProfile K - kacLogVarianceProfile (K / 2)) + 4 * E := by
    have h0 := abs_le.mp h₀
    have h1 := abs_le.mp h₁
    have h2 := abs_le.mp h₂
    have h3 := abs_le.mp h₃
    linarith
  calc
    _ ≤ 1 + ((kacLogVarianceProfile (-K / 2) - kacLogVarianceProfile (-K)) -
        (kacLogVarianceProfile K - kacLogVarianceProfile (K / 2)) + 4 * E) / (K / 2) :=
      hmass.trans (add_le_add (le_refl _) (div_le_div_of_nonneg_right herror (by positivity)))
    _ = kacAnnularTailCoefficient K + 8 * E / K := by unfold kacAnnularTailCoefficient; ring
    _ ≤ _ := add_le_add (kacAnnularTailCoefficient_le hK) (le_refl _)

/-- The negative-coordinate logarithmic profile increment across a gap `h`
is at most `(1/2) log (K / (K - h))`. -/
theorem kacLogVarianceProfile_negative_gap_bound {K h : ℝ} (hh : 0 < h) (hhK : h < K) :
    kacLogVarianceProfile (-(K - h)) - kacLogVarianceProfile (-K) ≤
      (1 / 2 : ℝ) * Real.log (K / (K - h)) := by
  have hy : 0 < K - h := by linarith
  have hK : 0 < K := by linarith
  have hprofile {y : ℝ} (hy : 0 < y) :
      kacVarianceProfile (-y) = (1 - Real.exp (-2 * y)) / (2 * y) := by
    simp only [kacVarianceProfile, neg_eq_zero, hy.ne', ↓reduceIte]
    rw [show 2 * -y = -2 * y by ring]
    field_simp
    ring
  have hmul : kacVarianceProfile (-(K - h)) ≤ K / (K - h) * kacVarianceProfile (-K) := by
    rw [hprofile hy, hprofile hK]
    have he : Real.exp (-2 * K) ≤ Real.exp (-2 * (K - h)) := Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ (1 - Real.exp (-2 * K)) / (2 * (K - h)) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      _ = _ := by field_simp
  have hl := Real.log_le_log (kacVarianceProfile_pos _) hmul
  rw [Real.log_mul (div_pos hK hy).ne' (kacVarianceProfile_pos _).ne'] at hl
  unfold kacLogVarianceProfile
  linarith

/-- Four logarithmic profile errors at the probes `-K`, `-(K - h)`, `K - h`, `K`
bound the fraction of roots outside the annulus of width `K`. -/
theorem radial_mass_le_kac_profile_gap_bound (P : ℂ[X]) (N : ℕ) (hdegree : P.natDegree = N)
    {K h E c : ℝ} (hh : 0 < h) (hhK : h < K) (hNK : 2 * K < N)
    (h₀ : |logCircleAverage P (1 - K / N) - (kacLogVarianceProfile (-K) + c)| ≤ E)
    (h₁ : |logCircleAverage P (1 - (K - h) / N) - (kacLogVarianceProfile (-(K - h)) + c)| ≤ E)
    (h₂ : |logCircleAverage P (1 + (K - h) / N) - (kacLogVarianceProfile (K - h) + c)| ≤ E)
    (h₃ : |logCircleAverage P (1 + K / N) - (kacLogVarianceProfile K + c)| ≤ E) :
    (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) / N ≤
      (2 * (kacLogVarianceProfile (-(K - h)) - kacLogVarianceProfile (-K)) + 4 * E) / h := by
  have hK : 0 < K := by linarith
  have hn : (0 : ℝ) < N := by linarith
  have ht : K / (N : ℝ) < 1 / 2 := (div_lt_iff₀ hn).mpr (by linarith)
  have hs : 0 < h / (N : ℝ) := div_pos hh hn
  have hgap : K / (N : ℝ) - (K - h) / N = h / N := by ring
  have hs' : 0 ≤ (K - h) / (N : ℝ) := div_nonneg (by linarith) hn.le
  have hri : 0 < 1 - K / (N : ℝ) := by linarith
  have hri' : 1 - K / (N : ℝ) < 1 - (K - h) / N := by linarith
  have hro : 0 < 1 + (K - h) / (N : ℝ) := by linarith
  have hro' : 1 + (K - h) / (N : ℝ) < 1 + K / N := by linarith
  have hinner := (log_radius_ratio_bounds hri (hri.trans hri')).1
  have houter := (log_radius_ratio_bounds hro (hro.trans hro')).2
  have hin : h ≤ (N : ℝ) * Real.log ((1 - (K - h) / N) / (1 - K / N)) := by
    have he : (1 - (K - h) / (N : ℝ)) - (1 - K / N) = h / N := by linarith
    rw [he] at hinner
    have hl : h / (N : ℝ) ≤ (h / N) / (1 - (K - h) / N) :=
      le_div_self hs.le (by linarith) (by linarith)
    have h' := mul_le_mul_of_nonneg_left (hl.trans hinner) hn.le
    rwa [mul_div_cancel₀ _ hn.ne'] at h'
  have hout : (N : ℝ) * Real.log ((1 + K / N) / (1 + (K - h) / N)) ≤ h := by
    have he : (1 + K / (N : ℝ)) - (1 + (K - h) / N) = h / N := by linarith
    rw [he] at houter
    have hu : (h / (N : ℝ)) / (1 + (K - h) / N) ≤ h / N :=
      div_le_self hs.le (by linarith)
    have h' := mul_le_mul_of_nonneg_left (houter.trans hu) hn.le
    rwa [mul_div_cancel₀ _ hn.ne'] at h'
  have hmass := radial_mass_le_linear_secants P hn hh hri hri' hro hro' hin hout
  have hset : {z : ℂ | ‖z‖ < 1 - K / N ∨ 1 + K / N < ‖z‖} =
      {z : ℂ | |‖z‖ - 1| ≤ K / N}ᶜ := by
    ext z
    simp only [mem_ofPred_eq, mem_compl_iff, not_le, lt_abs]
    constructor <;> rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  rw [hset, hdegree, div_self hn.ne'] at hmass
  have hreflect := kacLogVarianceProfile_reflection K
  have hreflect' := kacLogVarianceProfile_reflection (K - h)
  have herror : (logCircleAverage P (1 - (K - h) / N) - logCircleAverage P (1 - K / N)) -
      (logCircleAverage P (1 + K / N) - logCircleAverage P (1 + (K - h) / N)) ≤
      2 * (kacLogVarianceProfile (-(K - h)) - kacLogVarianceProfile (-K)) - h + 4 * E := by
    have h0 := abs_le.mp h₀
    have h1 := abs_le.mp h₁
    have h2 := abs_le.mp h₂
    have h3 := abs_le.mp h₃
    linarith
  calc
    _ ≤ 1 + (2 * (kacLogVarianceProfile (-(K - h)) - kacLogVarianceProfile (-K)) - h + 4 * E) / h :=
      hmass.trans (add_le_add (le_refl _) (div_le_div_of_nonneg_right herror hh.le))
    _ = _ := by field_simp; ring

/-- At the gap `h = 1`, the four profile errors give the annular tail
coefficient `1 / (K - 1)`. -/
theorem radial_mass_le_kac_profile_unit_gap_bound (P : ℂ[X]) (N : ℕ)
    (hdegree : P.natDegree = N) {K E c : ℝ} (hK : 1 < K) (hNK : 2 * K < N)
    (h₀ : |logCircleAverage P (1 - K / N) - (kacLogVarianceProfile (-K) + c)| ≤ E)
    (h₁ : |logCircleAverage P (1 - (K - 1) / N) - (kacLogVarianceProfile (-(K - 1)) + c)| ≤ E)
    (h₂ : |logCircleAverage P (1 + (K - 1) / N) - (kacLogVarianceProfile (K - 1) + c)| ≤ E)
    (h₃ : |logCircleAverage P (1 + K / N) - (kacLogVarianceProfile K + c)| ≤ E) :
    (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) / N ≤ 1 / (K - 1) + 4 * E := by
  have hK1 : 0 < K - 1 := by linarith
  have hmass := radial_mass_le_kac_profile_gap_bound P N hdegree one_pos hK hNK h₀ h₁ h₂ h₃
  have hprofile := kacLogVarianceProfile_negative_gap_bound one_pos hK
  have hlog : Real.log (K / (K - 1)) ≤ 1 / (K - 1) := by
    have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < K) hK1)
    have he : K / (K - 1) - 1 = 1 / (K - 1) := by field_simp; ring
    linarith
  rw [div_one] at hmass
  linarith

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.RightEndpointSums
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Quantitative logarithmic radial coordinates

On the scale `1/N`, the logarithmic radius differs from its linear
coordinate by at most the squared coordinate divided by `N`. This controls
radial monomials uniformly when the annular width grows with the degree.
-/

noncomputable section
open MeasureTheory Set
namespace Erdos522

/-- The linear approximation to the real logarithm on the half-unit interval. -/
theorem abs_log_one_add_sub_self_le_sq {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - u| ≤ u ^ 2 := by
  have hu1 : ‖(u : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      (hu.trans_lt (by norm_num : (1 / 2 : ℝ) < 1))
  have h := Complex.norm_log_one_add_sub_self_le hu1
  have hpos : 0 ≤ 1 + u := by have := (abs_le.mp hu).1; linarith
  have hlog : Complex.log (1 + (u : ℂ)) = (Real.log (1 + u) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_log hpos]
  rw [hlog, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  have hden : 0 < 1 - |u| := by linarith
  have hinv : (1 - |u|)⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ hden).mpr (by linarith)
  calc
    _ ≤ u ^ 2 * (1 - |u|)⁻¹ / 2 := h
    _ ≤ u ^ 2 * 2 / 2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hinv (sq_nonneg _)) (by norm_num)
    _ = _ := by ring

/-- The exact logarithmic radial coordinate has a quadratic finite-degree error. -/
theorem abs_scaled_log_radius_sub_le {N : ℕ} (hN : 0 < N) {K x : ℝ}
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N) (hx : |x| ≤ K) :
    |(N : ℝ) * Real.log (1 + x / N) - x| ≤ K ^ 2 / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : |x / N| ≤ (1 / 2 : ℝ) := by
    rw [abs_div, abs_of_pos hn]
    exact (div_le_iff₀ hn).mpr (by linarith)
  have h := abs_log_one_add_sub_self_le_sq hu
  have hsq : x ^ 2 ≤ K ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hK).mpr hx
  calc
    _ = (N : ℝ) * |Real.log (1 + x / N) - x / N| := by
      have he : (N : ℝ) * Real.log (1 + x / N) - x =
          N * (Real.log (1 + x / N) - x / N) := by field_simp
      rw [he, abs_mul, abs_of_pos hn]
    _ ≤ (N : ℝ) * (x / N) ^ 2 := mul_le_mul_of_nonneg_left h hn.le
    _ = x ^ 2 / N := by field_simp
    _ ≤ K ^ 2 / N := div_le_div_of_nonneg_right hsq hn.le

/-- The sampled radial exponent differs uniformly from its continuum exponent. -/
theorem abs_sampled_radial_exponent_sub_le {N : ℕ} (hN : 0 < N) {K x t : ℝ}
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N) (hx : |x| ≤ K) (ht : t ∈ Ico (0 : ℝ) 1) :
    |2 * ((N : ℝ) * Real.log (1 + x / N)) * rightEndpointSample N t - 2 * x * t| ≤
      2 * (K ^ 2 + K) / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := rightEndpointSample_mem hN ht
  have hmesh := rightEndpointSample_bounds hN ht.1
  have hdiff : |rightEndpointSample N t - t| ≤ 1 / N := by
    rw [abs_of_nonneg (sub_nonneg.mpr hmesh.1.le)]
    linarith [hmesh.2]
  have hrad := abs_scaled_log_radius_sub_le hN hK hNK hx
  calc
    _ = 2 * |((N : ℝ) * Real.log (1 + x / N) - x) * rightEndpointSample N t +
        x * (rightEndpointSample N t - t)| := by
      have he : 2 * ((N : ℝ) * Real.log (1 + x / N)) * rightEndpointSample N t - 2 * x * t =
          2 * (((N : ℝ) * Real.log (1 + x / N) - x) * rightEndpointSample N t +
            x * (rightEndpointSample N t - t)) := by ring
      rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * (|(N : ℝ) * Real.log (1 + x / N) - x| * |rightEndpointSample N t| +
        |x| * |rightEndpointSample N t - t|) := by
      rw [← abs_mul, ← abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ 2 * (K ^ 2 / N * 1 + K * (1 / N)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add
      · exact mul_le_mul hrad (by simpa only [abs_of_pos hs.1] using hs.2)
          (abs_nonneg _) (by positivity)
      · exact mul_le_mul hx hdiff (abs_nonneg _) hK
    _ = _ := by ring

end Erdos522

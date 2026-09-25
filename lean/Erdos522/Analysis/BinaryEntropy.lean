/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic

/-!
# Binary relative entropy

The negative binary entropy has curvature at least four on the unit interval.
Its supporting-line inequality gives the sharp quadratic lower bound used in
entropy comparisons of probability measures.
-/

noncomputable section

open Set

namespace Erdos522

/-- Relative entropy of two Bernoulli laws, written with the totalized real logarithm. -/
def binaryRelativeEntropy (u v : ℝ) : ℝ :=
  u * Real.log (u / v) + (1 - u) * Real.log ((1 - u) / (1 - v))

/-- Negative binary entropy after subtracting the quadratic curvature term. -/
def binaryEntropyDefect (u : ℝ) : ℝ :=
  -Real.binEntropy u - 2 * u ^ 2

/-- The endpoint values are covered by continuity of `x log x`. -/
theorem continuous_binaryEntropyDefect : Continuous binaryEntropyDefect := by
  unfold binaryEntropyDefect
  fun_prop

/-- The derivative of the convexity defect on the open probability interval. -/
theorem hasDerivAt_binaryEntropyDefect {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt binaryEntropyDefect (Real.log u - Real.log (1 - u) - 4 * u) u := by
  have hentropy := (Real.hasDerivAt_binEntropy hu0.ne' hu1.ne).neg
  have hquad := ((hasDerivAt_id u).pow 2).const_mul 2
  convert hentropy.sub hquad using 1
  · ext x
    simp [binaryEntropyDefect]
  · norm_num
    ring

/-- The second derivative is nonnegative because `u(1-u) ≤ 1/4`. -/
theorem hasDerivAt_binaryEntropyDefect_derivative {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (fun x : ℝ => Real.log x - Real.log (1 - x) - 4 * x)
      (u⁻¹ + (1 - u)⁻¹ - 4) u := by
  have hlog := ((hasDerivAt_id u).const_sub 1).log (sub_pos.mpr hu1).ne'
  convert ((Real.hasDerivAt_log hu0.ne').sub hlog).sub
    ((hasDerivAt_id u).const_mul 4) using 1
  · ext x
    rfl
  · norm_num [one_div]
    ring

/-- Subtracting `2u²` from negative binary entropy leaves a convex function on
    the entire closed unit interval. -/
theorem convexOn_binaryEntropyDefect : ConvexOn ℝ (Icc (0 : ℝ) 1) binaryEntropyDefect := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fun x : ℝ =>
      Real.log x - Real.log (1 - x) - 4 * x)
    (f'' := fun x : ℝ => x⁻¹ + (1 - x)⁻¹ - 4)
    (convex_Icc _ _) continuous_binaryEntropyDefect.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_binaryEntropyDefect hx.1 hx.2).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_binaryEntropyDefect_derivative hx.1 hx.2).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
    have heq : x⁻¹ + (1 - x)⁻¹ - 4 = (2 * x - 1) ^ 2 / (x * (1 - x)) := by
      field_simp
      ring
    rw [heq]
    exact div_nonneg (sq_nonneg _) (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le))

/-- The supporting line at an interior point lies below the binary entropy defect. -/
theorem binaryEntropyDefect_support {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 < v) (hv1 : v < 1) :
    binaryEntropyDefect v + (Real.log v - Real.log (1 - v) - 4 * v) * (u - v) ≤
      binaryEntropyDefect u := by
  have hu : u ∈ Icc (0 : ℝ) 1 := ⟨hu0, hu1⟩
  have hv : v ∈ Icc (0 : ℝ) 1 := ⟨hv0.le, hv1.le⟩
  rcases lt_trichotomy u v with huv | rfl | hvu
  · have hs := convexOn_binaryEntropyDefect.slope_le_of_hasDerivAt hu hv huv
      (hasDerivAt_binaryEntropyDefect hv0 hv1)
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr huv)).mp hs
    nlinarith
  · simp
  · have hs := convexOn_binaryEntropyDefect.le_slope_of_hasDerivAt hv hu hvu
      (hasDerivAt_binaryEntropyDefect hv0 hv1)
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr hvu)).mp hs
    nlinarith

/-- The logarithmic ratio formula remains valid after multiplication by a zero numerator. -/
theorem mul_log_div_eq {u v : ℝ} (hv : v ≠ 0) :
    u * Real.log (u / v) = u * Real.log u - u * Real.log v := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [Real.log_div hu hv]
    ring

/-- Binary relative entropy dominates twice the squared difference of the probabilities. -/
theorem binaryRelativeEntropy_ge_two_mul_sq {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 < v) (hv1 : v < 1) :
    2 * (u - v) ^ 2 ≤ binaryRelativeEntropy u v := by
  have h := binaryEntropyDefect_support hu0 hu1 hv0 hv1
  unfold binaryRelativeEntropy
  rw [mul_log_div_eq hv0.ne', mul_log_div_eq (sub_pos.mpr hv1).ne']
  simp only [binaryEntropyDefect, Real.binEntropy, Real.log_inv] at h
  nlinarith

/-- The square-root form of the binary relative-entropy inequality. -/
theorem abs_sub_le_sqrt_half_binaryRelativeEntropy {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 < v) (hv1 : v < 1) :
    |u - v| ≤ Real.sqrt (binaryRelativeEntropy u v / 2) := by
  have h := binaryRelativeEntropy_ge_two_mul_sq hu0 hu1 hv0 hv1
  have hs : (u - v) ^ 2 ≤ binaryRelativeEntropy u v / 2 := by linarith
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hs

/-- For a reference probability in `(0,1)`, binary relative entropy is continuous
    in its first probability, including the endpoints `0` and `1`. -/
theorem continuous_binaryRelativeEntropy_left {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    Continuous (fun u => binaryRelativeEntropy u v) := by
  have hfun : (fun u => binaryRelativeEntropy u v) =
      (fun u => u * Real.log u - u * Real.log v +
        ((1 - u) * Real.log (1 - u) - (1 - u) * Real.log (1 - v))) := by
    ext u
    exact congrArg₂ (· + ·) (mul_log_div_eq hv0.ne')
      (mul_log_div_eq (sub_pos.mpr hv1).ne')
  rw [hfun]
  fun_prop

end Erdos522

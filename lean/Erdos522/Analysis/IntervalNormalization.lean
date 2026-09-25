/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.AffineIntegration

/-!
# Normalization of interval restriction inequalities

The affine map from a centered unit interval to `[u,v)` preserves relative
set lengths and multiplies both sides of an integral inequality by the same
positive factor.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Erdos522

/-- The centered affine map has exactly the prescribed half-open image. -/
theorem preimage_Ico_interval_center {u v : ℝ} (huv : u < v) :
    (realAffineEquiv ((u + v) / 2) (v - u) (sub_pos.mpr huv).ne') ⁻¹' Ico u v =
      Ico (-(1 / 2 : ℝ)) (1 / 2) := by
  have h := preimage_Ico_realAffineEquiv ((u + v) / 2) (sub_pos.mpr huv)
  rw [show (u + v) / 2 - (v - u) / 2 = u by ring,
    show (u + v) / 2 + (v - u) / 2 = v by ring] at h
  exact h

/-- Relative density becomes ordinary length after normalizing an interval. -/
theorem le_volumeReal_preimage_interval_center {u v γ : ℝ} (huv : u < v)
    (E : Set ℝ) (hE : MeasurableSet E)
    (hden : γ * volume.real (Ico u v) ≤ volume.real E) :
    γ ≤ volume.real
      ((realAffineEquiv ((u + v) / 2) (v - u) (sub_pos.mpr huv).ne') ⁻¹' E) := by
  rw [volumeReal_preimage_realAffineEquiv _ (sub_pos.mpr huv) _ hE]
  rw [Real.volume_real_Ico, max_eq_left (sub_pos.mpr huv).le] at hden
  exact (le_inv_mul_iff₀ (sub_pos.mpr huv)).mpr (by simpa only [mul_comm] using hden)

/-- A subset of an interval pulls back to the centered unit interval. -/
theorem preimage_subset_centered_interval {u v : ℝ} (huv : u < v)
    {E : Set ℝ} (hsub : E ⊆ Ico u v) :
    (realAffineEquiv ((u + v) / 2) (v - u) (sub_pos.mpr huv).ne') ⁻¹' E ⊆
      Icc (-(1 / 2 : ℝ)) (1 / 2) := by
  have hs := preimage_mono (f := realAffineEquiv ((u + v) / 2) (v - u)
    (sub_pos.mpr huv).ne') hsub
  rw [preimage_Ico_interval_center huv] at hs
  exact hs.trans Ico_subset_Icc_self

/-- Integrating after affine normalization does not change a restriction
constant, since the two integrals acquire the same positive factor. -/
theorem integral_Ico_le_of_affine_restriction {u v B : ℝ} (huv : u < v)
    (E : Set ℝ) (f : ℝ → ℝ)
    (h : (∫ x in Ico (-(1 / 2 : ℝ)) (1 / 2),
      f ((u + v) / 2 + (v - u) * x)) ≤
      B * ∫ x in (realAffineEquiv ((u + v) / 2) (v - u) (sub_pos.mpr huv).ne') ⁻¹' E,
        f ((u + v) / 2 + (v - u) * x)) :
    (∫ x in Ico u v, f x) ≤ B * ∫ x in E, f x := by
  rw [← preimage_Ico_interval_center huv,
    integral_preimage_realAffineEquiv _ (sub_pos.mpr huv),
    integral_preimage_realAffineEquiv _ (sub_pos.mpr huv)] at h
  have h' : (v - u)⁻¹ * (∫ x in Ico u v, f x) ≤
      (v - u)⁻¹ * (B * ∫ x in E, f x) := by nlinarith [h]
  exact (mul_le_mul_iff_right₀ (inv_pos.mpr (sub_pos.mpr huv))).mp h'

end Erdos522

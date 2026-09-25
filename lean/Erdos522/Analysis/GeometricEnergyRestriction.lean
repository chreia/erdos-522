/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.GeometricMean
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# From geometric restriction to energy restriction

A pointwise bound by a geometric mean becomes an `L²` restriction estimate
by Jensen's inequality. Normalizing an interval to length one leaves exactly
one additional inverse power of the length of the measurable subset.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Erdos522

/-- A geometric restriction bound on an interval of length one gives a
mean-square restriction bound with one additional inverse-length factor. -/
theorem integral_norm_sq_le_of_geometric_bound
    (E : Set ℝ) (hfinite : volume E ≠ ∞) (hpos : 0 < volume.real E)
    (f : ℝ → ℂ) (hlog : IntegrableOn (fun x => Real.log ‖f x‖) E)
    (hE2 : IntegrableOn (fun x => ‖f x‖ ^ 2) E)
    (hI2 : IntegrableOn (fun x => ‖f x‖ ^ 2) (Ico (-(1 / 2 : ℝ)) (1 / 2)))
    (hzero : ∀ᵐ x ∂volume.restrict E, f x ≠ 0)
    {B : ℝ}
    (hbound : ∀ x ∈ Ico (-(1 / 2 : ℝ)) (1 / 2),
      ‖f x‖ ≤ B * geometricMean (volume.restrict E) f) :
    (∫ x in Ico (-(1 / 2 : ℝ)) (1 / 2), ‖f x‖ ^ 2) ≤
      B ^ 2 * (volume.real E)⁻¹ * ∫ x in E, ‖f x‖ ^ 2 := by
  let μ := volume.restrict E
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hfinite
  have hμ : μ ≠ 0 := by
    intro hz
    have heq : volume.real E = 0 := by
      calc
        _ = μ.real univ := (measureReal_restrict_apply_univ E).symm
        _ = 0 := by rw [hz]; simp
    exact hpos.ne' heq
  let : NeZero μ := ⟨hμ⟩
  have hmean := geometricMean_sq_le_average_norm_sq μ f hlog hE2 hzero
  rw [average_eq, smul_eq_mul, measureReal_restrict_apply_univ] at hmean
  have hpoint : ∀ᵐ x ∂volume.restrict (Ico (-(1 / 2 : ℝ)) (1 / 2)),
      ‖f x‖ ^ 2 ≤ B ^ 2 * geometricMean μ f ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hbound x hx) 2
  have hint := integral_mono_ae hI2 (integrable_const (B ^ 2 * geometricMean μ f ^ 2)) hpoint
  rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ico] at hint
  norm_num at hint
  calc
    _ ≤ B ^ 2 * geometricMean μ f ^ 2 := hint
    _ ≤ B ^ 2 * ((volume.real E)⁻¹ * ∫ x in E, ‖f x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmean (sq_nonneg B)
    _ = _ := by ring

/-- A constant at least one absorbs the additional inverse-length factor.
The displayed exponent also covers the empty and one-term cases. -/
theorem geometric_restriction_coefficient_le {C α γ : ℝ} (hC : 1 ≤ C)
    (hα : 0 < α) (hγ : 0 < γ) (hγα : γ ≤ α) (hγ1 : γ ≤ 1) (m : ℕ) :
    ((C / α) ^ (m - 1)) ^ 2 * α⁻¹ ≤ (C / γ) ^ (2 * m + 1) := by
  have hC0 : 0 ≤ C := by linarith
  have hbase : C / α ≤ C / γ := div_le_div_of_nonneg_left hC0 hγ hγα
  have hinv : α⁻¹ ≤ C / γ := by
    calc
      _ = 1 / α := (one_div α).symm
      _ ≤ 1 / γ := one_div_le_one_div_of_le hγ hγα
      _ ≤ C / γ := div_le_div_of_nonneg_right hC hγ.le
  have hone : 1 ≤ C / γ := (le_div_iff₀ hγ).mpr (by linarith)
  calc
    _ ≤ ((C / γ) ^ (m - 1)) ^ 2 * (C / γ) := by
      apply mul_le_mul _ hinv (inv_nonneg.mpr hα.le) (by positivity)
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) hbase _) _
    _ = (C / γ) ^ (2 * (m - 1) + 1) := by rw [← pow_mul, pow_succ]; ring_nf
    _ ≤ _ := pow_le_pow_right₀ hone (by omega)

/-- A continuous function satisfying geometric restriction on the centered
unit interval satisfies the corresponding measurable-set energy inequality. -/
theorem integral_norm_sq_le_of_geometric_restriction
    (E : Set ℝ) (hsub : E ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (f : ℝ → ℂ) (hf : Continuous f)
    (hlog : IntegrableOn (fun x => Real.log ‖f x‖) E)
    (hzero : ∀ᵐ x ∂volume.restrict E, f x ≠ 0)
    {C γ : ℝ} (hC : 1 ≤ C) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hden : γ ≤ volume.real E) (m : ℕ)
    (hbound : ∀ x ∈ Ico (-(1 / 2 : ℝ)) (1 / 2),
      ‖f x‖ ≤ (C / volume.real E) ^ (m - 1) * geometricMean (volume.restrict E) f) :
    (∫ x in Ico (-(1 / 2 : ℝ)) (1 / 2), ‖f x‖ ^ 2) ≤
      (C / γ) ^ (2 * m + 1) * ∫ x in E, ‖f x‖ ^ 2 := by
  have hfinite : volume E ≠ ∞ := ne_of_lt ((measure_mono hsub).trans_lt (by simp))
  have hpos := hγ.trans_le hden
  have hE2 : IntegrableOn (fun x => ‖f x‖ ^ 2) E :=
    (hf.norm.pow 2).integrableOn_Icc.mono_set hsub
  have hI2 : IntegrableOn (fun x => ‖f x‖ ^ 2) (Ico (-(1 / 2 : ℝ)) (1 / 2)) :=
    (hf.norm.pow 2).integrableOn_Icc.mono_set Ico_subset_Icc_self
  calc
    _ ≤ ((C / volume.real E) ^ (m - 1)) ^ 2 * (volume.real E)⁻¹ *
        ∫ x in E, ‖f x‖ ^ 2 :=
      integral_norm_sq_le_of_geometric_bound E hfinite hpos f hlog hE2 hI2 hzero hbound
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (geometric_restriction_coefficient_le hC hpos hγ hden hγ1 m)
      (integral_nonneg fun _ => sq_nonneg _)

end Erdos522

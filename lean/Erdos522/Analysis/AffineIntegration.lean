/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.GeometricMean
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Affine normalization of real integrals

An orientation-preserving affine change of variables rescales Lebesgue measure
and integrals by the reciprocal length. Averages and geometric means are
unchanged, which permits measurable restriction bounds to be stated on one
fixed interval and reused on every interval.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Erdos522

/-- The measurable affine equivalence `x ↦ a + l x`. -/
def realAffineEquiv (a l : ℝ) (hl : l ≠ 0) : ℝ ≃ᵐ ℝ :=
  (MeasurableEquiv.mulLeft₀ l hl).trans (MeasurableEquiv.addLeft a)

@[simp] theorem realAffineEquiv_apply (a l : ℝ) (hl : l ≠ 0) (x : ℝ) :
    realAffineEquiv a l hl x = a + l * x := rfl

/-- An affine map sends a centered unit interval to the interval with the
given center and length. -/
theorem preimage_Ico_realAffineEquiv (a : ℝ) {l : ℝ} (hl : 0 < l) :
    (realAffineEquiv a l hl.ne') ⁻¹' Ico (a - l / 2) (a + l / 2) =
      Ico (-(1 / 2 : ℝ)) (1 / 2) := by
  ext x
  simp only [mem_preimage, realAffineEquiv_apply, mem_Ico]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor <;> nlinarith
  · rintro ⟨hlo, hhi⟩
    constructor <;> nlinarith

/-- Positive affine scaling transports Lebesgue measure by the reciprocal length. -/
theorem map_volume_realAffineEquiv (a : ℝ) {l : ℝ} (hl : 0 < l) :
    Measure.map (realAffineEquiv a l hl.ne') volume = ENNReal.ofReal l⁻¹ • volume := by
  change Measure.map ((fun x : ℝ => a + x) ∘ (fun x => l * x)) volume = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), Real.map_volume_mul_left hl.ne',
    Measure.map_smul _ (by fun_prop), Measure.IsAddLeftInvariant.map_add_left_eq_self]
  rw [abs_of_pos (inv_pos.mpr hl)]

/-- The same scaling identity holds after restriction to an arbitrary set. -/
theorem map_restrict_realAffineEquiv (a : ℝ) {l : ℝ} (hl : 0 < l) (E : Set ℝ) :
    Measure.map (realAffineEquiv a l hl.ne')
      (volume.restrict ((realAffineEquiv a l hl.ne') ⁻¹' E)) =
      ENNReal.ofReal l⁻¹ • volume.restrict E := by
  rw [← (realAffineEquiv a l hl.ne').restrict_map, map_volume_realAffineEquiv a hl,
    Measure.restrict_smul]

/-- Set lengths scale by the reciprocal affine length. -/
theorem volume_preimage_realAffineEquiv (a : ℝ) {l : ℝ} (hl : 0 < l)
    (E : Set ℝ) (hE : MeasurableSet E) :
    volume ((realAffineEquiv a l hl.ne') ⁻¹' E) = ENNReal.ofReal l⁻¹ * volume E := by
  rw [← Measure.map_apply (realAffineEquiv a l hl.ne').measurable hE,
    map_volume_realAffineEquiv a hl, Measure.smul_apply, smul_eq_mul]

theorem volumeReal_preimage_realAffineEquiv (a : ℝ) {l : ℝ} (hl : 0 < l)
    (E : Set ℝ) (hE : MeasurableSet E) :
    volume.real ((realAffineEquiv a l hl.ne') ⁻¹' E) = l⁻¹ * volume.real E := by
  rw [measureReal_def, volume_preimage_realAffineEquiv a hl E hE, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hl.le)]
  rfl

/-- Affine substitution in a real set integral. -/
theorem integral_preimage_realAffineEquiv (a : ℝ) {l : ℝ} (hl : 0 < l)
    (E : Set ℝ) (f : ℝ → ℝ) :
    (∫ x in (realAffineEquiv a l hl.ne') ⁻¹' E, f (a + l * x)) =
      l⁻¹ * ∫ x in E, f x := by
  calc
    _ = ∫ x, f x ∂Measure.map (realAffineEquiv a l hl.ne')
        (volume.restrict ((realAffineEquiv a l hl.ne') ⁻¹' E)) :=
      ((realAffineEquiv a l hl.ne').measurableEmbedding.integral_map f).symm
    _ = _ := by
      rw [map_restrict_realAffineEquiv a hl, integral_smul_measure,
        ENNReal.toReal_ofReal (inv_nonneg.mpr hl.le), smul_eq_mul]

/-- The normalized average is invariant under positive affine substitution. -/
theorem average_preimage_realAffineEquiv (a : ℝ) {l : ℝ} (hl : 0 < l)
    (E : Set ℝ) (hE : MeasurableSet E) (f : ℝ → ℝ) :
    (⨍ x in (realAffineEquiv a l hl.ne') ⁻¹' E, f (a + l * x)) = ⨍ x in E, f x := by
  rw [average_eq, average_eq, smul_eq_mul, smul_eq_mul,
    measureReal_restrict_apply_univ, measureReal_restrict_apply_univ,
    volumeReal_preimage_realAffineEquiv a hl E hE, integral_preimage_realAffineEquiv a hl]
  rw [mul_inv_rev, inv_inv]
  field_simp

/-- Geometric means use the same normalization on every real interval. -/
theorem geometricMean_preimage_realAffineEquiv (a : ℝ) {l : ℝ} (hl : 0 < l)
    (E : Set ℝ) (hE : MeasurableSet E) (f : ℝ → ℂ) :
    geometricMean (volume.restrict ((realAffineEquiv a l hl.ne') ⁻¹' E))
      (fun x => f (a + l * x)) = geometricMean (volume.restrict E) f := by
  unfold geometricMean
  exact congrArg Real.exp (average_preimage_realAffineEquiv a hl E hE
    (fun x => Real.log ‖f x‖))

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Angular exceptional sets

Normalized Haar measure controls the real-axis resonances and the ordinary
and conjugate diagonals excluded from polynomial jet covariance estimates.
-/

noncomputable section
open MeasureTheory Metric
open scoped ENNReal

namespace Erdos522

/-- The normalized measure of a closed arc on a circle of circumference `T`. -/
theorem haarAddCircle_real_closedBall {T : ℝ} [hT : Fact (0 < T)]
    (θ : AddCircle T) (δ : ℝ) (hδ : 0 ≤ δ) :
    AddCircle.haarAddCircle.real (closedBall θ δ) = min T (2 * δ) / T := by
  have h := congrArg (fun μ : Measure (AddCircle T) => μ.real (closedBall θ δ))
    (AddCircle.volume_eq_smul_haarAddCircle (T := T))
  simp only [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal hT.out.le] at h
  have hv : (volume : Measure (AddCircle T)).real (closedBall θ δ) = min T (2 * δ) := by
    rw [measureReal_def, AddCircle.volume_closedBall, ENNReal.toReal_ofReal]
    exact le_min hT.out.le (mul_nonneg (by norm_num) hδ)
  rw [hv] at h
  apply (eq_div_iff hT.out.ne').mpr
  linarith

/-- A closed arc has normalized measure at most its length divided by the circumference. -/
theorem haarAddCircle_real_closedBall_le {T : ℝ} [hT : Fact (0 < T)]
    (θ : AddCircle T) (δ : ℝ) (hδ : 0 ≤ δ) :
    AddCircle.haarAddCircle.real (closedBall θ δ) ≤ 2 * δ / T := by
  rw [haarAddCircle_real_closedBall θ δ hδ]
  exact div_le_div_of_nonneg_right (min_le_right _ _) hT.out.le

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Normalized angular measure in radian coordinates. -/
abbrev radianHaar : Measure (AddCircle (2 * Real.pi)) := AddCircle.haarAddCircle

/-- The angular resonance near the real axis is the inverse image of a short arc under doubling. -/
def angularResonance (δ : ℝ) : Set (AddCircle (2 * Real.pi)) :=
  {θ | ‖(2 : ℤ) • θ‖ < δ}

/-- The real-axis angular exceptional set is measurable. -/
theorem measurableSet_angularResonance (δ : ℝ) : MeasurableSet (angularResonance δ) := by
  exact measurableSet_lt (by fun_prop) measurable_const

/-- Doubling preserves normalized Haar measure, so the resonance has measure at most `δ/π`. -/
theorem radianHaar_angularResonance_le (δ : ℝ) (hδ : 0 ≤ δ) :
    radianHaar.real (angularResonance δ) ≤ δ / Real.pi := by
  have hpres : MeasurePreserving (fun θ : AddCircle (2 * Real.pi) => (2 : ℤ) • θ)
      radianHaar radianHaar := Measure.measurePreserving_zsmul radianHaar (by norm_num)
  have hsubset : angularResonance δ ⊆
      (fun θ : AddCircle (2 * Real.pi) => (2 : ℤ) • θ) ⁻¹' closedBall 0 δ := by
    intro θ hθ
    change ‖(2 : ℤ) • θ‖ < δ at hθ
    simpa only [Set.mem_preimage, mem_closedBall, dist_zero_right] using hθ.le
  have hmono := measureReal_mono (μ := radianHaar) hsubset
  have heq := hpres.measure_preimage (s := closedBall 0 δ) measurableSet_closedBall.nullMeasurableSet
  simp only [measureReal_def, heq] at hmono
  calc
    _ ≤ radianHaar.real (closedBall 0 δ) := hmono
    _ ≤ 2 * δ / (2 * Real.pi) := haarAddCircle_real_closedBall_le 0 δ hδ
    _ = δ / Real.pi := by ring

/-- A short open angular arc has normalized measure at most `δ/π`. -/
theorem radianHaar_real_ball_le (δ : ℝ) (hδ : 0 ≤ δ) :
    radianHaar.real (ball 0 δ) ≤ δ / Real.pi := by
  calc
    _ ≤ radianHaar.real (closedBall 0 δ) := measureReal_mono ball_subset_closedBall
    _ ≤ 2 * δ / (2 * Real.pi) := haarAddCircle_real_closedBall_le 0 δ hδ
    _ = _ := by ring

/-- The union of the two real-axis resonances and the ordinary and conjugate diagonals. -/
def angularPairExceptions (δ : ℝ) : Set (AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi)) :=
  ((Prod.fst ⁻¹' angularResonance δ) ∪ (Prod.snd ⁻¹' angularResonance δ)) ∪
    (((fun p => p.1 - p.2) ⁻¹' ball 0 δ) ∪ ((fun p => p.1 + p.2) ⁻¹' ball 0 δ))

/-- All four excluded angular relations form a measurable set. -/
theorem measurableSet_angularPairExceptions (δ : ℝ) : MeasurableSet (angularPairExceptions δ) :=
  (((measurableSet_angularResonance δ).preimage measurable_fst).union
    ((measurableSet_angularResonance δ).preimage measurable_snd)).union
      ((measurableSet_ball.preimage (by fun_prop)).union (measurableSet_ball.preimage (by fun_prop)))

/-- Four measure-preserving projections give the exact four-term exceptional-set budget. -/
theorem radianHaar_angularPairExceptions_le (δ : ℝ) (hδ : 0 ≤ δ) :
    (radianHaar.prod radianHaar).real (angularPairExceptions δ) ≤ 4 * δ / Real.pi := by
  have hsub : MeasurePreserving
      (fun p : AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi) => p.1 - p.2)
      (radianHaar.prod radianHaar) radianHaar :=
    measurePreserving_fst.comp (measurePreserving_sub_prod radianHaar radianHaar)
  have hadd : MeasurePreserving
      (fun p : AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi) => p.1 + p.2)
      (radianHaar.prod radianHaar) radianHaar :=
    measurePreserving_fst.comp (measurePreserving_add_prod radianHaar radianHaar)
  have hreal (f : AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi))
      (hf : MeasurePreserving f (radianHaar.prod radianHaar) radianHaar)
      (s : Set (AddCircle (2 * Real.pi))) (hs : MeasurableSet s) :
      (radianHaar.prod radianHaar).real (f ⁻¹' s) = radianHaar.real s :=
    congrArg ENNReal.toReal (hf.measure_preimage hs.nullMeasurableSet)
  have h₁ := hreal Prod.fst measurePreserving_fst (angularResonance δ) (measurableSet_angularResonance δ)
  have h₂ := hreal Prod.snd measurePreserving_snd (angularResonance δ) (measurableSet_angularResonance δ)
  have h₃ := hreal _ hsub (ball 0 δ) measurableSet_ball
  have h₄ := hreal _ hadd (ball 0 δ) measurableSet_ball
  unfold angularPairExceptions
  calc
    _ ≤ (radianHaar.prod radianHaar).real
          ((Prod.fst ⁻¹' angularResonance δ) ∪ (Prod.snd ⁻¹' angularResonance δ)) +
        (radianHaar.prod radianHaar).real
          (((fun p => p.1 - p.2) ⁻¹' ball 0 δ) ∪ ((fun p => p.1 + p.2) ⁻¹' ball 0 δ)) :=
      measureReal_union_le _ _
    _ ≤ ((radianHaar.prod radianHaar).real (Prod.fst ⁻¹' angularResonance δ) +
          (radianHaar.prod radianHaar).real (Prod.snd ⁻¹' angularResonance δ)) +
        ((radianHaar.prod radianHaar).real ((fun p => p.1 - p.2) ⁻¹' ball 0 δ) +
          (radianHaar.prod radianHaar).real ((fun p => p.1 + p.2) ⁻¹' ball 0 δ)) :=
      add_le_add (measureReal_union_le _ _) (measureReal_union_le _ _)
    _ ≤ (δ / Real.pi + δ / Real.pi) + (δ / Real.pi + δ / Real.pi) := by
      rw [h₁, h₂, h₃, h₄]
      exact add_le_add (add_le_add (radianHaar_angularResonance_le δ hδ)
        (radianHaar_angularResonance_le δ hδ))
        (add_le_add (radianHaar_real_ball_le δ hδ) (radianHaar_real_ball_le δ hδ))
    _ = _ := by ring

/-- Outside the exceptional set, precisely the four covariance separations hold. -/
theorem not_mem_angularPairExceptions_iff (δ : ℝ)
    (θ φ : AddCircle (2 * Real.pi)) :
    (θ, φ) ∉ angularPairExceptions δ ↔
      δ ≤ ‖(2 : ℤ) • θ‖ ∧ δ ≤ ‖(2 : ℤ) • φ‖ ∧ δ ≤ ‖θ - φ‖ ∧ δ ≤ ‖θ + φ‖ := by
  simp only [angularPairExceptions, angularResonance, Set.mem_union, Set.mem_preimage,
    Set.mem_ofPred_eq, mem_ball, dist_zero_right, not_or, not_lt]
  tauto

/-- In real representatives the four conditions are exactly those in the jet estimates. -/
theorem not_mem_angularPairExceptions_coe_iff (δ θ φ : ℝ) :
    ((θ : AddCircle (2 * Real.pi)), (φ : AddCircle (2 * Real.pi))) ∉ angularPairExceptions δ ↔
      δ ≤ ‖((2 * θ : ℝ) : Real.Angle)‖ ∧ δ ≤ ‖((2 * φ : ℝ) : Real.Angle)‖ ∧
        δ ≤ ‖((θ - φ : ℝ) : Real.Angle)‖ ∧ δ ≤ ‖((θ + φ : ℝ) : Real.Angle)‖ := by
  rw [not_mem_angularPairExceptions_iff]
  simp only [← AddCircle.coe_zsmul, zsmul_eq_mul, Int.cast_ofNat,
    ← AddCircle.coe_sub, ← AddCircle.coe_add]
  rfl

/-- Normalized Lebesgue measure on one full interval of radian representatives. -/
def radianIntervalMeasure : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) • volume.restrict (Set.Ioc 0 (2 * Real.pi))

/-- Quotienting a uniform radian representative gives normalized Haar measure. -/
theorem measurePreserving_radianQuotient :
    MeasurePreserving (fun θ : ℝ => (θ : AddCircle (2 * Real.pi)))
      radianIntervalMeasure radianHaar := by
  refine ⟨by fun_prop, ?_⟩
  have h := (AddCircle.measurePreserving_mk (2 * Real.pi) 0).map_eq
  simp only [zero_add] at h
  rw [radianIntervalMeasure, Measure.map_smul _ (by fun_prop), h,
    AddCircle.volume_eq_smul_haarAddCircle, smul_smul]
  rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0),
    ENNReal.ofReal_one, one_smul]

instance : IsProbabilityMeasure radianIntervalMeasure := by
  constructor
  have h := measurePreserving_radianQuotient.measure_preimage (s := Set.univ)
    MeasurableSet.univ.nullMeasurableSet
  simpa using h

/-- The single exceptional set has the same bound in normalized Lebesgue coordinates. -/
theorem radianInterval_angularResonance_le (δ : ℝ) (hδ : 0 ≤ δ) :
    radianIntervalMeasure.real {θ : ℝ | ‖((2 * θ : ℝ) : Real.Angle)‖ < δ} ≤ δ / Real.pi := by
  have hevent : {θ : ℝ | ‖((2 * θ : ℝ) : Real.Angle)‖ < δ} =
      (fun θ : ℝ => (θ : AddCircle (2 * Real.pi))) ⁻¹' angularResonance δ := by
    ext θ
    simp only [angularResonance, Set.mem_preimage, Set.mem_ofPred_eq,
      ← AddCircle.coe_zsmul, zsmul_eq_mul, Int.cast_ofNat]
    rfl
  rw [hevent]
  have heq := measurePreserving_radianQuotient.measure_preimage
    (measurableSet_angularResonance δ).nullMeasurableSet
  change (radianIntervalMeasure _).toReal ≤ _
  rw [heq]
  exact radianHaar_angularResonance_le δ hδ

/-- The four exceptional relations have the same bound in normalized Lebesgue pair coordinates. -/
theorem radianInterval_angularPairExceptions_le (δ : ℝ) (hδ : 0 ≤ δ) :
    (radianIntervalMeasure.prod radianIntervalMeasure).real
      {p : ℝ × ℝ | ‖((2 * p.1 : ℝ) : Real.Angle)‖ < δ ∨
        ‖((2 * p.2 : ℝ) : Real.Angle)‖ < δ ∨
        ‖((p.1 - p.2 : ℝ) : Real.Angle)‖ < δ ∨
        ‖((p.1 + p.2 : ℝ) : Real.Angle)‖ < δ} ≤ 4 * δ / Real.pi := by
  have hevent : {p : ℝ × ℝ | ‖((2 * p.1 : ℝ) : Real.Angle)‖ < δ ∨
        ‖((2 * p.2 : ℝ) : Real.Angle)‖ < δ ∨
        ‖((p.1 - p.2 : ℝ) : Real.Angle)‖ < δ ∨
        ‖((p.1 + p.2 : ℝ) : Real.Angle)‖ < δ} =
      (fun p : ℝ × ℝ => ((p.1 : AddCircle (2 * Real.pi)),
        (p.2 : AddCircle (2 * Real.pi)))) ⁻¹' angularPairExceptions δ := by
    ext p
    rw [Set.mem_preimage, ← not_iff_not, not_mem_angularPairExceptions_coe_iff]
    simp only [Set.mem_ofPred_eq, not_or, not_lt]
  rw [hevent]
  have hp := measurePreserving_radianQuotient.prod measurePreserving_radianQuotient
  have heq := hp.measure_preimage (measurableSet_angularPairExceptions δ).nullMeasurableSet
  change ((radianIntervalMeasure.prod radianIntervalMeasure)
    ((Prod.map (fun θ : ℝ => (θ : AddCircle (2 * Real.pi)))
      (fun θ : ℝ => (θ : AddCircle (2 * Real.pi)))) ⁻¹' angularPairExceptions δ)).toReal ≤ _
  rw [heq]
  exact radianHaar_angularPairExceptions_le δ hδ

/-- The additive equivalence from turns to radians. -/
def turnToRadian : AddCircle (1 : ℝ) ≃+ AddCircle (2 * Real.pi) :=
  AddCircle.equivAddCircle 1 (2 * Real.pi) one_ne_zero (by positivity)

/-- Normalized angular measure is unchanged by converting turns to radians. -/
theorem measurePreserving_turnToRadian :
    MeasurePreserving turnToRadian AddCircle.haarAddCircle radianHaar := by
  exact turnToRadian.toAddMonoidHom.measurePreserving
    (AddCircle.continuous_equivAddCircle _ _ _ _) turnToRadian.surjective (by simp)

/-- The one-point exclusion budget on the unit additive circle used by Fourier sums. -/
theorem haarUnitCircle_angularResonance_le (δ : ℝ) (hδ : 0 ≤ δ) :
    (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))).real
      (turnToRadian ⁻¹' angularResonance δ) ≤ δ / Real.pi := by
  change (AddCircle.haarAddCircle _).toReal ≤ _
  rw [measurePreserving_turnToRadian.measure_preimage
    (measurableSet_angularResonance δ).nullMeasurableSet]
  exact radianHaar_angularResonance_le δ hδ

/-- The two-point exclusion budget on the product of unit additive circles. -/
theorem haarUnitCircle_angularPairExceptions_le (δ : ℝ) (hδ : 0 ≤ δ) :
    ((AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))).prod
      AddCircle.haarAddCircle).real
      ((Prod.map turnToRadian turnToRadian) ⁻¹' angularPairExceptions δ) ≤ 4 * δ / Real.pi := by
  change ((AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) _).toReal ≤ _
  rw [(measurePreserving_turnToRadian.prod measurePreserving_turnToRadian).measure_preimage
    (measurableSet_angularPairExceptions δ).nullMeasurableSet]
  exact radianHaar_angularPairExceptions_le δ hδ

end Erdos522

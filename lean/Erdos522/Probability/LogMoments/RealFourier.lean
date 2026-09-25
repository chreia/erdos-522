/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.UnitIntervalPartition
import Erdos522.Probability.RademacherLogMoments
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Real lifts of finite Rademacher Fourier polynomials

The product of the finite sign law with Lebesgue measure on `[0,1)` maps to
the sign-and-circle probability space. Real lifts preserve all squared energies
and supply the sectionwise `L²` functions used in interval approximation.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos522.LogMoments

/-- The finite sign law together with normalized Lebesgue measure on `[0,1)`. -/
def realFourierMeasure (N : ℕ) : Measure (SignVector N × ℝ) :=
  (signMeasure N).prod unitIntervalMeasure

instance (N : ℕ) : IsProbabilityMeasure (realFourierMeasure N) := by
  unfold realFourierMeasure
  infer_instance

/-- Passing from a real angular coordinate to the normalized additive circle. -/
def realToFourierSpace (N : ℕ) (q : SignVector N × ℝ) :
    SignVector N × AddCircle (1 : ℝ) := (q.1, (q.2 : AddCircle (1 : ℝ)))

/-- The Fourier polynomial expressed in a real angular coordinate. -/
def realFourier {N : ℕ} (a : Fin (N + 1) → ℂ) (q : SignVector N × ℝ) : ℂ :=
  randomFourier a (realToFourierSpace N q)

theorem measurePreserving_realToFourierSpace (N : ℕ) :
    MeasurePreserving (realToFourierSpace N) (realFourierMeasure N) (fourierMeasure N) :=
  (MeasurePreserving.id (signMeasure N)).prod measurePreserving_unitInterval_toCircle

theorem measurable_realFourier {N : ℕ} (a : Fin (N + 1) → ℂ) :
    Measurable (realFourier a) :=
  (measurable_randomFourier a).comp (measurePreserving_realToFourierSpace N).measurable

/-- Measurable integrands have the same integral on the real lift and on the
    sign-and-circle space. -/
theorem integral_realToFourierSpace_eq {N : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : SignVector N × AddCircle (1 : ℝ) → E)
    (hf : AEStronglyMeasurable f (fourierMeasure N)) :
    (∫ q, f (realToFourierSpace N q) ∂realFourierMeasure N) = ∫ q, f q ∂fourierMeasure N := by
  have hp := measurePreserving_realToFourierSpace N
  have hm : AEStronglyMeasurable f (Measure.map (realToFourierSpace N) (realFourierMeasure N)) := by
    rwa [hp.map_eq]
  have h := integral_map hp.measurable.aemeasurable hm
  rw [hp.map_eq] at h
  exact h.symm

/-- Squared norms of real Fourier lifts are integrable. -/
theorem integrable_norm_sq_realFourier {N : ℕ} (a : Fin (N + 1) → ℂ) :
    Integrable (fun q => ‖realFourier a q‖ ^ 2) (realFourierMeasure N) := by
  exact ((measurePreserving_realToFourierSpace N).integrable_comp
    ((measurable_randomFourier a).norm.pow_const 2).aestronglyMeasurable).mpr
      (integrable_norm_sq_randomFourier a)

/-- The real lift belongs to `L²` under the actual sign-and-interval law. -/
theorem memLp_realFourier {N : ℕ} (a : Fin (N + 1) → ℂ) :
    MemLp (realFourier a) 2 (realFourierMeasure N) :=
  (memLp_two_iff_integrable_sq_norm (measurable_realFourier a).aestronglyMeasurable).mpr
    (integrable_norm_sq_realFourier a)

/-- Each fixed-sign angular section is an `L²` function on the real unit
    interval. -/
theorem memLp_realFourier_section {N : ℕ} (a : Fin (N + 1) → ℂ) (ω : SignVector N) :
    MemLp (fun x : ℝ => realFourier a (ω, x)) 2 unitIntervalMeasure := by
  have hc := continuous_fourierPolynomial a ω
  have hi : Integrable (fun θ => ‖fourierPolynomial a ω θ‖ ^ 2)
      AddCircle.haarAddCircle :=
    (hc.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcircle : MemLp (fourierPolynomial a ω) 2 AddCircle.haarAddCircle :=
    (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr hi
  exact hcircle.comp_measurePreserving measurePreserving_unitInterval_toCircle

/-- Real-lift and circle squared energies are identical. -/
theorem integral_norm_sq_realFourier_eq_circle {N : ℕ} (a : Fin (N + 1) → ℂ) :
    (∫ q, ‖realFourier a q‖ ^ 2 ∂realFourierMeasure N) =
      ∫ q, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N :=
  integral_realToFourierSpace_eq _
    ((measurable_randomFourier a).norm.pow_const 2).aestronglyMeasurable

/-- Parseval for the finite sign law and the half-open real unit interval. -/
theorem integral_norm_sq_realFourier {N : ℕ} (a : Fin (N + 1) → ℂ) :
    (∫ q, ‖realFourier a q‖ ^ 2 ∂realFourierMeasure N) = ∑ k, ‖a k‖ ^ 2 := by
  rw [integral_norm_sq_realFourier_eq_circle, integral_norm_sq_randomFourier]

/-- Parseval also holds for every fixed-sign real section. -/
theorem integral_norm_sq_realFourier_section {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) :
    (∫ x, ‖realFourier a (ω, x)‖ ^ 2 ∂unitIntervalMeasure) = ∑ k, ‖a k‖ ^ 2 := by
  change (∫ x, ‖fourierPolynomial a ω (x : AddCircle (1 : ℝ))‖ ^ 2 ∂unitIntervalMeasure) = _
  rw [integral_unitInterval_lift_eq_haar (fun θ => ‖fourierPolynomial a ω θ‖ ^ 2),
    integral_norm_sq_fourierPolynomial]

end Erdos522.LogMoments

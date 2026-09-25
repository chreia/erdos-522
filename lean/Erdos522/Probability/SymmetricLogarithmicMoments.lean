/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SymmetricSignRepresentation

/-!
# Logarithmic moments for symmetric coefficients on an energy event

Independent signs preserve a centrally symmetric coefficient law. The energy
event is invariant under those signs, so the conditional Rademacher estimate
transfers to the original coefficient-and-angle product law.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Erdos522

/-- A weighted Fourier polynomial evaluated at a coefficient vector and angle. -/
def weightedCoefficientFourier {N : ℕ} (c : Fin (N + 1) → ℂ)
    (q : (Fin (N + 1) → ℂ) × AddCircle (1 : ℝ)) : ℂ :=
  ∑ k, c k * q.1 k * fourier k.val q.2

/-- Coefficient vectors whose weighted energy lies in the specified amplitude range. -/
def coefficientEnergyEvent {N : ℕ} (c : Fin (N + 1) → ℂ) (B : ℝ) :
    Set (Fin (N + 1) → ℂ) :=
  {a | 1 / 2 ≤ ∑ k, ‖c k * a k‖ ^ 2 ∧ (∑ k, ‖c k * a k‖ ^ 2) ≤ B ^ 2}

theorem measurableSet_coefficientEnergyEvent {N : ℕ} (c : Fin (N + 1) → ℂ) (B : ℝ) :
    MeasurableSet (coefficientEnergyEvent c B) := by
  unfold coefficientEnergyEvent
  have hm : Measurable (fun a : Fin (N + 1) → ℂ => ∑ k, ‖c k * a k‖ ^ 2) := by fun_prop
  exact (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)

/-- Independent amplitude, sign, and angle coordinates can be ordered so that
the signed coefficient vector has the original symmetric law. -/
theorem measurePreserving_amplitude_sign_angle {N : ℕ}
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] :
    MeasurePreserving
      (fun q : (Fin (N + 1) → ℂ) × (LogMoments.SignVector N × AddCircle (1 : ℝ)) =>
        ((fun k => LogMoments.sign (q.2.1 k) * q.1 k), q.2.2))
      ((Measure.pi μ).prod (LogMoments.fourierMeasure N))
      ((Measure.pi μ).prod AddCircle.haarAddCircle) := by
  have hassoc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (Measure.pi μ) (LogMoments.signMeasure N) (AddCircle.haarAddCircle (T := (1 : ℝ))))
  have hswap := (Measure.measurePreserving_swap (μ := Measure.pi μ) (ν := LogMoments.signMeasure N)).prod
    (show MeasurePreserving (fun θ : AddCircle (1 : ℝ) => θ)
      AddCircle.haarAddCircle AddCircle.haarAddCircle from ⟨measurable_id, Measure.map_id⟩)
  exact (measurePreserving_rademacher_amplitudes_and_angle μ).comp (hswap.comp hassoc)

/-- The original product of centrally symmetric complex coefficient laws
satisfies the coefficient-uniform logarithmic estimate on its energy event. -/
theorem symmetric_event_restricted_logarithmic_moments {N : ℕ}
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] (c : Fin (N + 1) → ℂ) (B : ℝ)
    {p : ℝ} (hp : 1 ≤ p) :
    IntegrableOn (fun q => |Real.log ‖weightedCoefficientFourier c q‖| ^ p)
      (coefficientEnergyEvent c B ×ˢ univ) ((Measure.pi μ).prod AddCircle.haarAddCircle) ∧
    (∫ q in coefficientEnergyEvent c B ×ˢ univ,
      |Real.log ‖weightedCoefficientFourier c q‖| ^ p
      ∂((Measure.pi μ).prod AddCircle.haarAddCircle)) ≤
        (LogMoments.amplitudeLogarithmicConstant B * p) ^ (6 * p) := by
  let E := coefficientEnergyEvent c B
  let T := fun q : (Fin (N + 1) → ℂ) × (LogMoments.SignVector N × AddCircle (1 : ℝ)) =>
    ((fun k => LogMoments.sign (q.2.1 k) * q.1 k), q.2.2)
  let f := fun q : (Fin (N + 1) → ℂ) × AddCircle (1 : ℝ) =>
    |Real.log ‖weightedCoefficientFourier c q‖| ^ p
  have hE := measurableSet_coefficientEnergyEvent c B
  have hT := measurePreserving_amplitude_sign_angle μ
  have hpre : T ⁻¹' (E ×ˢ univ) = E ×ˢ univ := by
    ext q
    simp only [T, Set.mem_preimage, Set.mem_prod, mem_univ, and_true, E,
      coefficientEnergyEvent, Set.mem_ofPred_eq, norm_mul, LogMoments.norm_sign, one_mul]
  have hTr : MeasurePreserving T
      (((Measure.pi μ).prod (LogMoments.fourierMeasure N)).restrict (E ×ˢ univ))
      (((Measure.pi μ).prod AddCircle.haarAddCircle).restrict (E ×ˢ univ)) := by
    refine ⟨hT.measurable, ?_⟩
    rw [← hpre, ← Measure.restrict_map hT.measurable (hE.prod MeasurableSet.univ), hT.map_eq]
  have hf : Measurable f := by
    have hw : Measurable (weightedCoefficientFourier c) := by
      unfold weightedCoefficientFourier
      fun_prop
    simpa only [f, Real.norm_eq_abs] using hw.norm.log.norm.pow_const p
  have heq (q) : f (T q) =
      |Real.log ‖LogMoments.randomFourier (fun k => c k * q.1 k) q.2‖| ^ p := by
    have hw : weightedCoefficientFourier c (T q) =
        LogMoments.randomFourier (fun k => c k * q.1 k) q.2 := by
      simp only [weightedCoefficientFourier, LogMoments.randomFourier,
        LogMoments.fourierPolynomial_eq_sum, T]
      apply Finset.sum_congr rfl
      intro k _
      ring
    exact congrArg (fun z : ℂ => |Real.log ‖z‖| ^ p) hw
  obtain ⟨hI, hbound⟩ := LogMoments.event_restricted_logarithmic_moments (Measure.pi μ)
    (fun a k => c k * a k) (fun k => measurable_const.mul (measurable_pi_apply k))
    E hE (fun _ h => h.1) (fun _ h => h.2) hp
  have hcomp : Integrable (f ∘ T)
      (((Measure.pi μ).prod (LogMoments.fourierMeasure N)).restrict (E ×ˢ univ)) := by
    simpa only [IntegrableOn, Function.comp_def, heq] using hI
  have hfI := (hTr.integrable_comp hf.aestronglyMeasurable).mp hcomp
  refine ⟨hfI, ?_⟩
  change (∫ q, f q ∂(((Measure.pi μ).prod AddCircle.haarAddCircle).restrict (E ×ˢ univ))) ≤ _
  rw [← hTr.map_eq, integral_map hTr.measurable.aemeasurable hf.aestronglyMeasurable]
  simpa only [heq] using hbound

end Erdos522

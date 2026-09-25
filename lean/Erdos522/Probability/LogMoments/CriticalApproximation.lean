/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.CriticalShifts
import Erdos522.Probability.LogMoments.RestrictedApproximation

/-!
# Local Fourier approximation at the critical shift scale

Every event of positive measure either captures a definite fraction of the
Fourier energy or admits coefficient-uniform local approximation at a scale
whose angular translation adds a prescribed amount of measure.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Erdos522.LogMoments

/-- The critical-shift dichotomy with its local exponential approximants and
explicit squared-error bound, on the actual finite Rademacher model. -/
theorem critical_approximation_or_restricted_energy {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (p : ℕ) (hp : 1 ≤ p) :
    let n := shiftOrder ((fourierMeasure N).real E) p
    (∀ a : Fin (N + 1) → ℂ, (∑ k, ‖a k‖ ^ 2 = 1) →
      (fourierMeasure N).real E / 4 ≤
        ∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) ∨
    (∃ τ : ℝ, 0 < τ ∧ (n : ℝ) * τ < 1 ∧
      angularTranslationLoss E (((n : ℝ) * τ : ℝ) : AddCircle (1 : ℝ)) =
        (fourierMeasure N).real E / (2 * (n : ℝ)) ∧
      ∀ a : Fin (N + 1) → ℂ, (∑ k, ‖a k‖ ^ 2 = 1) →
        ∃ (m : ℕ) (ξ : Fin m → ℝ), m ≤ n ∧ Function.Injective ξ ∧
          ∀ (q : ℕ), 0 < q → ∀ M : ℝ, 1 ≤ M → 1 / (q : ℝ) = M * τ →
            ∃ Φ : SignVector N × ℝ → ℝ,
              (∀ z, 0 ≤ Φ z) ∧ MemLp Φ 2 (realFourierMeasure N) ∧
              (∫ z, Φ z ^ 2 ∂realFourierMeasure N) ≤
                restrictedApproximationConstant n ((fourierMeasure N).real E) *
                  (∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) ∧
              ∀ i : Fin q, ∃ P : SignVector N → ℝ → ℂ,
                (∀ ω, P ω ∈ exponentialSpan (Set.range ξ)) ∧
                ∀ ω x, x ∈ unitIntervalCell i →
                  ‖realFourier a (ω, x) - P ω x‖ ≤ M ^ n * Φ (ω, x)) := by
  dsimp only
  rcases critical_shift_or_restricted_energy E hE hpos p hp with henergy | hcritical
  · exact Or.inl henergy
  · obtain ⟨τ, hτ, hperiod, hgain, hsmall⟩ := hcritical
    refine Or.inr ⟨τ, hτ, hperiod, hgain, fun a ha => ?_⟩
    have hB : 0 < (4 * ((shiftOrder ((fourierMeasure N).real E) p : ℝ) + 1) /
        (fourierMeasure N).real E) *
        (∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) :=
      mul_pos (div_pos (by positivity) hpos) (restricted_fourier_energy_pos a ha E hpos)
    obtain ⟨Λ, hΛ, hcard, hweight⟩ := exists_distinct_weighted_spectrum_of_shift_relations a
      hτ hB (fun t => hsmall t.val t.property.1 t.property.2 a)
    exact exists_fourier_approximation_of_distinct_spectrum a E hτ Λ hΛ hcard hweight

end Erdos522.LogMoments

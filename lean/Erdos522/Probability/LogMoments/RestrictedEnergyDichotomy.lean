/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.AngularSections
import Erdos522.Probability.LogMoments.LongSections

/-!
# Translation loss or restricted Fourier energy

If angular translations change little of an event, many sign fibers contain
nearly the whole circle. Parseval on those fibers and the uniform moment bound
then force a definite fraction of every normalized Fourier sum's energy into
the event.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos522.LogMoments

/-- Small translation loss forces a coefficient-uniform lower bound for restricted energy. -/
theorem restricted_energy_lower_bound_of_small_translation_loss {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (p : ℕ) (hp : 1 ≤ p)
    {n : ℝ} (hn : 2 ≤ n)
    (horder : 512 * Real.exp 4 * (p : ℝ) ^ 2 *
      (fourierMeasure N).real E ^ (-(1 / (p : ℝ))) ≤ n)
    (hloss : ∀ t : AddCircle (1 : ℝ), angularTranslationLoss E t <
      (fourierMeasure N).real E / (2 * n))
    (a : Fin (N + 1) → ℂ) (ha : ∑ k, ‖a k‖ ^ 2 = 1) :
    (fourierMeasure N).real E / 4 ≤
      ∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N := by
  apply restricted_energy_ge_of_long_sections a ha E hE (longSections E n) hpos
    (half_measure_lt_longSections hE (by linarith) hloss).le
    (measure_longSections_hole_le_twice hE hn) p hp horder

/-- Every positive-measure event either has a substantial translation loss or
    captures a fixed fraction of the energy of every normalized Fourier sum. -/
theorem restricted_energy_dichotomy {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (p : ℕ) (hp : 1 ≤ p)
    {n : ℝ} (hn : 2 ≤ n)
    (horder : 512 * Real.exp 4 * (p : ℝ) ^ 2 *
      (fourierMeasure N).real E ^ (-(1 / (p : ℝ))) ≤ n) :
    (∃ t : AddCircle (1 : ℝ), (fourierMeasure N).real E / (2 * n) ≤
      angularTranslationLoss E t) ∨
    (∀ a : Fin (N + 1) → ℂ, (∑ k, ‖a k‖ ^ 2 = 1) →
      (fourierMeasure N).real E / 4 ≤
        ∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N) := by
  by_cases h : ∀ t : AddCircle (1 : ℝ), angularTranslationLoss E t <
      (fourierMeasure N).real E / (2 * n)
  · exact Or.inr (restricted_energy_lower_bound_of_small_translation_loss E hE hpos p hp hn horder h)
  · push Not at h
    exact Or.inl h

end Erdos522.LogMoments

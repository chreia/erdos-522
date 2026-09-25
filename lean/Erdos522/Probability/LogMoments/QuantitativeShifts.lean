/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.RestrictedEnergySubspace
import Erdos522.Probability.LogMoments.TranslationSets

/-!
# Quantitative small-shift relations for Rademacher Fourier sums

The order depends only on the event measure and the chosen moment order.
A single positive interval of shift parameters works for every coefficient
vector. Spectral truncation and translation of the integration set give the
explicit energy loss.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos522.LogMoments

/-- The number of shifts needed to overcome the restricted-energy exceptional subspace. -/
def shiftOrder (δ : ℝ) (m : ℕ) : ℕ :=
  ⌈(32 * Real.exp 2 * (m : ℝ)) ^ 2 * (δ / 2) ^ (-(1 / (m : ℝ)))⌉₊

/-- Passing to a subset of at least half the original measure respects the chosen order. -/
theorem restricted_dimension_le_shiftOrder {δ ε : ℝ} (hδ : 0 < δ)
    (hε : δ / 2 ≤ ε) (m : ℕ) (hm : 1 ≤ m) :
    (32 * Real.exp 2 * (m : ℝ)) ^ 2 * ε ^ (-(1 / (m : ℝ))) ≤ shiftOrder δ m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  calc
    _ ≤ (32 * Real.exp 2 * (m : ℝ)) ^ 2 * (δ / 2) ^ (-(1 / (m : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hε (neg_nonpos.mpr (by positivity))
    _ ≤ shiftOrder δ m := Nat.le_ceil _

/-- A half-measure shift intersection gives a normalized relation for the
prescribed shift, uniformly over Fourier coefficients. -/
theorem exists_small_shift_relation_of_half_measure {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ)))
    (hpos : 0 < (fourierMeasure N).real E) (m : ℕ) (hm : 1 ≤ m)
    (t : AddCircle (1 : ℝ))
    (hhalf : (fourierMeasure N).real E / 2 ≤
      (fourierMeasure N).real (shiftIntersection E (shiftOrder ((fourierMeasure N).real E) m) t))
    (a : Fin (N + 1) → ℂ) :
    ∃ c : Fin (shiftOrder ((fourierMeasure N).real E) m + 1) → ℂ,
      (∑ j, ‖c j‖ ^ 2) = 1 ∧
      (∫ q, ‖∑ j, c j * randomFourier a
        (angularTranslation N (j.val • t) q)‖ ^ 2 ∂fourierMeasure N) ≤
        (4 * ((shiftOrder ((fourierMeasure N).real E) m : ℝ) + 1) /
          (fourierMeasure N).real E) *
          ∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N := by
  let n := shiftOrder ((fourierMeasure N).real E) m
  let E' := shiftIntersection E n t
  have hpos' : 0 < (fourierMeasure N).real E' := lt_of_lt_of_le (by positivity) hhalf
  obtain ⟨V, hdim, hcoercive⟩ := exists_restricted_energy_subspace E' hpos' m hm
  have hV : Module.finrank ℂ V ≤ n := by
    exact_mod_cast hdim.trans (restricted_dimension_le_shiftOrder hpos hhalf m hm)
  apply exists_small_shift_energy_le a E t V hV hpos
  intro b hb
  have h := hcoercive b hb
  calc
    ((fourierMeasure N).real E / 4) * ∑ k, ‖b k‖ ^ 2 ≤
        ((fourierMeasure N).real E' / 2) * ∑ k, ‖b k‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right (by linarith)
          exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
    _ ≤ _ := h


/-- Every positive-measure event admits coefficient-uniform normalized small-shift relations.
    The order and the loss are explicit, and the shift radius is independent of the coefficients. -/
theorem exists_quantitative_small_shifts {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (m : ℕ) (hm : 1 ≤ m) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ t : ℝ, 0 < t → t < τ →
      ∀ a : Fin (N + 1) → ℂ,
      ∃ c : Fin (shiftOrder ((fourierMeasure N).real E) m + 1) → ℂ,
        (∑ j, ‖c j‖ ^ 2) = 1 ∧
        (∫ q, ‖∑ j, c j * randomFourier a
          (angularTranslation N (j.val • (t : AddCircle (1 : ℝ))) q)‖ ^ 2
            ∂fourierMeasure N) ≤
          (4 * ((shiftOrder ((fourierMeasure N).real E) m : ℝ) + 1) /
            (fourierMeasure N).real E) *
              ∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N := by
  let n := shiftOrder ((fourierMeasure N).real E) m
  obtain ⟨τ, hτ, hsmall⟩ := exists_shift_radius hE hpos n
  refine ⟨τ, hτ, ?_⟩
  intro t ht0 htτ a
  exact exists_small_shift_relation_of_half_measure E hpos m hm
    (t : AddCircle (1 : ℝ)) (hsmall t ht0 htτ) a

end Erdos522.LogMoments

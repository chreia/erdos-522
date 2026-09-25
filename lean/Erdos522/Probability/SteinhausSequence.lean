/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CoefficientSequence
import Erdos522.Probability.SteinhausLaw

/-!
# A shared infinite Steinhaus sequence

Finite restrictions have the independent uniform-circle law. All
coefficients have modulus one on a single event, so every prefix has its
nominal degree and a nonzero constant coefficient.
-/

noncomputable section
open MeasureTheory Polynomial Filter
namespace Erdos522

/-- The law of one infinite sequence of independent uniform-circle coefficients. -/
def steinhausSequenceMeasure : Measure (ℕ → ℂ) :=
  coefficientSequenceMeasure steinhausMeasure

instance : IsProbabilityMeasure steinhausSequenceMeasure := by
  unfold steinhausSequenceMeasure
  infer_instance

/-- Every coefficient has modulus one simultaneously almost surely. -/
theorem ae_steinhausSequence_norm :
    ∀ᵐ ω ∂steinhausSequenceMeasure, ∀ k, ‖ω k‖ = 1 :=
  ae_coefficientSequence_coordinates steinhausMeasure (fun z => ‖z‖ = 1)
    ae_norm_steinhaus_eq_one

/-- Every finite Steinhaus prefix has its nominal degree and a nonzero constant. -/
theorem ae_steinhausPrefix_degree_and_constant :
    ∀ᵐ ω ∂steinhausSequenceMeasure, ∀ N,
      (Polynomial.ofFn (N + 1) (coefficientPrefix N ω)).natDegree = N ∧
      (Polynomial.ofFn (N + 1) (coefficientPrefix N ω)).coeff 0 ≠ 0 := by
  have hnonzero : ∀ᵐ z ∂steinhausMeasure, z ≠ 0 :=
    ae_norm_steinhaus_eq_one.mono (fun z hz => norm_pos_iff.mp (by rw [hz]; norm_num))
  have hzero : steinhausMeasure {0} = 0 := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using hnonzero
  simpa only [steinhausSequenceMeasure, coefficientPrefix_polynomial] using
    ae_polynomialPrefix_degree_and_constant steinhausMeasure hzero

/-- Indexed finite exceptions with summable outer probabilities eventually
cease along the shared Steinhaus sequence. -/
theorem ae_eventually_indexed_steinhausPrefix_notMem (n : ℕ → ℕ)
    (E : ∀ j, Set (Fin (n j + 1) → ℂ))
    (hs : Summable (fun j =>
      (Measure.pi (fun _ : Fin (n j + 1) => steinhausMeasure)).real (E j))) :
    ∀ᵐ ω ∂steinhausSequenceMeasure, ∀ᶠ j in atTop, coefficientPrefix (n j) ω ∉ E j :=
  ae_eventually_indexed_coefficientPrefix_notMem steinhausMeasure n E hs

end Erdos522

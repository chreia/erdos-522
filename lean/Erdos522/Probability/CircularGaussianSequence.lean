/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianCoefficients
import Erdos522.Probability.CoefficientSequence

/-!
# A shared circular Gaussian coefficient sequence

Finite restrictions have the independent standard circular complex Gaussian
law. Almost surely every coefficient is nonzero, so all prefixes have their
nominal degree and nonzero constant coefficient on one event.
-/

noncomputable section
open MeasureTheory Polynomial Filter
namespace Erdos522

/-- The law of one infinite circular complex Gaussian coefficient sequence. -/
def circularGaussianSequenceMeasure : Measure (ℕ → ℂ) :=
  coefficientSequenceMeasure circularComplexGaussian

instance : IsProbabilityMeasure circularGaussianSequenceMeasure := by
  unfold circularGaussianSequenceMeasure
  infer_instance

/-- A circular complex Gaussian coefficient is almost surely nonzero. -/
theorem circularComplexGaussian_ae_ne_zero : ∀ᵐ z ∂circularComplexGaussian, z ≠ 0 :=
  ae_circularComplexGaussian_ne_zero

/-- Every coefficient is nonzero on one probability-one event. -/
theorem ae_circularGaussianSequence_nonzero :
    ∀ᵐ ω ∂circularGaussianSequenceMeasure, ∀ k, ω k ≠ 0 :=
  ae_coefficientSequence_coordinates circularComplexGaussian (fun z => z ≠ 0)
    circularComplexGaussian_ae_ne_zero

/-- Every finite prefix has its nominal degree and a nonzero constant coefficient. -/
theorem ae_circularGaussianPrefix_degree_and_constant :
    ∀ᵐ ω ∂circularGaussianSequenceMeasure, ∀ N,
      (Polynomial.ofFn (N + 1) (coefficientPrefix N ω)).natDegree = N ∧
      (Polynomial.ofFn (N + 1) (coefficientPrefix N ω)).coeff 0 ≠ 0 := by
  have hzero : circularComplexGaussian {0} = 0 := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using
      ae_circularComplexGaussian_ne_zero
  simpa only [circularGaussianSequenceMeasure, coefficientPrefix_polynomial] using
    ae_polynomialPrefix_degree_and_constant circularComplexGaussian hzero

/-- Summable arbitrary finite exceptions transfer to the shared circular Gaussian sequence. -/
theorem ae_eventually_indexed_circularGaussianPrefix_notMem (n : ℕ → ℕ)
    (E : ∀ j, Set (Fin (n j + 1) → ℂ))
    (hs : Summable (fun j =>
      (Measure.pi (fun _ : Fin (n j + 1) => circularComplexGaussian)).real (E j))) :
    ∀ᵐ ω ∂circularGaussianSequenceMeasure, ∀ᶠ j in atTop, coefficientPrefix (n j) ω ∉ E j :=
  ae_eventually_indexed_coefficientPrefix_notMem circularComplexGaussian n E hs

end Erdos522

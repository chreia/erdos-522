/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.RelativeCovarianceEntropy
import Erdos522.Probability.EntropyComparison

/-!
# Event probabilities for nearby Gaussian covariance matrices

A quadratic perturbation estimate, a positive lower covariance bound, and
Pinsker's inequality give a uniform comparison for every measurable event.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal MatrixOrder

namespace Erdos522

/-- Event probabilities of two centered Gaussians differ by at most
`√(d/2)` times the relative quadratic covariance error. -/
theorem gaussian_measureReal_sub_le_of_quadratic_error {d : ℕ}
    (S T : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef) (hT : T.PosDef)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) (hsmall : δ / c ≤ 1 / 2)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin d), c * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ T *ᵥ x.ofLp)
    (herror : ∀ x : EuclideanSpace ℝ (Fin d),
      |x.ofLp ⬝ᵥ (S - T) *ᵥ x.ofLp| ≤ δ * ‖x‖ ^ 2)
    (E : Set (EuclideanSpace ℝ (Fin d))) (hE : MeasurableSet E) :
    |(multivariateGaussian 0 S).real E - (multivariateGaussian 0 T).real E| ≤
      Real.sqrt ((d : ℝ) / 2) * (δ / c) := by
  have hkl := klDiv_multivariateGaussian_le_of_quadratic_error S T hS hT c δ hc hδ
    hsmall hlower herror
  have h := abs_measureReal_sub_le_of_klDiv_le _ _ (by positivity) hkl E hE
  have hsqrt : Real.sqrt ((d : ℝ) * (δ / c) ^ 2 / 2) =
      Real.sqrt ((d : ℝ) / 2) * (δ / c) := by
    rw [show (d : ℝ) * (δ / c) ^ 2 / 2 = ((d : ℝ) / 2) * (δ / c) ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (div_nonneg hδ hc.le)]
  exact h.trans_eq hsqrt

/-- The four-dimensional Gaussian comparison has constant `√2`. -/
theorem gaussian_measureReal_sub_le_four
    (S T : Matrix (Fin 4) (Fin 4) ℝ) (hS : S.PosDef) (hT : T.PosDef)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) (hsmall : δ / c ≤ 1 / 2)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin 4), c * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ T *ᵥ x.ofLp)
    (herror : ∀ x : EuclideanSpace ℝ (Fin 4),
      |x.ofLp ⬝ᵥ (S - T) *ᵥ x.ofLp| ≤ δ * ‖x‖ ^ 2)
    (E : Set (EuclideanSpace ℝ (Fin 4))) (hE : MeasurableSet E) :
    |(multivariateGaussian 0 S).real E - (multivariateGaussian 0 T).real E| ≤
      Real.sqrt 2 * (δ / c) := by
  simpa only [Nat.cast_ofNat, show (4 : ℝ) / 2 = 2 by norm_num] using
    gaussian_measureReal_sub_le_of_quadratic_error S T hS hT c δ hc hδ hsmall hlower herror E hE

/-- The eight-dimensional Gaussian comparison has constant `2`. -/
theorem gaussian_measureReal_sub_le_eight
    (S T : Matrix (Fin 8) (Fin 8) ℝ) (hS : S.PosDef) (hT : T.PosDef)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) (hsmall : δ / c ≤ 1 / 2)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin 8), c * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ T *ᵥ x.ofLp)
    (herror : ∀ x : EuclideanSpace ℝ (Fin 8),
      |x.ofLp ⬝ᵥ (S - T) *ᵥ x.ofLp| ≤ δ * ‖x‖ ^ 2)
    (E : Set (EuclideanSpace ℝ (Fin 8))) (hE : MeasurableSet E) :
    |(multivariateGaussian 0 S).real E - (multivariateGaussian 0 T).real E| ≤
      2 * (δ / c) := by
  have h := gaussian_measureReal_sub_le_of_quadratic_error S T hS hT c δ hc hδ hsmall hlower herror E hE
  norm_num at h ⊢
  exact h

end Erdos522

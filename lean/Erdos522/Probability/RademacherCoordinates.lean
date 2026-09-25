/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.RademacherLogMoments
import Mathlib.Probability.Moments.SubGaussian

/-!
# Independent Rademacher coordinates

The uniform product law on Boolean vectors realizes independent fair signs.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos522.LogMoments

/-- The real-valued sign associated with a Boolean coin. -/
def realSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem ofReal_realSign (b : Bool) : (realSign b : ℂ) = sign b := by
  cases b <;> simp [realSign, sign]

@[simp] theorem abs_realSign (b : Bool) : |realSign b| = 1 := by
  cases b <;> norm_num [realSign]

/-- A fair sign has mean zero. -/
theorem integral_realSign :
    (∫ b, realSign b ∂(PMF.uniformOfFintype Bool).toMeasure) = 0 := by
  rw [integral_fintype Integrable.of_finite]
  simp [Measure.real, PMF.uniformOfFintype_apply, realSign]

/-- A fair sign has sub-Gaussian variance proxy one. -/
theorem hasSubgaussianMGF_realSign :
    HasSubgaussianMGF realSign 1 (PMF.uniformOfFintype Bool).toMeasure := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := (PMF.uniformOfFintype Bool).toMeasure)
    (a := (-1 : ℝ)) (b := (1 : ℝ))
    (measurable_of_finite realSign).aemeasurable
    (ae_of_all _ (fun b => by cases b <;> norm_num [realSign])) integral_realSign
  norm_num at h ⊢
  exact h

/-- Coordinate signs are independent under the finite product law. -/
theorem iIndepFun_realSign (N : ℕ) :
    iIndepFun (fun k (ω : SignVector N) => realSign (ω k)) (signMeasure N) := by
  exact iIndepFun_pi (fun _ => (measurable_of_finite realSign).aemeasurable)

/-- Each coordinate of the product sign law has variance proxy one. -/
theorem hasSubgaussianMGF_coordinate {N : ℕ} (k : Fin (N + 1)) :
    HasSubgaussianMGF (fun ω : SignVector N => realSign (ω k)) 1 (signMeasure N) := by
  have hmap := (measurePreserving_eval
    (fun _ : Fin (N + 1) => (PMF.uniformOfFintype Bool).toMeasure) k).map_eq
  apply HasSubgaussianMGF.of_map (X := realSign) (μ := signMeasure N)
    (measurable_pi_apply k).aemeasurable
  simpa only [signMeasure, hmap] using hasSubgaussianMGF_realSign

@[simp] theorem realSign_sq (b : Bool) : realSign b ^ 2 = 1 := by
  cases b <;> norm_num [realSign]

/-- Each fair coordinate has mean zero under the product measure. -/
theorem integral_realSign_coordinate {N : ℕ} (k : Fin (N + 1)) :
    (∫ ω : SignVector N, realSign (ω k) ∂signMeasure N) = 0 := by
  have hmap := (measurePreserving_eval
    (fun _ : Fin (N + 1) => (PMF.uniformOfFintype Bool).toMeasure) k).map_eq
  rw [← integral_realSign, ← hmap]
  exact (integral_map (measurable_pi_apply k).aemeasurable
    (measurable_of_finite realSign).aestronglyMeasurable).symm

/-- The second-moment matrix of independent fair signs is the identity. -/
theorem integral_mul_realSign_coordinates {N : ℕ} (i j : Fin (N + 1)) :
    (∫ ω : SignVector N, realSign (ω i) * realSign (ω j) ∂signMeasure N) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [← pow_two]
  · have hind := (iIndepFun_realSign N).indepFun hij
    have h := hind.integral_mul_eq_mul_integral
      (measurable_of_finite _).aestronglyMeasurable
      (measurable_of_finite _).aestronglyMeasurable
    simpa [Pi.mul_apply, integral_realSign_coordinate, hij] using h

end Erdos522.LogMoments

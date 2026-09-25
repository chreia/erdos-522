/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SymmetricLogarithmicMoments
import Erdos522.Probability.RademacherLogarithmicConcentration

/-!
# Radial Fourier normalization for complex coefficient vectors

Weighted finite Fourier sums agree with polynomial evaluation after exact
variance normalization. The radian-to-circle conversion preserves the
normalized angular measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
open scoped BigOperators
namespace Erdos522

/-- The exactly normalized polynomial modulus in radian coordinates. -/
def normalizedCoefficientValueModulus (N : ℕ) (r : ℝ)
    (p : ℝ × (Fin (N + 1) → ℂ)) : ℝ :=
  ‖weightedCoefficientFourier (normalizedRadialCoefficients N r) (p.2, radianToUnitCircle p.1)‖

theorem continuous_weightedCoefficientFourier {N : ℕ} (c : Fin (N + 1) → ℂ) :
    Continuous (weightedCoefficientFourier c) := by
  unfold weightedCoefficientFourier
  fun_prop

@[fun_prop]
theorem measurable_normalizedCoefficientValueModulus (N : ℕ) (r : ℝ) :
    Measurable (normalizedCoefficientValueModulus N r) := by
  unfold normalizedCoefficientValueModulus
  exact ((continuous_weightedCoefficientFourier _).measurable.comp
    (measurable_snd.prodMk (measurePreserving_radianToUnitCircle.measurable.comp measurable_fst))).norm

/-- The radial Fourier expression equals normalized polynomial evaluation. -/
theorem weightedCoefficientFourier_radial_eq (N : ℕ) (r : ℝ)
    (a : Fin (N + 1) → ℂ) (θ : AddCircle (1 : ℝ)) :
    weightedCoefficientFourier (normalizedRadialCoefficients N r) (a, θ) =
      (Polynomial.ofFn (N + 1) a).eval ((r : ℂ) * AddCircle.toCircle θ) / radialSigma N r := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    weightedCoefficientFourier, normalizedRadialCoefficients, Finset.sum_div, mul_pow]
  apply Finset.sum_congr rfl
  intro k _
  simp only [fourier_apply, AddCircle.toCircle_zsmul, zpow_natCast, Circle.coe_pow]
  ring

theorem normalizedCoefficientValueModulus_eq (N : ℕ) (r θ : ℝ) (a : Fin (N + 1) → ℂ) :
    normalizedCoefficientValueModulus N r (θ, a) =
      ‖(Polynomial.ofFn (N + 1) a).eval (r * Complex.exp (Complex.I * θ))‖ / radialSigma N r := by
  simp only [normalizedCoefficientValueModulus, weightedCoefficientFourier_radial_eq,
    toCircle_radianToUnitCircle, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (radialSigma_pos N r)]

/-- Squared normalized values are angularly integrable for every coefficient vector. -/
theorem integrable_normalizedCoefficientValueModulus_sq (N : ℕ) (r : ℝ) (a : Fin (N + 1) → ℂ) :
    Integrable (fun θ => normalizedCoefficientValueModulus N r (θ, a) ^ 2) radianIntervalMeasure := by
  have hc : Continuous (fun θ => weightedCoefficientFourier (normalizedRadialCoefficients N r) (a, θ)) :=
    (continuous_weightedCoefficientFourier _).comp (continuous_const.prodMk continuous_id)
  have hI := (hc.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := AddCircle.haarAddCircle)
  exact (measurePreserving_radianToUnitCircle.integrable_comp (hc.norm.pow 2).aestronglyMeasurable).mpr hI

end Erdos522

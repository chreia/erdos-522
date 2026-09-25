/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianJetSmallBall
import Erdos522.Probability.GaussianApproximation.ValuePairs

/-!
# Exactly normalized Gaussian polynomial values

The variance normalization is the finite radial sum. The oscillatory
covariance comparison gives one- and two-point circular Gaussian estimates
on arbitrary measurable events.
-/

noncomputable section
open MeasureTheory ProbabilityTheory WithLp
namespace Erdos522

/-- The real two-vector of the Gaussian polynomial divided by its exact standard deviation. -/
def realGaussianValue (N : ℕ) (r : ℝ) (z : ℂ) :
    (Fin (N + 1) → ℝ) → EuclideanSpace ℝ (Fin 2) :=
  gaussianVectorSum (realValueCoefficient N r z)

theorem realGaussianValue_eq_polynomial (N : ℕ) (r : ℝ) (z : ℂ) (g : Fin (N + 1) → ℝ) :
    realGaussianValue N r z g = toLp 2 ![
      ((gaussianPolynomial N g).eval (r * z)).re / radialSigma N r,
      ((gaussianPolynomial N g).eval (r * z)).im / radialSigma N r] := by
  ext i
  fin_cases i <;>
    simp only [realGaussianValue, gaussianVectorSum, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, smul_eq_mul, realValueCoefficient, gaussianPolynomial_eval,
      Complex.re_sum, Complex.im_sum, Finset.sum_div]
  all_goals
    apply Finset.sum_congr rfl
    intro k _
    simp only [mul_pow, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    norm_num
    ring

/-- Projection of the Gaussian jet gives its exactly normalized polynomial value. -/
theorem normalizedValueOfJet_gaussianPolynomialJet (N : ℕ) (hN : 0 < N) (r : ℝ) (z : ℂ)
    (g : Fin (N + 1) → ℝ) :
    normalizedValueOfJet N r (normalizedPolynomialJet (gaussianPolynomial N g) N (r * z)) =
      realGaussianValue N r z g := by
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN : (0 : ℝ) < N)).ne'
  rw [realGaussianValue_eq_polynomial]
  ext i
  fin_cases i <;> simp only [normalizedValueOfJet, normalizedPolynomialJet, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals field_simp

/-- One Gaussian value differs from the circular target by an explicit covariance error. -/
theorem gaussian_value_circular_comparison (N : ℕ) (hN : 0 < N) (K r θ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (20 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (A : Set (EuclideanSpace ℝ (Fin 2))) (hA : MeasurableSet A) :
    |(gaussianCoefficientMeasure (N + 1)).real {g |
      realGaussianValue N r (Complex.exp (Complex.I * θ)) g ∈ A} - circularGaussian.real A| ≤
      10 * Real.exp (8 * K) / Real.sqrt N := by
  have hb := gaussian_normalizedValue_circular_comparison N hN K r θ hK hNK hrl hru hdegree hangle A hA
  rw [← map_gaussianVectorSum, measureReal_def,
    Measure.map_apply (measurable_gaussianVectorSum _) hA] at hb
  exact hb

/-- The exact two-point circular comparison constant. -/
def gaussianValuePairError (K : ℝ) : ℝ :=
  80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80) + 20 * Real.exp (8 * K)

/-- Two separated Gaussian values approach independent circular values for every measurable rectangle. -/
theorem gaussian_value_pair_circular_comparison (N : ℕ) (hN : 0 < N) (K r s θ φ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsl : 1 - K / N ≤ s) (hsu : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hθ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (hφ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
    (A B : Set (EuclideanSpace ℝ (Fin 2))) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |(gaussianCoefficientMeasure (N + 1)).real {g |
        realGaussianValue N r (Complex.exp (Complex.I * θ)) g ∈ A ∧
        realGaussianValue N s (Complex.exp (Complex.I * φ)) g ∈ B} -
      circularGaussian.real A * circularGaussian.real B| ≤ gaussianValuePairError K / Real.sqrt N := by
  have hdegree' : (20 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ) := by
    calc
      _ ≤ (6400 * Real.exp (8 * K)) ^ 2 := by gcongr; norm_num
      _ ≤ _ := hdegree
  have h₁ := gaussian_value_circular_comparison N hN K r θ hK hNK hrl hru hdegree' hθ A hA
  have h₂ := gaussian_value_circular_comparison N hN K s φ hK hNK hsl hsu hdegree' hφ B hB
  have hp := gaussian_annular_jet_factorization N hN K r s θ φ hK hNK hrl hru hsl hsu
    hdegree hθ hφ hdifference hsum (normalizedValueOfJet N r ⁻¹' A) (normalizedValueOfJet N s ⁻¹' B)
    (measurableSet_valueOfJet_preimage N r A hA) (measurableSet_valueOfJet_preimage N s B hB)
  simp only [Set.mem_preimage, normalizedValueOfJet_gaussianPolynomialJet N hN] at hp
  have hm := abs_mul_sub_mul_le_of_unitInterval
    ((gaussianCoefficientMeasure (N + 1)).real {g | realGaussianValue N r (Complex.exp (Complex.I * θ)) g ∈ A})
    ((gaussianCoefficientMeasure (N + 1)).real {g | realGaussianValue N s (Complex.exp (Complex.I * φ)) g ∈ B})
    (circularGaussian.real A) (circularGaussian.real B)
    measureReal_nonneg measureReal_le_one measureReal_nonneg measureReal_le_one
  calc
    _ ≤ |(gaussianCoefficientMeasure (N + 1)).real {g |
        realGaussianValue N r (Complex.exp (Complex.I * θ)) g ∈ A ∧
        realGaussianValue N s (Complex.exp (Complex.I * φ)) g ∈ B} -
      (gaussianCoefficientMeasure (N + 1)).real {g | realGaussianValue N r (Complex.exp (Complex.I * θ)) g ∈ A} *
      (gaussianCoefficientMeasure (N + 1)).real {g | realGaussianValue N s (Complex.exp (Complex.I * φ)) g ∈ B}| +
      |(gaussianCoefficientMeasure (N + 1)).real {g | realGaussianValue N r (Complex.exp (Complex.I * θ)) g ∈ A} *
      (gaussianCoefficientMeasure (N + 1)).real {g | realGaussianValue N s (Complex.exp (Complex.I * φ)) g ∈ B} -
      circularGaussian.real A * circularGaussian.real B| := abs_sub_le _ _ _
    _ ≤ (80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N +
      (10 * Real.exp (8 * K) / Real.sqrt N + 10 * Real.exp (8 * K) / Real.sqrt N) :=
      add_le_add hp (hm.trans (add_le_add h₁ h₂))
    _ = _ := by unfold gaussianValuePairError; ring

end Erdos522

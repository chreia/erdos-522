/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.BoundedJets

/-!
# Covariance comparison for jets with complex coefficients

Complex multiplication transforms each real test direction by the coefficient's
rotation and scale. Integrating the real paired covariance estimate preserves
its constant when the coefficient second moment is one.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

/-- The Gram quadratic form in a complex-linear test direction is integrable. -/
theorem integrable_complex_direction_gram (μ : Measure ℂ)
    (h2 : MemLp (fun z : ℂ => z) 2 μ) {n d : ℕ}
    (a : Fin (n + 1) → EuclideanSpace ℝ (Fin d)) (x y : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun c : ℂ => (c.re • x + c.im • y).ofLp ⬝ᵥ signCovarianceMatrix a *ᵥ
      (c.re • x + c.im • y).ofLp) μ := by
  simp_rw [signCovarianceMatrix_form]
  have hv := memLp_complexCoefficientVector μ h2 x y
  apply integrable_finsetSum
  intro k _
  have h := (hv.const_inner (a k)).integrable_sq
  simpa only [circularVector, real_inner_comm, pow_two] using h

/-- The coefficient covariance is the average real Gram form in the corresponding complex direction. -/
theorem quadratic_coefficientCovarianceMatrix_jet (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h2 : MemLp (fun z : ℂ => z) 2 μ) (hmean : (∫ z, z ∂μ) = 0)
    (N : ℕ) (r : ℝ) (z : ℂ) (x : EuclideanSpace ℝ (Fin 4)) :
    x.ofLp ⬝ᵥ coefficientCovarianceMatrix μ (realJetCoefficient N r z)
      (imaginaryJetCoefficient N r z) *ᵥ x.ofLp =
      ∫ c, (c.re • x + c.im • jetDirectionRotation x).ofLp ⬝ᵥ
        signCovarianceMatrix (realJetCoefficient N r z) *ᵥ
          (c.re • x + c.im • jetDirectionRotation x).ofLp ∂μ := by
  rw [coefficientCovarianceMatrix, dotProduct_covarianceMatrix_mulVec,
    covarianceBilin_complexCoefficientSum μ h2 hmean]
  apply integral_congr_ae
  filter_upwards with c
  rw [signCovarianceMatrix_form]
  apply Finset.sum_congr rfl
  intro k _
  simp only [circularVector, inner_add_right, real_inner_smul_right,
    inner_add_left, real_inner_smul_left, inner_imaginaryJetCoefficient_rotation]

/-- The same integrated-Gram identity holds for paired jets. -/
theorem quadratic_coefficientCovarianceMatrix_pairedJet (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h2 : MemLp (fun z : ℂ => z) 2 μ) (hmean : (∫ z, z ∂μ) = 0)
    (N : ℕ) (r s : ℝ) (z w : ℂ) (x : EuclideanSpace ℝ (Fin 8)) :
    x.ofLp ⬝ᵥ coefficientCovarianceMatrix μ (realPairedJetCoefficient N r s z w)
      (imaginaryPairedJetCoefficient N r s z w) *ᵥ x.ofLp =
      ∫ c, (c.re • x + c.im • pairedJetDirectionRotation x).ofLp ⬝ᵥ
        signCovarianceMatrix (realPairedJetCoefficient N r s z w) *ᵥ
          (c.re • x + c.im • pairedJetDirectionRotation x).ofLp ∂μ := by
  rw [coefficientCovarianceMatrix, dotProduct_covarianceMatrix_mulVec,
    covarianceBilin_complexCoefficientSum μ h2 hmean]
  apply integral_congr_ae
  filter_upwards with c
  rw [signCovarianceMatrix_form]
  apply Finset.sum_congr rfl
  intro k _
  simp only [circularVector, inner_add_right, real_inner_smul_right,
    inner_add_left, real_inner_smul_left, inner_imaginaryPairedJetCoefficient]

/-- Complex multiplication commutes with the split into two jet directions. -/
theorem finAddEquivProd_complex_paired_jet_direction (c : ℂ) (x : EuclideanSpace ℝ (Fin 8)) :
    EuclideanSpace.finAddEquivProd (n := 4) (m := 4) (c.re • x + c.im • pairedJetDirectionRotation x) =
      (c.re • (EuclideanSpace.finAddEquivProd (n := 4) (m := 4) x).1 +
        c.im • jetDirectionRotation (EuclideanSpace.finAddEquivProd (n := 4) (m := 4) x).1,
       c.re • (EuclideanSpace.finAddEquivProd (n := 4) (m := 4) x).2 +
        c.im • jetDirectionRotation (EuclideanSpace.finAddEquivProd (n := 4) (m := 4) x).2) := by
  apply Prod.ext <;> ext i <;> fin_cases i <;> rfl

/-- The joint-to-independent covariance difference is an integrated real difference. -/
theorem complexPairedJet_covariance_error_eq (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h2 : MemLp (fun z : ℂ => z) 2 μ) (hmean : (∫ z, z ∂μ) = 0)
    (N : ℕ) (r s : ℝ) (z w : ℂ) (x : EuclideanSpace ℝ (Fin 8)) :
    x.ofLp ⬝ᵥ (coefficientCovarianceMatrix μ (realPairedJetCoefficient N r s z w)
        (imaginaryPairedJetCoefficient N r s z w) -
      gaussianBlockCovariance
        (coefficientCovarianceMatrix μ (realJetCoefficient N r z) (imaginaryJetCoefficient N r z))
        (coefficientCovarianceMatrix μ (realJetCoefficient N s w) (imaginaryJetCoefficient N s w))) *ᵥ x.ofLp =
      ∫ c, (c.re • x + c.im • pairedJetDirectionRotation x).ofLp ⬝ᵥ
        (signCovarianceMatrix (realPairedJetCoefficient N r s z w) -
          gaussianBlockCovariance (signCovarianceMatrix (realJetCoefficient N r z))
            (signCovarianceMatrix (realJetCoefficient N s w))) *ᵥ
              (c.re • x + c.im • pairedJetDirectionRotation x).ofLp ∂μ := by
  let x₁ := (EuclideanSpace.finAddEquivProd (n := 4) (m := 4) x).1
  let x₂ := (EuclideanSpace.finAddEquivProd (n := 4) (m := 4) x).2
  have hI := integrable_complex_direction_gram μ h2 (realPairedJetCoefficient N r s z w)
    x (pairedJetDirectionRotation x)
  have hI₁ := integrable_complex_direction_gram μ h2 (realJetCoefficient N r z) x₁ (jetDirectionRotation x₁)
  have hI₂ := integrable_complex_direction_gram μ h2 (realJetCoefficient N s w) x₂ (jetDirectionRotation x₂)
  simp only [Matrix.sub_mulVec, dotProduct_sub, quadratic_gaussianBlockCovariance (m := 4) (n := 4),
    quadratic_coefficientCovarianceMatrix_pairedJet μ h2 hmean,
    quadratic_coefficientCovarianceMatrix_jet μ h2 hmean,
    finAddEquivProd_complex_paired_jet_direction]
  have he := integral_sub hI (hI₁.add hI₂)
  simp only [Pi.add_apply] at he
  rw [integral_add hI₁ hI₂] at he
  simpa only [x₁, x₂] using he.symm

/-- Unit-second-moment complex coefficients retain the explicit paired covariance perturbation. -/
theorem complexPairedJet_covariance_error_le (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h2 : MemLp (fun z : ℂ => z) 2 μ) (hmean : (∫ z, z ∂μ) = 0)
    (hnorm : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)
    (N : ℕ) (hN : 0 < N) (K r s θ φ : ℝ)
    (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hr : r ≤ 1 + K / N) (hs : s ≤ 1 + K / N)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
    (x : EuclideanSpace ℝ (Fin 8)) :
    |x.ofLp ⬝ᵥ (coefficientCovarianceMatrix μ (realPairedJetCoefficient N r s
        (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))
        (imaginaryPairedJetCoefficient N r s (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))) -
      gaussianBlockCovariance
        (coefficientCovarianceMatrix μ (realJetCoefficient N r (Complex.exp (Complex.I * θ)))
          (imaginaryJetCoefficient N r (Complex.exp (Complex.I * θ))))
        (coefficientCovarianceMatrix μ (realJetCoefficient N s (Complex.exp (Complex.I * φ)))
          (imaginaryJetCoefficient N s (Complex.exp (Complex.I * φ))))) *ᵥ x.ofLp| ≤
      (20 * Real.exp (4 * K) / Real.sqrt N) * ‖x‖ ^ 2 := by
  let z := Complex.exp (Complex.I * θ)
  let w := Complex.exp (Complex.I * φ)
  let d := 20 * Real.exp (4 * K) / Real.sqrt N
  let v := fun c : ℂ => c.re • x + c.im • pairedJetDirectionRotation x
  let f := fun c : ℂ => (v c).ofLp ⬝ᵥ
    (signCovarianceMatrix (realPairedJetCoefficient N r s z w) -
      gaussianBlockCovariance (signCovarianceMatrix (realJetCoefficient N r z))
        (signCovarianceMatrix (realJetCoefficient N s w))) *ᵥ (v c).ofLp
  have hI : Integrable f μ := by
    simp only [f, v, Matrix.sub_mulVec, dotProduct_sub,
      quadratic_gaussianBlockCovariance (m := 4) (n := 4), finAddEquivProd_complex_paired_jet_direction]
    exact (integrable_complex_direction_gram μ h2 _ _ _).sub
      ((integrable_complex_direction_gram μ h2 _ _ _).add (integrable_complex_direction_gram μ h2 _ _ _))
  rw [complexPairedJet_covariance_error_eq μ h2 hmean]
  change |∫ c, f c ∂μ| ≤ d * ‖x‖ ^ 2
  calc
    _ ≤ ∫ c, |f c| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ c, d * (‖c‖ ^ 2 * ‖x‖ ^ 2) ∂μ := by
      apply integral_mono hI.abs ((h2.norm.integrable_sq.mul_const _).const_mul _)
      intro c
      have h := pairedJet_covariance_error_le N hN K r s θ φ hK hr0 hs0 hr hs hdifference hsum (v c)
      rw [show ‖v c‖ ^ 2 = ‖c‖ ^ 2 * ‖x‖ ^ 2 from norm_sq_complex_paired_jet_direction c x] at h
      exact h
    _ = _ := by rw [integral_const_mul, integral_mul_const, hnorm, one_mul]

/-- The Gaussian law of separated polynomial jets differs from its independent
marginals by at most the manuscript's explicit covariance-comparison constant. -/
theorem gaussian_complexPairedJet_measureReal_prod_le (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h2 : MemLp (fun z : ℂ => z) 2 μ) (hmean : (∫ z, z ∂μ) = 0)
    (hnorm : (∫ z, ‖z‖ ^ 2 ∂μ) = 1) (N : ℕ) (hN : 0 < N) (K r s θ φ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsl : 1 - K / N ≤ s) (hsu : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hθ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (hφ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
    (A B : Set (EuclideanSpace ℝ (Fin 4))) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |(multivariateGaussian 0 (coefficientCovarianceMatrix μ (realPairedJetCoefficient N r s
        (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))) (imaginaryPairedJetCoefficient N r s
        (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))))).real
      ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹' (A ×ˢ B)) -
      (multivariateGaussian 0 (coefficientCovarianceMatrix μ (realJetCoefficient N r
        (Complex.exp (Complex.I * θ))) (imaginaryJetCoefficient N r
        (Complex.exp (Complex.I * θ))))).real A *
      (multivariateGaussian 0 (coefficientCovarianceMatrix μ (realJetCoefficient N s
        (Complex.exp (Complex.I * φ))) (imaginaryJetCoefficient N s
        (Complex.exp (Complex.I * φ))))).real B| ≤
      (80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N := by
  let S₁ := coefficientCovarianceMatrix μ (realJetCoefficient N r (Complex.exp (Complex.I * θ))) (imaginaryJetCoefficient N r (Complex.exp (Complex.I * θ)))
  let S₂ := coefficientCovarianceMatrix μ (realJetCoefficient N s (Complex.exp (Complex.I * φ))) (imaginaryJetCoefficient N s (Complex.exp (Complex.I * φ)))
  let S := coefficientCovarianceMatrix μ (realPairedJetCoefficient N r s
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))) (imaginaryPairedJetCoefficient N r s
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))
  let c := Real.exp (-4 * K) / 80
  let δ := 20 * Real.exp (4 * K) / Real.sqrt N
  have hc : 0 < c := by dsimp [c]; positivity
  have hl₁ (x : EuclideanSpace ℝ (Fin 4)) : c * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S₁ *ᵥ x.ofLp := by
    rw [show S₁ = coefficientCovarianceMatrix μ (realJetCoefficient N r (Complex.exp (Complex.I * θ)))
      (imaginaryJetCoefficient N r (Complex.exp (Complex.I * θ))) from rfl,
      coefficientCovarianceMatrix, dotProduct_covarianceMatrix_mulVec]
    exact covarianceBilin_complex_jet_lower μ h2 hmean hnorm N hN K r θ hK hNK hrl hru hdegree hθ x
  have hl₂ (x : EuclideanSpace ℝ (Fin 4)) : c * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S₂ *ᵥ x.ofLp := by
    rw [show S₂ = coefficientCovarianceMatrix μ (realJetCoefficient N s (Complex.exp (Complex.I * φ)))
      (imaginaryJetCoefficient N s (Complex.exp (Complex.I * φ))) from rfl,
      coefficientCovarianceMatrix, dotProduct_covarianceMatrix_mulVec]
    exact covarianceBilin_complex_jet_lower μ h2 hmean hnorm N hN K s φ hK hNK hsl hsu hdegree hφ x
  have h₁ : S₁.PosDef := coefficientCovarianceMatrix_posDef μ _ _ hc
    (covarianceBilin_complex_jet_lower μ h2 hmean hnorm N hN K r θ hK hNK hrl hru hdegree hθ)
  have h₂ : S₂.PosDef := coefficientCovarianceMatrix_posDef μ _ _ hc
    (covarianceBilin_complex_jet_lower μ h2 hmean hnorm N hN K s φ hK hNK hsl hsu hdegree hφ)
  have hS : S.PosDef := coefficientCovarianceMatrix_posDef μ _ _ (by positivity)
    (covarianceBilin_complex_paired_jet_lower μ h2 hmean hnorm N hN K r s θ φ hK hNK
      hrl hru hsl hsu hdegree hθ hφ hdifference hsum)
  have hT := gaussianBlockCovariance_posDef_of_lower S₁ S₂ h₁.posSemidef h₂.posSemidef c hc hl₁ hl₂
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : K / (N : ℝ) ≤ 1 / 2 := (div_le_iff₀ hn).mpr (by linarith)
  have hr0 : 0 ≤ r := by linarith
  have hs0 : 0 ≤ s := by linarith
  have herror := complexPairedJet_covariance_error_le μ h2 hmean hnorm N hN K r s θ φ hK hr0 hs0 hru hsu hdifference hsum
  have h := gaussian_measureReal_sub_le_eight S (gaussianBlockCovariance S₁ S₂) hS hT c δ hc
    (by dsimp [δ]; positivity) (pairedJet_relative_error_le_half N hN K hdegree)
    (gaussianBlockCovariance_lower S₁ S₂ c hl₁ hl₂) herror
    ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹' (A ×ˢ B)) ((hA.prod hB).preimage (by fun_prop))
  rw [gaussianBlockCovariance_measureReal_prod S₁ S₂ h₁.posSemidef h₂.posSemidef A B hA hB] at h
  refine h.trans ?_
  dsimp [c, δ]
  have hpos : 0 ≤ Real.exp (4 * K) / ((Real.exp (-4 * K) / 80) * Real.sqrt N) := by positivity
  calc
    _ = 40 * (Real.exp (4 * K) / ((Real.exp (-4 * K) / 80) * Real.sqrt N)) := by ring
    _ ≤ 80 * (Real.exp (4 * K) / ((Real.exp (-4 * K) / 80) * Real.sqrt N)) := by nlinarith
    _ = _ := by ring



end Erdos522

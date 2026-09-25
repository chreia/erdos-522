/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.ComplexCoefficientCovarianceComparison
import Erdos522.Probability.GaussianApproximation.CircularPairedSmallBall

/-!
# Small-value events for bounded complex polynomial jets

Finite Gaussian approximation and covariance comparison give explicit one-
and two-point estimates for any centered bounded complex coefficient law of
unit second moment. Polynomial thresholds retain their separate value and
derivative normalizations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace NNReal
namespace Erdos522

local instance boundedPairConvexSpace {d : ℕ} : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule
local instance boundedPairModuleConvexSpace {d : ℕ} : Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.of_module

/-- Approximate factorization for arbitrary measurable convex events in two
separated normalized jets with bounded complex coefficients. -/
theorem exists_annular_bounded_jet_factorization_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
      (bound : ℝ) (_ : 0 ≤ bound) (_ : ∀ᵐ z ∂μ, ‖z‖ ≤ bound)
      (_ : (∫ z, z ∂μ) = 0) (_ : (∫ z, ‖z‖ ^ 2 ∂μ) = 1) (N : ℕ) (_ : 0 < N) (K r s θ φ : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : 1 - K / N ≤ s) (_ : s ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
      (A B : Set (EuclideanSpace ℝ (Fin 4)))
      (_ : MeasurableSet A) (_ : MeasurableSet B)
      (_ : Convexity.IsConvexSet ℝ A) (_ : Convexity.IsConvexSet ℝ B),
      |((Measure.pi (fun _ : Fin (N + 1) => μ)).map (circularPairedJet N r s
          (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))).real
        ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹' (A ×ˢ B)) -
        ((Measure.pi (fun _ : Fin (N + 1) => μ)).map (circularJet N r
          (Complex.exp (Complex.I * θ)))).real A *
        ((Measure.pi (fun _ : Fin (N + 1) => μ)).map (circularJet N s
          (Complex.exp (Complex.I * φ)))).real B| ≤
        (2 * boundedJetGaussianErrorConstant C bound K + boundedPairedJetGaussianErrorConstant C bound K +
          80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_gaussian_approximation_bounded_jet_constant
  obtain ⟨C₂, hC₂, h₂⟩ := exists_gaussian_approximation_bounded_paired_jet_constant
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro μ _ bound hbound0 hbound hmean hsecond N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum A B hA hB hcA hcB
  let E := (EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹' (A ×ˢ B)
  have hE : MeasurableSet E := (hA.prod hB).preimage (by fun_prop)
  have hcE : Convexity.IsConvexSet ℝ E := isConvexSet_pair_preimage A B hcA hcB
  have hmono₁ : boundedJetGaussianErrorConstant C₁ bound K ≤ boundedJetGaussianErrorConstant (C₁ + C₂) bound K := by
    unfold boundedJetGaussianErrorConstant
    gcongr
    linarith
  have hmono₂ : boundedPairedJetGaussianErrorConstant C₂ bound K ≤ boundedPairedJetGaussianErrorConstant (C₁ + C₂) bound K := by
    unfold boundedPairedJetGaussianErrorConstant
    gcongr
    linarith
  have hb₁ := (h₁ μ bound hbound0 hbound hmean hsecond N hN K r θ hK hNK hrl hru
    hdegree hθ A hA hcA).trans
    (div_le_div_of_nonneg_right hmono₁ (Real.sqrt_nonneg N))
  have hb₂ := (h₁ μ bound hbound0 hbound hmean hsecond N hN K s φ hK hNK hsl hsu
    hdegree hφ B hB hcB).trans
    (div_le_div_of_nonneg_right hmono₁ (Real.sqrt_nonneg N))
  have hpair := (h₂ μ bound hbound0 hbound hmean hsecond N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree
    hθ hφ hdifference hsum E hE hcE).trans
    (div_le_div_of_nonneg_right hmono₂ (Real.sqrt_nonneg N))
  let p₁ := ((Measure.pi (fun _ : Fin (N + 1) => μ)).map
    (circularJet N r (Complex.exp (Complex.I * θ)))).real A
  let p₂ := ((Measure.pi (fun _ : Fin (N + 1) => μ)).map
    (circularJet N s (Complex.exp (Complex.I * φ)))).real B
  let g₁ := (multivariateGaussian 0 (coefficientCovarianceMatrix μ (realJetCoefficient N r (Complex.exp (Complex.I * θ))) (imaginaryJetCoefficient N r (Complex.exp (Complex.I * θ))))).real A
  let g₂ := (multivariateGaussian 0 (coefficientCovarianceMatrix μ (realJetCoefficient N s (Complex.exp (Complex.I * φ))) (imaginaryJetCoefficient N s (Complex.exp (Complex.I * φ))))).real B
  let p := ((Measure.pi (fun _ : Fin (N + 1) => μ)).map (circularPairedJet N r s
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))).real E
  let g := (multivariateGaussian 0 (coefficientCovarianceMatrix μ (realPairedJetCoefficient N r s
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))) (imaginaryPairedJetCoefficient N r s
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))))).real E
  have hp₂ : p₂ ≤ 1 := measureReal_le_one
  have hg₁ : g₁ ≤ 1 := measureReal_le_one
  have hm := abs_mul_sub_mul_le_of_unitInterval g₁ g₂ p₁ p₂
    measureReal_nonneg hg₁ measureReal_nonneg hp₂
  have hb₁' : |g₁ - p₁| ≤ boundedJetGaussianErrorConstant (C₁ + C₂) bound K / Real.sqrt N := by
    change |p₁ - g₁| ≤ _ at hb₁
    rwa [abs_sub_comm] at hb₁
  have hb₂' : |g₂ - p₂| ≤ boundedJetGaussianErrorConstant (C₁ + C₂) bound K / Real.sqrt N := by
    change |p₂ - g₂| ≤ _ at hb₂
    rwa [abs_sub_comm] at hb₂
  have hg : |g - g₁ * g₂| ≤
      (80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N :=
    gaussian_complexPairedJet_measureReal_prod_le μ
      (MemLp.of_bound (by fun_prop) bound hbound) hmean hsecond N hN K r s θ φ hK hNK hrl hru hsl hsu
      hdegree hθ hφ hdifference hsum A B hA hB
  change |p - g| ≤ _ at hpair
  change |p - p₁ * p₂| ≤ _
  calc
    _ ≤ |p - g| + |g - g₁ * g₂| + |g₁ * g₂ - p₁ * p₂| := by
      calc
        _ ≤ |p - g| + |g - p₁ * p₂| := abs_sub_le _ _ _
        _ ≤ _ := by linarith [abs_sub_le g (g₁ * g₂) (p₁ * p₂)]
    _ ≤ boundedPairedJetGaussianErrorConstant (C₁ + C₂) bound K / Real.sqrt N +
        (80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N +
        (boundedJetGaussianErrorConstant (C₁ + C₂) bound K / Real.sqrt N +
          boundedJetGaussianErrorConstant (C₁ + C₂) bound K / Real.sqrt N) :=
      add_le_add (add_le_add hpair hg) (hm.trans (add_le_add hb₁' hb₂'))
    _ = _ := by ring


/-- The one-point jet law measures precisely the polynomial small-ball event. -/
theorem coefficientJet_measureReal_smallBall (μ : Measure ℂ) (N : ℕ) (hN : 0 < N) (r : ℝ) (z : ℂ) (u v : ℝ) :
    ((Measure.pi (fun _ : Fin (N + 1) => μ)).map (circularJet N r z)).real (jetSmallBallSet u v) =
      (Measure.pi (fun _ : Fin (N + 1) => μ)).real (circularPolynomialJetSmallBallEvent N (r * z) u v) := by
  rw [measureReal_def, Measure.map_apply (measurable_circularJet N r z) (measurableSet_jetSmallBallSet u v)]
  congr 2
  ext ω
  exact mem_jetSmallBallSet_circular N hN r z ω u v

/-- The paired jet rectangle measures the intersection of the actual polynomial events. -/
theorem coefficientPairedJet_measureReal_smallBall (μ : Measure ℂ) (N : ℕ) (hN : 0 < N) (r s : ℝ) (z w : ℂ)
    (u v u' v' : ℝ) :
    ((Measure.pi (fun _ : Fin (N + 1) => μ)).map (circularPairedJet N r s z w)).real
      ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹'
        (jetSmallBallSet u v ×ˢ jetSmallBallSet u' v')) =
      (Measure.pi (fun _ : Fin (N + 1) => μ)).real (circularPolynomialJetSmallBallEvent N (r * z) u v ∩
        circularPolynomialJetSmallBallEvent N (s * w) u' v') := by
  have hE : MeasurableSet ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹'
      (jetSmallBallSet u v ×ˢ jetSmallBallSet u' v')) :=
    ((measurableSet_jetSmallBallSet u v).prod (measurableSet_jetSmallBallSet u' v')).preimage
      (by fun_prop)
  rw [measureReal_def, Measure.map_apply (measurable_circularPairedJet N r s z w) hE]
  congr 2
  ext ω
  simp only [Set.mem_preimage, Set.mem_prod, finAddEquivProd_circularPairedJet,
    mem_jetSmallBallSet_circular N hN, Set.mem_inter_iff, circularPolynomialJetSmallBallEvent, Set.mem_ofPred_eq]

/-- Joint small-value events for a single bounded complex polynomial factor up to the
explicit inverse-square-root error at separated annular points. -/
theorem exists_bounded_polynomial_small_ball_factorization_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
      (bound : ℝ) (_ : 0 ≤ bound) (_ : ∀ᵐ z ∂μ, ‖z‖ ≤ bound)
      (_ : (∫ z, z ∂μ) = 0) (_ : (∫ z, ‖z‖ ^ 2 ∂μ) = 1) (N : ℕ) (_ : 0 < N) (K r s θ φ : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : 1 - K / N ≤ s) (_ : s ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖) (u v u' v' : ℝ),
      |(Measure.pi (fun _ : Fin (N + 1) => μ)).real
        (circularPolynomialJetSmallBallEvent N (r * Complex.exp (Complex.I * θ)) u v ∩
          circularPolynomialJetSmallBallEvent N (s * Complex.exp (Complex.I * φ)) u' v') -
        (Measure.pi (fun _ : Fin (N + 1) => μ)).real
          (circularPolynomialJetSmallBallEvent N (r * Complex.exp (Complex.I * θ)) u v) *
        (Measure.pi (fun _ : Fin (N + 1) => μ)).real
          (circularPolynomialJetSmallBallEvent N (s * Complex.exp (Complex.I * φ)) u' v')| ≤
        (2 * boundedJetGaussianErrorConstant C bound K + boundedPairedJetGaussianErrorConstant C bound K +
          80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N := by
  obtain ⟨C, hC, h⟩ := exists_annular_bounded_jet_factorization_constant
  refine ⟨C, hC, ?_⟩
  intro μ _ bound hbound0 hbound hmean hsecond N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum u v u' v'
  have hb := h μ bound hbound0 hbound hmean hsecond N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum
    (jetSmallBallSet u v) (jetSmallBallSet u' v')
    (measurableSet_jetSmallBallSet u v) (measurableSet_jetSmallBallSet u' v')
    (isConvexSet_jetSmallBallSet u v) (isConvexSet_jetSmallBallSet u' v')
  rwa [coefficientPairedJet_measureReal_smallBall μ N hN, coefficientJet_measureReal_smallBall μ N hN,
    coefficientJet_measureReal_smallBall μ N hN] at hb



/-- Separate value and derivative thresholds retain their exact two-complex-disk scale. -/
theorem exists_bounded_polynomial_jet_small_ball_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
      (bound : ℝ) (_ : 0 ≤ bound) (_ : ∀ᵐ z ∂μ, ‖z‖ ≤ bound)
      (_ : (∫ z, z ∂μ) = 0) (_ : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)
      (N : ℕ) (_ : 0 < N) (K r θ : ℝ) (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
      (u v : ℝ) (_ : 0 ≤ u) (_ : 0 ≤ v),
      (Measure.pi (fun _ : Fin (N + 1) => μ)).real
        (circularPolynomialJetSmallBallEvent N (r * Complex.exp (Complex.I * θ)) u v) ≤
        u ^ 2 * v ^ 2 / (4 * (Real.exp (-4 * K) / 80) ^ 2) +
          boundedJetGaussianErrorConstant C bound K / Real.sqrt N := by
  obtain ⟨C, hC, happrox⟩ := exists_gaussian_approximation_bounded_jet_constant
  refine ⟨C, hC, ?_⟩
  intro μ _ bound hbound0 hbound hmean hsecond N hN K r θ hK hNK hrl hru hdegree hangle u v hu hv
  have h2 : MemLp (fun z : ℂ => z) 2 μ := MemLp.of_bound (by fun_prop) bound hbound
  let z := Complex.exp (Complex.I * θ)
  let S := coefficientCovarianceMatrix μ (realJetCoefficient N r z) (imaginaryJetCoefficient N r z)
  let c : ℝ≥0 := ⟨Real.exp (-4 * K) / 80, by positivity⟩
  have hc : c ≠ 0 := ne_of_gt (show 0 < c from by change 0 < Real.exp (-4 * K) / 80; positivity)
  have hS : S.PosDef := coefficientCovarianceMatrix_posDef μ _ _ (by positivity)
    (covarianceBilin_complex_jet_lower μ h2 hmean hsecond N hN K r θ hK hNK hrl hru hdegree hangle)
  have hlower (x : EuclideanSpace ℝ (Fin 4)) : (c : ℝ) * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S *ᵥ x.ofLp := by
    rw [show S = coefficientCovarianceMatrix μ (realJetCoefficient N r z) (imaginaryJetCoefficient N r z) from rfl,
      coefficientCovarianceMatrix, dotProduct_covarianceMatrix_mulVec]
    exact covarianceBilin_complex_jet_lower μ h2 hmean hsecond N hN K r θ hK hNK hrl hru hdegree hangle x
  have hg := gaussian_jetSmallBallSet_le S hS.posSemidef c hc hlower u v hu hv
  have hb := (le_abs_self _).trans (happrox μ bound hbound0 hbound hmean hsecond
    N hN K r θ hK hNK hrl hru hdegree hangle
    (jetSmallBallSet u v) (measurableSet_jetSmallBallSet u v) (isConvexSet_jetSmallBallSet u v))
  change (multivariateGaussian 0 S).real (jetSmallBallSet u v) ≤
    u ^ 2 * v ^ 2 / (4 * (Real.exp (-4 * K) / 80) ^ 2) at hg
  change ((Measure.pi (fun _ : Fin (N + 1) => μ)).map (circularJet N r z)).real (jetSmallBallSet u v) -
    (multivariateGaussian 0 S).real (jetSmallBallSet u v) ≤
      boundedJetGaussianErrorConstant C bound K / Real.sqrt N at hb
  rw [coefficientJet_measureReal_smallBall μ N hN] at hb
  linarith

end Erdos522

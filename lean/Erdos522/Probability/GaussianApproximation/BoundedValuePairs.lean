/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.BoundedValues
import Erdos522.Probability.GaussianApproximation.BoundedPairedSmallBall
import Erdos522.Probability.GaussianApproximation.CircularValuePairs

/-!
# Paired value approximation for bounded complex coefficients

Projection of the separated polynomial jets and the exactly normalized
marginal value comparison yield the circular Gaussian product target.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder
namespace Erdos522

local instance boundedValuePairConvexSpace {d : ℕ} : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule
local instance boundedValuePairModuleConvexSpace {d : ℕ} : Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.of_module

/-- The projected jet event and the normalized value event have the same probability. -/
theorem coefficientJet_measureReal_valueOfJet (μ : Measure ℂ) (N : ℕ) (hN : 0 < N) (r : ℝ) (z : ℂ)
    (A : Set (EuclideanSpace ℝ (Fin 2))) (hA : MeasurableSet A) :
    ((Measure.pi (fun _ : Fin (N + 1) => μ)).map (circularJet N r z)).real
      (normalizedValueOfJet N r ⁻¹' A) =
      ((Measure.pi (fun _ : Fin (N + 1) => μ)).map (circularValue N r z)).real A := by
  simp only [measureReal_def, Measure.map_apply (measurable_circularJet N r z)
    (measurableSet_valueOfJet_preimage N r A hA), Measure.map_apply (measurable_circularValue N r z) hA]
  congr 2
  ext ω
  simp only [Set.mem_preimage, normalizedValueOfJet_circularJet N hN]

/-- The paired projected rectangle is the intersection of the two normalized value events. -/
theorem coefficientPairedJet_measureReal_valueOfJet (μ : Measure ℂ) (N : ℕ) (hN : 0 < N) (r s : ℝ) (z w : ℂ)
    (A B : Set (EuclideanSpace ℝ (Fin 2))) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ((Measure.pi (fun _ : Fin (N + 1) => μ)).map (circularPairedJet N r s z w)).real
      ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹'
        ((normalizedValueOfJet N r ⁻¹' A) ×ˢ (normalizedValueOfJet N s ⁻¹' B))) =
      (Measure.pi (fun _ : Fin (N + 1) => μ)).real {ω | circularValue N r z ω ∈ A ∧
        circularValue N s w ω ∈ B} := by
  have hE : MeasurableSet ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹'
      ((normalizedValueOfJet N r ⁻¹' A) ×ˢ (normalizedValueOfJet N s ⁻¹' B))) :=
    ((measurableSet_valueOfJet_preimage N r A hA).prod
      (measurableSet_valueOfJet_preimage N s B hB)).preimage (by fun_prop)
  rw [measureReal_def, Measure.map_apply (measurable_circularPairedJet N r s z w) hE]
  congr 2
  ext ω
  simp only [Set.mem_preimage, finAddEquivProd_circularPairedJet,
    Set.mem_prod, normalizedValueOfJet_circularJet N hN, Set.mem_ofPred_eq]

/-- The two-point error includes two marginal comparisons and the separated-jet factorization. -/
def boundedValuePairGaussianErrorConstant (C bound K : ℝ) : ℝ :=
  2 * boundedValueGaussianErrorConstant C bound K + 2 * boundedJetGaussianErrorConstant C bound K +
    boundedPairedJetGaussianErrorConstant C bound K + 80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)

/-- The same coefficient sequence at two separated points has the joint circular Gaussian
limit, uniformly over pairs of measurable convex value events. -/
theorem exists_gaussian_approximation_bounded_value_pair_constant :
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
      (A B : Set (EuclideanSpace ℝ (Fin 2)))
      (_ : MeasurableSet A) (_ : MeasurableSet B)
      (_ : Convexity.IsConvexSet ℝ A) (_ : Convexity.IsConvexSet ℝ B),
      |(Measure.pi (fun _ : Fin (N + 1) => μ)).real {ω |
          circularValue N r (Complex.exp (Complex.I * θ)) ω ∈ A ∧
          circularValue N s (Complex.exp (Complex.I * φ)) ω ∈ B} -
        circularGaussian.real A * circularGaussian.real B| ≤
        boundedValuePairGaussianErrorConstant C bound K / Real.sqrt N := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_gaussian_approximation_bounded_value_constant
  obtain ⟨C₂, hC₂, h₂⟩ := exists_annular_bounded_jet_factorization_constant
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro μ _ bound hbound0 hbound hmean hsecond N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum A B hA hB hcA hcB
  have hvmono : boundedValueGaussianErrorConstant C₁ bound K ≤ boundedValueGaussianErrorConstant (C₁ + C₂) bound K := by
    unfold boundedValueGaussianErrorConstant
    gcongr
    linarith
  have hjmono : boundedJetGaussianErrorConstant C₂ bound K ≤ boundedJetGaussianErrorConstant (C₁ + C₂) bound K := by
    unfold boundedJetGaussianErrorConstant
    gcongr
    linarith
  have hpmono : boundedPairedJetGaussianErrorConstant C₂ bound K ≤ boundedPairedJetGaussianErrorConstant (C₁ + C₂) bound K := by
    unfold boundedPairedJetGaussianErrorConstant
    gcongr
    linarith
  have hm := h₂ μ bound hbound0 hbound hmean hsecond N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum
    (normalizedValueOfJet N r ⁻¹' A) (normalizedValueOfJet N s ⁻¹' B)
    (measurableSet_valueOfJet_preimage N r A hA) (measurableSet_valueOfJet_preimage N s B hB)
    (isConvexSet_valueOfJet_preimage N r A hcA) (isConvexSet_valueOfJet_preimage N s B hcB)
  rw [coefficientPairedJet_measureReal_valueOfJet μ N hN _ _ _ _ A B hA hB,
    coefficientJet_measureReal_valueOfJet μ N hN _ _ A hA, coefficientJet_measureReal_valueOfJet μ N hN _ _ B hB] at hm
  have hpair := hm.trans (div_le_div_of_nonneg_right
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hjmono (by norm_num : (0 : ℝ) ≤ 2)) hpmono) (le_refl _))
    (Real.sqrt_nonneg N))
  have hdegree' : (20 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ) := by
    calc
      _ ≤ (6400 * Real.exp (8 * K)) ^ 2 := by gcongr; norm_num
      _ ≤ _ := hdegree
  have hv₁ := (h₁ μ bound hbound0 hbound hmean hsecond N hN K r θ hK hNK hrl hru
    hdegree' hθ A hA hcA).trans
    (div_le_div_of_nonneg_right hvmono (Real.sqrt_nonneg N))
  have hv₂ := (h₁ μ bound hbound0 hbound hmean hsecond N hN K s φ hK hNK hsl hsu
    hdegree' hφ B hB hcB).trans
    (div_le_div_of_nonneg_right hvmono (Real.sqrt_nonneg N))
  let p₁ := ((Measure.pi (fun _ : Fin (N + 1) => μ)).map
    (circularValue N r (Complex.exp (Complex.I * θ)))).real A
  let p₂ := ((Measure.pi (fun _ : Fin (N + 1) => μ)).map
    (circularValue N s (Complex.exp (Complex.I * φ)))).real B
  let p := (Measure.pi (fun _ : Fin (N + 1) => μ)).real {ω |
    circularValue N r (Complex.exp (Complex.I * θ)) ω ∈ A ∧
    circularValue N s (Complex.exp (Complex.I * φ)) ω ∈ B}
  have hproduct := (abs_mul_sub_mul_le_of_unitInterval p₁ p₂ (circularGaussian.real A)
    (circularGaussian.real B) measureReal_nonneg measureReal_le_one
    measureReal_nonneg measureReal_le_one).trans (add_le_add hv₁ hv₂)
  change |p - p₁ * p₂| ≤ _ at hpair
  change |p - circularGaussian.real A * circularGaussian.real B| ≤ _
  calc
    _ ≤ |p - p₁ * p₂| + |p₁ * p₂ - circularGaussian.real A * circularGaussian.real B| :=
      abs_sub_le _ _ _
    _ ≤ (2 * boundedJetGaussianErrorConstant (C₁ + C₂) bound K + boundedPairedJetGaussianErrorConstant (C₁ + C₂) bound K +
        80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N +
      (boundedValueGaussianErrorConstant (C₁ + C₂) bound K / Real.sqrt N +
        boundedValueGaussianErrorConstant (C₁ + C₂) bound K / Real.sqrt N) := add_le_add hpair hproduct
    _ = _ := by unfold boundedValuePairGaussianErrorConstant; ring



end Erdos522

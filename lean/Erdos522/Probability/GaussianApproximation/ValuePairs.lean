/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.Values
import Erdos522.Probability.GaussianApproximation.PairedSmallBall

/-!
# Two-point circular Gaussian approximation

Projection of the normalized jet preserves the exact value normalization.
The separated-jet factorization and the one-point circular approximation
therefore give the joint law of two independent standard circular values.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder

namespace Erdos522

local instance normalizedValuePairConvexSpace {d : ℕ} : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule
local instance normalizedValuePairModuleConvexSpace {d : ℕ} : Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.of_module

/-- Projection of the jet followed by the exact standard-deviation normalization. -/
def normalizedValueOfJet (N : ℕ) (r : ℝ) :
    EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := toLp 2 ![Real.sqrt N / radialSigma N r * x 0,
    Real.sqrt N / radialSigma N r * x 1]
  map_add' x y := by ext i; fin_cases i <;> simp [mul_add]
  map_smul' a x := by ext i; fin_cases i <;> simp [mul_left_comm]

/-- The projection gives the actual exactly normalized value of the same polynomial. -/
theorem normalizedValueOfJet_realRademacherJet (N : ℕ) (hN : 0 < N) (r : ℝ) (z : ℂ)
    (ω : LogMoments.SignVector N) :
    normalizedValueOfJet N r (realRademacherJet N r z ω) = realRademacherValue N r z ω := by
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN : (0 : ℝ) < N)).ne'
  rw [realRademacherJet_eq_normalizedPolynomialJet, realRademacherValue_eq_polynomial]
  ext i
  fin_cases i <;> simp only [normalizedValueOfJet, normalizedPolynomialJet, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals field_simp

/-- Measurable normalized value events pull back to measurable jet events. -/
theorem measurableSet_valueOfJet_preimage (N : ℕ) (r : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin 2))) (hA : MeasurableSet A) :
    MeasurableSet (normalizedValueOfJet N r ⁻¹' A) :=
  hA.preimage (normalizedValueOfJet N r).continuous_of_finiteDimensional.measurable

/-- Convex normalized value events pull back to convex jet events. -/
theorem isConvexSet_valueOfJet_preimage (N : ℕ) (r : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin 2))) (hA : Convexity.IsConvexSet ℝ A) :
    Convexity.IsConvexSet ℝ (normalizedValueOfJet N r ⁻¹' A) :=
  hA.preimage (Convexity.IsAffineMap.linearMap (normalizedValueOfJet N r))

/-- The projected jet event and the normalized value event have the same probability. -/
theorem realJet_measureReal_valueOfJet (N : ℕ) (hN : 0 < N) (r : ℝ) (z : ℂ)
    (A : Set (EuclideanSpace ℝ (Fin 2))) (hA : MeasurableSet A) :
    ((LogMoments.signMeasure N).map (realRademacherJet N r z)).real
      (normalizedValueOfJet N r ⁻¹' A) =
      ((LogMoments.signMeasure N).map (realRademacherValue N r z)).real A := by
  simp only [measureReal_def, Measure.map_apply (measurable_of_finite _)
    (measurableSet_valueOfJet_preimage N r A hA), Measure.map_apply (measurable_of_finite _) hA]
  congr 2
  ext ω
  simp only [Set.mem_preimage, normalizedValueOfJet_realRademacherJet N hN]

/-- The paired projected rectangle is the intersection of the two normalized value events. -/
theorem realPairedJet_measureReal_valueOfJet (N : ℕ) (hN : 0 < N) (r s : ℝ) (z w : ℂ)
    (A B : Set (EuclideanSpace ℝ (Fin 2))) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ((LogMoments.signMeasure N).map (realPairedRademacherJet N r s z w)).real
      ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹'
        ((normalizedValueOfJet N r ⁻¹' A) ×ˢ (normalizedValueOfJet N s ⁻¹' B))) =
      (LogMoments.signMeasure N).real {ω | realRademacherValue N r z ω ∈ A ∧
        realRademacherValue N s w ω ∈ B} := by
  have hE : MeasurableSet ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹'
      ((normalizedValueOfJet N r ⁻¹' A) ×ˢ (normalizedValueOfJet N s ⁻¹' B))) :=
    ((measurableSet_valueOfJet_preimage N r A hA).prod
      (measurableSet_valueOfJet_preimage N s B hB)).preimage (by fun_prop)
  rw [measureReal_def, Measure.map_apply (measurable_of_finite _) hE]
  congr 2
  ext ω
  simp only [Set.mem_preimage, finAddEquivProd_realPairedRademacherJet,
    Set.mem_prod, normalizedValueOfJet_realRademacherJet N hN, Set.mem_ofPred_eq]

/-- The two-point error includes two marginal comparisons and the separated-jet factorization. -/
def valuePairGaussianErrorConstant (C K : ℝ) : ℝ :=
  2 * valueGaussianErrorConstant C K + 2 * jetGaussianErrorConstant C K +
    pairedJetGaussianErrorConstant C K + 80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)

/-- The same coefficient sequence at two separated points has the joint circular Gaussian
limit, uniformly over pairs of measurable convex value events. -/
theorem exists_circular_gaussian_approximation_value_pair_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r s θ φ : ℝ)
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
      |(LogMoments.signMeasure N).real {ω |
          realRademacherValue N r (Complex.exp (Complex.I * θ)) ω ∈ A ∧
          realRademacherValue N s (Complex.exp (Complex.I * φ)) ω ∈ B} -
        circularGaussian.real A * circularGaussian.real B| ≤
        valuePairGaussianErrorConstant C K / Real.sqrt N := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_circular_gaussian_approximation_value_constant
  obtain ⟨C₂, hC₂, h₂⟩ := exists_annular_jet_factorization_constant
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum A B hA hB hcA hcB
  have hdegree' : (20 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ) := by
    calc
      _ ≤ (6400 * Real.exp (8 * K)) ^ 2 := by gcongr; norm_num
      _ ≤ _ := hdegree
  have hvmono : valueGaussianErrorConstant C₁ K ≤ valueGaussianErrorConstant (C₁ + C₂) K := by
    unfold valueGaussianErrorConstant
    gcongr
    linarith
  have hjmono : jetGaussianErrorConstant C₂ K ≤ jetGaussianErrorConstant (C₁ + C₂) K := by
    unfold jetGaussianErrorConstant
    gcongr
    linarith
  have hpmono : pairedJetGaussianErrorConstant C₂ K ≤ pairedJetGaussianErrorConstant (C₁ + C₂) K := by
    unfold pairedJetGaussianErrorConstant
    gcongr
    linarith
  have hm := h₂ N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum
    (normalizedValueOfJet N r ⁻¹' A) (normalizedValueOfJet N s ⁻¹' B)
    (measurableSet_valueOfJet_preimage N r A hA) (measurableSet_valueOfJet_preimage N s B hB)
    (isConvexSet_valueOfJet_preimage N r A hcA) (isConvexSet_valueOfJet_preimage N s B hcB)
  rw [realPairedJet_measureReal_valueOfJet N hN _ _ _ _ A B hA hB,
    realJet_measureReal_valueOfJet N hN _ _ A hA, realJet_measureReal_valueOfJet N hN _ _ B hB] at hm
  have hpair := hm.trans (div_le_div_of_nonneg_right
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hjmono (by norm_num : (0 : ℝ) ≤ 2)) hpmono) (le_refl _))
    (Real.sqrt_nonneg N))
  have hv₁ := (h₁ N hN K r θ hK hNK hrl hru hdegree' hθ A hA hcA).trans
    (div_le_div_of_nonneg_right hvmono (Real.sqrt_nonneg N))
  have hv₂ := (h₁ N hN K s φ hK hNK hsl hsu hdegree' hφ B hB hcB).trans
    (div_le_div_of_nonneg_right hvmono (Real.sqrt_nonneg N))
  let p₁ := ((LogMoments.signMeasure N).map
    (realRademacherValue N r (Complex.exp (Complex.I * θ)))).real A
  let p₂ := ((LogMoments.signMeasure N).map
    (realRademacherValue N s (Complex.exp (Complex.I * φ)))).real B
  let p := (LogMoments.signMeasure N).real {ω |
    realRademacherValue N r (Complex.exp (Complex.I * θ)) ω ∈ A ∧
    realRademacherValue N s (Complex.exp (Complex.I * φ)) ω ∈ B}
  have hproduct := (abs_mul_sub_mul_le_of_unitInterval p₁ p₂ (circularGaussian.real A)
    (circularGaussian.real B) measureReal_nonneg measureReal_le_one
    measureReal_nonneg measureReal_le_one).trans (add_le_add hv₁ hv₂)
  change |p - p₁ * p₂| ≤ _ at hpair
  change |p - circularGaussian.real A * circularGaussian.real B| ≤ _
  calc
    _ ≤ |p - p₁ * p₂| + |p₁ * p₂ - circularGaussian.real A * circularGaussian.real B| :=
      abs_sub_le _ _ _
    _ ≤ (2 * jetGaussianErrorConstant (C₁ + C₂) K + pairedJetGaussianErrorConstant (C₁ + C₂) K +
        80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N +
      (valueGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N +
        valueGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N) := add_le_add hpair hproduct
    _ = _ := by unfold valuePairGaussianErrorConstant; ring

end Erdos522

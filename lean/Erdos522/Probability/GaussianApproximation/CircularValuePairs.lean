/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.CircularValues
import Erdos522.Probability.GaussianApproximation.CircularPairedSmallBall
import Erdos522.Probability.GaussianApproximation.ValuePairs

/-!
# Two-point circular-value approximation

Projection of the separated circular jets gives two polynomial values with
exact standard-deviation normalization. Their joint law is close to two
independent standard circular Gaussian values.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder
namespace Erdos522

local instance {d : ℕ} : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule
local instance {d : ℕ} : Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.of_module

/-- The projection gives the actual exactly normalized value of the same polynomial. -/
theorem normalizedValueOfJet_circularJet (N : ℕ) (hN : 0 < N) (r : ℝ) (z : ℂ)
    (ω : Fin (N + 1) → ℂ) :
    normalizedValueOfJet N r (circularJet N r z ω) = circularValue N r z ω := by
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN : (0 : ℝ) < N)).ne'
  rw [circularJet_eq_normalizedPolynomialJet, circularValue_eq_polynomial]
  ext i
  fin_cases i <;> simp only [normalizedValueOfJet, normalizedPolynomialJet, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals field_simp

/-- The projected jet event and the normalized value event have the same probability. -/
theorem circularJet_measureReal_valueOfJet (N : ℕ) (hN : 0 < N) (r : ℝ) (z : ℂ)
    (A : Set (EuclideanSpace ℝ (Fin 2))) (hA : MeasurableSet A) :
    ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map (circularJet N r z)).real
      (normalizedValueOfJet N r ⁻¹' A) =
      ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map (circularValue N r z)).real A := by
  simp only [measureReal_def, Measure.map_apply (measurable_circularJet N r z)
    (measurableSet_valueOfJet_preimage N r A hA), Measure.map_apply (measurable_circularValue N r z) hA]
  congr 2
  ext ω
  simp only [Set.mem_preimage, normalizedValueOfJet_circularJet N hN]

/-- The paired projected rectangle is the intersection of the two normalized value events. -/
theorem circularPairedJet_measureReal_valueOfJet (N : ℕ) (hN : 0 < N) (r s : ℝ) (z w : ℂ)
    (A B : Set (EuclideanSpace ℝ (Fin 2))) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map (circularPairedJet N r s z w)).real
      ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹'
        ((normalizedValueOfJet N r ⁻¹' A) ×ˢ (normalizedValueOfJet N s ⁻¹' B))) =
      (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real {ω | circularValue N r z ω ∈ A ∧
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
def circularValuePairGaussianErrorConstant (C K : ℝ) : ℝ :=
  2 * circularValueGaussianErrorConstant C K + 2 * circularJetGaussianErrorConstant C K +
    circularPairedJetGaussianErrorConstant C K + 80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)

/-- The same coefficient sequence at two separated points has the joint circular Gaussian
limit, uniformly over pairs of measurable convex value events. -/
theorem exists_gaussian_approximation_circular_value_pair_constant :
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
      |(Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real {ω |
          circularValue N r (Complex.exp (Complex.I * θ)) ω ∈ A ∧
          circularValue N s (Complex.exp (Complex.I * φ)) ω ∈ B} -
        circularGaussian.real A * circularGaussian.real B| ≤
        circularValuePairGaussianErrorConstant C K / Real.sqrt N := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_gaussian_approximation_circular_value_constant
  obtain ⟨C₂, hC₂, h₂⟩ := exists_annular_circular_jet_factorization_constant
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum A B hA hB hcA hcB
  have hvmono : circularValueGaussianErrorConstant C₁ K ≤ circularValueGaussianErrorConstant (C₁ + C₂) K := by
    unfold circularValueGaussianErrorConstant
    gcongr
    linarith
  have hjmono : circularJetGaussianErrorConstant C₂ K ≤ circularJetGaussianErrorConstant (C₁ + C₂) K := by
    unfold circularJetGaussianErrorConstant
    gcongr
    linarith
  have hpmono : circularPairedJetGaussianErrorConstant C₂ K ≤ circularPairedJetGaussianErrorConstant (C₁ + C₂) K := by
    unfold circularPairedJetGaussianErrorConstant
    gcongr
    linarith
  have hm := h₂ N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum
    (normalizedValueOfJet N r ⁻¹' A) (normalizedValueOfJet N s ⁻¹' B)
    (measurableSet_valueOfJet_preimage N r A hA) (measurableSet_valueOfJet_preimage N s B hB)
    (isConvexSet_valueOfJet_preimage N r A hcA) (isConvexSet_valueOfJet_preimage N s B hcB)
  rw [circularPairedJet_measureReal_valueOfJet N hN _ _ _ _ A B hA hB,
    circularJet_measureReal_valueOfJet N hN _ _ A hA, circularJet_measureReal_valueOfJet N hN _ _ B hB] at hm
  have hpair := hm.trans (div_le_div_of_nonneg_right
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hjmono (by norm_num : (0 : ℝ) ≤ 2)) hpmono) (le_refl _))
    (Real.sqrt_nonneg N))
  have hv₁ := (h₁ N hN K r hK hNK hrl hru (Complex.exp (Complex.I * θ))
    (Complex.norm_exp_I_mul_ofReal θ) A hA hcA).trans
    (div_le_div_of_nonneg_right hvmono (Real.sqrt_nonneg N))
  have hv₂ := (h₁ N hN K s hK hNK hsl hsu (Complex.exp (Complex.I * φ))
    (Complex.norm_exp_I_mul_ofReal φ) B hB hcB).trans
    (div_le_div_of_nonneg_right hvmono (Real.sqrt_nonneg N))
  let p₁ := ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map
    (circularValue N r (Complex.exp (Complex.I * θ)))).real A
  let p₂ := ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map
    (circularValue N s (Complex.exp (Complex.I * φ)))).real B
  let p := (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real {ω |
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
    _ ≤ (2 * circularJetGaussianErrorConstant (C₁ + C₂) K + circularPairedJetGaussianErrorConstant (C₁ + C₂) K +
        80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N +
      (circularValueGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N +
        circularValueGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N) := add_le_add hpair hproduct
    _ = _ := by unfold circularValuePairGaussianErrorConstant; ring


end Erdos522

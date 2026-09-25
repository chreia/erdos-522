/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianVectors
import Erdos522.Probability.GaussianApproximation.BoundedValuePairs

/-!
# Normalized circular Gaussian polynomial values

The exact finite-dimensional Gaussian law and covariance comparison control
one-point and separated two-point events in the finite radial normalization.
-/

noncomputable section
open MeasureTheory ProbabilityTheory WithLp
namespace Erdos522

/-- One Gaussian value differs from the circular target by an explicit covariance error. -/
theorem circularGaussian_value_circular_comparison (N : ℕ) (hN : 0 < N) (K r θ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (20 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (A : Set (EuclideanSpace ℝ (Fin 2))) (hA : MeasurableSet A) :
    |(Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {g |
      circularValue N r (Complex.exp (Complex.I * θ)) g ∈ A} - circularGaussian.real A| ≤
      10 * Real.exp (8 * K) / Real.sqrt N := by
  have hb := gaussian_complexValue_circular_comparison circularComplexGaussian
    memLp_two_id_circularComplexGaussian integral_id_circularComplexGaussian
    integral_norm_sq_circularComplexGaussian N hN K r θ hK hNK hrl hru hdegree hangle A hA
  rw [← map_circularGaussianVectorSum, measureReal_def,
    Measure.map_apply (by unfold circularVectorSum circularVector; fun_prop) hA] at hb
  exact hb

/-- The exact two-point circular comparison constant. -/
def circularGaussianValuePairError (K : ℝ) : ℝ :=
  80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80) + 20 * Real.exp (8 * K)

/-- Two separated Gaussian values approach independent circular values for every measurable rectangle. -/
theorem circularGaussian_value_pair_circular_comparison (N : ℕ) (hN : 0 < N) (K r s θ φ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsl : 1 - K / N ≤ s) (hsu : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hθ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (hφ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
    (A B : Set (EuclideanSpace ℝ (Fin 2))) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |(Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {g |
        circularValue N r (Complex.exp (Complex.I * θ)) g ∈ A ∧
        circularValue N s (Complex.exp (Complex.I * φ)) g ∈ B} -
      circularGaussian.real A * circularGaussian.real B| ≤ circularGaussianValuePairError K / Real.sqrt N := by
  have hdegree' : (20 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ) := by
    calc
      _ ≤ (6400 * Real.exp (8 * K)) ^ 2 := by gcongr; norm_num
      _ ≤ _ := hdegree
  have h₁ := circularGaussian_value_circular_comparison N hN K r θ hK hNK hrl hru hdegree' hθ A hA
  have h₂ := circularGaussian_value_circular_comparison N hN K s φ hK hNK hsl hsu hdegree' hφ B hB
  have hp := gaussian_complexPairedJet_measureReal_prod_le circularComplexGaussian
    memLp_two_id_circularComplexGaussian integral_id_circularComplexGaussian
    integral_norm_sq_circularComplexGaussian N hN K r s θ φ hK hNK hrl hru hsl hsu
    hdegree hθ hφ hdifference hsum (normalizedValueOfJet N r ⁻¹' A) (normalizedValueOfJet N s ⁻¹' B)
    (measurableSet_valueOfJet_preimage N r A hA) (measurableSet_valueOfJet_preimage N s B hB)
  rw [← map_circularGaussianVectorSum, ← map_circularGaussianVectorSum,
    ← map_circularGaussianVectorSum] at hp
  change |((Measure.pi (fun _ : Fin (N+1) => circularComplexGaussian)).map
      (circularPairedJet N r s (Complex.exp (Complex.I*θ)) (Complex.exp (Complex.I*φ)))).real
      ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹'
        ((normalizedValueOfJet N r ⁻¹' A) ×ˢ (normalizedValueOfJet N s ⁻¹' B))) -
      ((Measure.pi (fun _ : Fin (N+1) => circularComplexGaussian)).map
        (circularJet N r (Complex.exp (Complex.I*θ)))).real (normalizedValueOfJet N r ⁻¹' A) *
      ((Measure.pi (fun _ : Fin (N+1) => circularComplexGaussian)).map
        (circularJet N s (Complex.exp (Complex.I*φ)))).real (normalizedValueOfJet N s ⁻¹' B)| ≤ _ at hp
  rw [coefficientPairedJet_measureReal_valueOfJet circularComplexGaussian N hN _ _ _ _ A B hA hB,
    coefficientJet_measureReal_valueOfJet circularComplexGaussian N hN _ _ A hA,
    coefficientJet_measureReal_valueOfJet circularComplexGaussian N hN _ _ B hB] at hp
  simp only [measureReal_def, Measure.map_apply (measurable_circularValue _ _ _) hA,
    Measure.map_apply (measurable_circularValue _ _ _) hB] at hp
  have hm := abs_mul_sub_mul_le_of_unitInterval
    ((Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {g | circularValue N r (Complex.exp (Complex.I * θ)) g ∈ A})
    ((Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {g | circularValue N s (Complex.exp (Complex.I * φ)) g ∈ B})
    (circularGaussian.real A) (circularGaussian.real B)
    measureReal_nonneg measureReal_le_one measureReal_nonneg measureReal_le_one
  calc
    _ ≤ |(Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {g |
        circularValue N r (Complex.exp (Complex.I * θ)) g ∈ A ∧
        circularValue N s (Complex.exp (Complex.I * φ)) g ∈ B} -
      (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {g | circularValue N r (Complex.exp (Complex.I * θ)) g ∈ A} *
      (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {g | circularValue N s (Complex.exp (Complex.I * φ)) g ∈ B}| +
      |(Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {g | circularValue N r (Complex.exp (Complex.I * θ)) g ∈ A} *
      (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {g | circularValue N s (Complex.exp (Complex.I * φ)) g ∈ B} -
      circularGaussian.real A * circularGaussian.real B| := abs_sub_le _ _ _
    _ ≤ (80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N +
      (10 * Real.exp (8 * K) / Real.sqrt N + 10 * Real.exp (8 * K) / Real.sqrt N) :=
      add_le_add hp (hm.trans (add_le_add h₁ h₂))
    _ = _ := by unfold circularGaussianValuePairError; ring

end Erdos522

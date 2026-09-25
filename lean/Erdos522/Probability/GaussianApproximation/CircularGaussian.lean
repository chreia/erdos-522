/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.Values
import Erdos522.Probability.GaussianApproximation.DiagonalEntropy
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Radial integrals for the circular Gaussian

The circular Gaussian has independent real coordinates of variance one half.
Its radial density is `2 r exp (-r²)`, giving the disk distribution exactly.
-/

noncomputable section
open MeasureTheory ProbabilityTheory WithLp Metric Set
open scoped ENNReal NNReal

namespace Erdos522

/-- Cartesian coordinates identify the real plane with a product of two real lines. -/
def valueCartesianCoordinates : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.piFinTwo fun _ => ℝ)

/-- Cartesian coordinates preserve the Euclidean volume normalization. -/
theorem volume_preserving_valueCartesianCoordinates : MeasurePreserving valueCartesianCoordinates :=
  (volume_preserving_piFinTwo fun _ : Fin 2 => ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

/-- The circular Gaussian has independent real Gaussian coordinates of variance one half. -/
theorem measurePreserving_circularGaussian_coordinates :
    MeasurePreserving valueCartesianCoordinates circularGaussian
      ((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))) := by
  have h := map_pi_gaussianReal_eq_multivariateGaussian (fun _ : Fin 2 => (1 / 2 : ℝ≥0))
  have hp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))
      (Measure.pi fun _ : Fin 2 => gaussianReal 0 (1 / 2)) circularGaussian :=
    ⟨(MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable, by
      change (Measure.pi fun _ : Fin 2 => gaussianReal 0 (1 / 2)).map (toLp 2) = _
      simpa only [circularGaussian, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using h⟩
  exact (measurePreserving_piFinTwo fun _ : Fin 2 => gaussianReal 0 (1 / 2)).comp hp.symm

/-- The product of the two real densities is the circular Gaussian density. -/
theorem gaussianPDFReal_half_prod (x y : ℝ) :
    gaussianPDFReal 0 (1 / 2) x * gaussianPDFReal 0 (1 / 2) y =
      Real.exp (-(x ^ 2 + y ^ 2)) / Real.pi := by
  have hs : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hs2 : Real.sqrt (2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  simp only [gaussianPDFReal, NNReal.coe_div, NNReal.coe_one]
  norm_num
  rw [Real.exp_add]
  field_simp
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

/-- Integrating against the circular Gaussian amounts to multiplying by `exp (-‖x‖²) / π`. -/
theorem integral_circularGaussian (f : EuclideanSpace ℝ (Fin 2) → ℝ) :
    (∫ x, f x ∂circularGaussian) =
      ∫ x, Real.exp (-‖x‖ ^ 2) / Real.pi * f x := by
  rw [← measurePreserving_circularGaussian_coordinates.symm.integral_comp
    valueCartesianCoordinates.symm.measurableEmbedding f]
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 / 2 : ℝ≥0) ≠ 0),
    prod_withDensity (measurable_gaussianPDF 0 (1 / 2)) (measurable_gaussianPDF 0 (1 / 2)),
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top)]
  have hnorm (p : ℝ × ℝ) :
      ‖valueCartesianCoordinates.symm p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    rfl
  rw [← volume_preserving_valueCartesianCoordinates.symm.integral_comp
    valueCartesianCoordinates.symm.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with p
  simp only [ENNReal.toReal_mul, toReal_gaussianPDF, smul_eq_mul, gaussianPDFReal_half_prod, hnorm]

/-- A radial function under the circular Gaussian has one-dimensional density `2 r exp (-r²)`. -/
theorem integral_circularGaussian_radial (g : ℝ → ℝ) :
    (∫ x, g ‖x‖ ∂circularGaussian) = ∫ r in Ioi (0 : ℝ), 2 * r * Real.exp (-r ^ 2) * g r := by
  rw [integral_circularGaussian]
  have h := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (fun r : ℝ => Real.exp (-r ^ 2) / Real.pi * g r)
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, smul_eq_mul, nsmul_eq_mul, measureReal_def, EuclideanSpace.volume_ball_fin_two,
    ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal Real.pi_pos.le] at h
  rw [h, ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  field_simp

/-- The radial density has an elementary antiderivative. -/
theorem integral_circular_radial_density (t : ℝ) :
    (∫ r in (0 : ℝ)..t, 2 * r * Real.exp (-r ^ 2)) = 1 - Real.exp (-t ^ 2) := by
  have hderiv (r : ℝ) : HasDerivAt (fun r : ℝ => -Real.exp (-r ^ 2))
      (2 * r * Real.exp (-r ^ 2)) r := by
    convert (((hasDerivAt_id r).pow 2).neg.exp).neg using 1
    · ext x
      rfl
    · simp [Pi.neg_apply, Pi.pow_apply, mul_comm, mul_left_comm]
  have hint : IntervalIntegrable (fun r : ℝ => 2 * r * Real.exp (-r ^ 2)) volume 0 t :=
    (show Continuous (fun r : ℝ => 2 * r * Real.exp (-r ^ 2)) by fun_prop).intervalIntegrable _ _
  simpa [sub_eq_add_neg, add_comm] using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hderiv r) hint

/-- The standard circular Gaussian disk probability is `1 - exp (-t²)` for `t ≥ 0`. -/
theorem circularGaussian_real_closedBall (t : ℝ) (ht : 0 ≤ t) :
    circularGaussian.real (closedBall 0 t) = 1 - Real.exp (-t ^ 2) := by
  have h := integral_circularGaussian_radial ((Iic t).indicator fun _ => 1)
  have hleft : (fun x : EuclideanSpace ℝ (Fin 2) => (Iic t).indicator (fun _ => (1 : ℝ)) ‖x‖) =
      (closedBall 0 t).indicator (fun _ => 1) := by
    ext x
    simp only [Set.indicator, mem_Iic, mem_closedBall, dist_zero_right]
  rw [hleft, integral_indicator_const (1 : ℝ) measurableSet_closedBall] at h
  simp only [smul_eq_mul, mul_one] at h
  have hright : (fun r : ℝ => 2 * r * Real.exp (-r ^ 2) * (Iic t).indicator (fun _ => 1) r) =
      (Iic t).indicator (fun r : ℝ => 2 * r * Real.exp (-r ^ 2)) := by
    ext r
    by_cases hr : r ≤ t <;> simp [hr]
  rw [hright, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic] at h
  have hset : Iic t ∩ Ioi (0 : ℝ) = Ioc 0 t := by ext r; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc]; tauto
  rw [hset, ← intervalIntegral.integral_of_le ht, integral_circular_radial_density] at h
  exact h

end Erdos522

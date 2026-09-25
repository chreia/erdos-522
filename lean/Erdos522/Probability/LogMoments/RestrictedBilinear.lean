/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.BilinearKhintchine

/-!
# Restricted integrals of quadratic Rademacher Fourier sums

Hölder's inequality converts the coefficient-uniform moment estimate into a
quantitative estimate on each measurable portion of the sign-and-angle space.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos522.LogMoments

/-- A restricted `L¹` integral in terms of a global `Lᵖ` moment. -/
theorem integral_norm_restrict_le_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℂ} {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) (E : Set Ω) :
    (∫ ω in E, ‖f ω‖ ∂μ) ≤
      (∫ ω, ‖f ω‖ ^ p ∂μ) ^ (1 / p) * μ.real E ^ (1 - 1 / p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hconj := Real.HolderConjugate.conjExponent hp
  have h := integral_mul_norm_le_Lp_mul_Lq hconj (hf.restrict E)
    (memLp_const (μ := μ.restrict E) (1 : ℂ))
  have hexp : 1 / Real.conjExponent p = 1 - 1 / p := by
    have hc := hconj.inv_add_inv_eq_one
    simpa only [one_div] using (eq_sub_of_add_eq' hc)
  simp only [norm_one, mul_one, Real.one_rpow, integral_const,
    measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
    smul_eq_mul, hexp] at h
  have hi : Integrable (fun ω => ‖f ω‖ ^ p) μ := by
    have hi := hf.integrable_norm_rpow
      (by simp [hp0]) ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp0.le] using hi
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (measureReal_nonneg) _)
  apply Real.rpow_le_rpow (integral_nonneg (fun ω => Real.rpow_nonneg (norm_nonneg _) _))
    _ (by positivity)
  exact integral_mono_measure Measure.restrict_le_self
    (ae_of_all _ fun ω => Real.rpow_nonneg (norm_nonneg _) _) hi

/-- The elementary bound furnishing all `Lᵖ` memberships. -/
theorem norm_randomBilinearFourier_le {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (q : SignVector N × AddCircle (1 : ℝ)) :
    ‖randomBilinearFourier A q‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  unfold randomBilinearFourier complexQuadraticSignSum
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · simp only [hij, ite_true, zero_mul, norm_zero]
    exact norm_nonneg _
  · simp only [hij, ite_false, norm_mul, norm_sign, mul_one,
      fourier_apply, Circle.norm_coe]
    exact le_rfl

theorem memLp_randomBilinearFourier {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (p : ENNReal) :
    MemLp (randomBilinearFourier A) p (fourierMeasure N) := by
  exact MemLp.of_bound (measurable_randomBilinearFourier A).aestronglyMeasurable
    (∑ i, ∑ j, ‖A i j‖) (ae_of_all _ (norm_randomBilinearFourier_le A))

/-- The restricted bilinear estimate: the measure exponent tends to one as the
    moment order grows, while the constant grows linearly in that order. -/
theorem integral_norm_randomBilinearFourier_restrict_le {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    {V : ℝ} (hV : 0 < V)
    (hA : ∑ i, ∑ j, (if i = j then 0 else ‖A i j‖ ^ 2) ≤ V)
    (m : ℕ) (hm : 1 ≤ m) (E : Set (SignVector N × AddCircle (1 : ℝ))) :
    (∫ q in E, ‖randomBilinearFourier A q‖ ∂fourierMeasure N) ≤
      (16 * Real.exp 2 * (m : ℝ)) * Real.sqrt V *
        (fourierMeasure N).real E ^ (1 - 1 / (2 * (m : ℝ))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hp : (1 : ℝ) < 2 * (m : ℝ) := by exact_mod_cast (by omega : 1 < 2 * m)
  have h := integral_norm_restrict_le_moment hp
    (memLp_randomBilinearFourier A (ENNReal.ofReal (2 * (m : ℝ)))) E
  have hmoment := integral_even_norm_randomBilinearFourier_le A hV hA m hm
  have hnat : (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) := by norm_num
  rw [hnat] at h
  simp only [Real.rpow_natCast] at h
  have hroot :
      ((16 * Real.exp 2 * (m : ℝ)) ^ (2 * m) * V ^ m) ^
        (1 / ((2 * m : ℕ) : ℝ)) = (16 * Real.exp 2 * (m : ℝ)) * Real.sqrt V := by
    have hv : V ^ m = Real.sqrt V ^ (2 * m) := by
      rw [pow_mul, Real.sq_sqrt hV.le]
    rw [hv, ← mul_pow, ← Real.rpow_natCast, one_div,
      Real.rpow_rpow_inv (by positivity) (by positivity)]
  calc
    _ ≤ (∫ q, ‖randomBilinearFourier A q‖ ^ (2 * m) ∂fourierMeasure N) ^
        (1 / ((2 * m : ℕ) : ℝ)) *
        (fourierMeasure N).real E ^ (1 - 1 / ((2 * m : ℕ) : ℝ)) := h
    _ ≤ ((16 * Real.exp 2 * (m : ℝ)) ^ (2 * m) * V ^ m) ^
        (1 / ((2 * m : ℕ) : ℝ)) *
        (fourierMeasure N).real E ^ (1 - 1 / ((2 * m : ℕ) : ℝ)) := by
      gcongr
    _ = _ := by rw [hroot, ← hnat]

end Erdos522.LogMoments

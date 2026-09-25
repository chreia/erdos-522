/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.JetSmallBall

/-!
# Finite sums of independent real Gaussian coefficients

The coefficient law is the product of standard real Gaussian measures.
Real linear projections have their exact centered Gaussian laws; these laws
control complex sums uniformly over every normalized coefficient vector.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set WithLp
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
namespace Erdos522

/-- The independent standard real Gaussian coefficient law. -/
def gaussianCoefficientMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance (n : ℕ) : IsProbabilityMeasure (gaussianCoefficientMeasure n) := by
  unfold gaussianCoefficientMeasure
  infer_instance

/-- A real projection of a finite Gaussian coefficient vector. -/
def realGaussianSum {n : ℕ} (b : Fin n → ℝ) (g : Fin n → ℝ) : ℝ := ∑ k, b k * g k

/-- A complex linear combination of independent standard real Gaussians. -/
def complexGaussianSum {n : ℕ} (a : Fin n → ℂ) (g : Fin n → ℝ) : ℂ :=
  ∑ k, (g k : ℂ) * a k

theorem measurable_realGaussianSum {n : ℕ} (b : Fin n → ℝ) : Measurable (realGaussianSum b) := by
  unfold realGaussianSum
  fun_prop

theorem measurable_complexGaussianSum {n : ℕ} (a : Fin n → ℂ) :
    Measurable (complexGaussianSum a) := by
  unfold complexGaussianSum
  fun_prop

/-- Every real projection is Gaussian with variance the squared norm of its coefficients. -/
theorem map_realGaussianSum {n : ℕ} (b : Fin n → ℝ) :
    (gaussianCoefficientMeasure n).map (realGaussianSum b) =
      gaussianReal 0 (Real.toNNReal (∑ k, b k ^ 2)) := by
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ (toLp 2 b)
  have he : realGaussianSum b = L ∘ (toLp 2) := by
    funext g
    simp [realGaussianSum, L, PiLp.inner_apply, mul_comm]
  rw [he, ← Measure.map_map L.measurable (by fun_prop), gaussianCoefficientMeasure,
    map_pi_eq_stdGaussian, IsGaussian.map_eq_gaussianReal,
    integral_strongDual_stdGaussian, variance_dual_stdGaussian]
  congr 2
  simp [L, innerSL_apply_norm, EuclideanSpace.real_norm_sq_eq]

/-- The square of each real projection is integrable. -/
theorem integrable_sq_realGaussianSum {n : ℕ} (b : Fin n → ℝ) :
    Integrable (fun g => realGaussianSum b g ^ 2) (gaussianCoefficientMeasure n) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := Real.toNNReal (∑ k, b k ^ 2)) 2).integrable_sq
  rw [← map_realGaussianSum b] at h
  exact (integrable_map_measure (by fun_prop) (measurable_realGaussianSum b).aemeasurable).mp h

/-- The exact second moment of a real projection. -/
theorem integral_sq_realGaussianSum {n : ℕ} (b : Fin n → ℝ) :
    (∫ g, realGaussianSum b g ^ 2 ∂gaussianCoefficientMeasure n) = ∑ k, b k ^ 2 := by
  have hm := integral_map (μ := gaussianCoefficientMeasure n)
    (f := fun x : ℝ => x ^ 2) (measurable_realGaussianSum b).aemeasurable (by fun_prop)
  rw [map_realGaussianSum] at hm
  rw [← hm]
  have hv := variance_eq_integral (μ := gaussianReal 0 (Real.toNNReal (∑ k, b k ^ 2)))
    (X := fun x : ℝ => x) measurable_id.aemeasurable
  simpa only [variance_fun_id_gaussianReal, integral_id_gaussianReal, sub_zero,
    Real.coe_toNNReal _ (Finset.sum_nonneg fun k _ => sq_nonneg (b k))] using hv.symm

theorem complexGaussianSum_re {n : ℕ} (a : Fin n → ℂ) (g : Fin n → ℝ) :
    (complexGaussianSum a g).re = realGaussianSum (fun k => (a k).re) g := by
  simp [complexGaussianSum, realGaussianSum, Complex.mul_re, mul_comm]

theorem complexGaussianSum_im {n : ℕ} (a : Fin n → ℂ) (g : Fin n → ℝ) :
    (complexGaussianSum a g).im = realGaussianSum (fun k => (a k).im) g := by
  simp [complexGaussianSum, realGaussianSum, Complex.mul_im, mul_comm]

/-- The complex sum has an integrable squared modulus. -/
theorem integrable_norm_sq_complexGaussianSum {n : ℕ} (a : Fin n → ℂ) :
    Integrable (fun g => ‖complexGaussianSum a g‖ ^ 2) (gaussianCoefficientMeasure n) := by
  have he (g : Fin n → ℝ) : ‖complexGaussianSum a g‖ ^ 2 =
      realGaussianSum (fun k => (a k).re) g ^ 2 + realGaussianSum (fun k => (a k).im) g ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, complexGaussianSum_re, complexGaussianSum_im]
    ring
  simp_rw [he]
  exact (integrable_sq_realGaussianSum _).add (integrable_sq_realGaussianSum _)

/-- The total second moment is the squared norm of the complex coefficient vector. -/
theorem integral_norm_sq_complexGaussianSum {n : ℕ} (a : Fin n → ℂ) :
    (∫ g, ‖complexGaussianSum a g‖ ^ 2 ∂gaussianCoefficientMeasure n) = ∑ k, ‖a k‖ ^ 2 := by
  have he (g : Fin n → ℝ) : ‖complexGaussianSum a g‖ ^ 2 =
      realGaussianSum (fun k => (a k).re) g ^ 2 + realGaussianSum (fun k => (a k).im) g ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, complexGaussianSum_re, complexGaussianSum_im]
    ring
  simp_rw [he]
  rw [integral_add (integrable_sq_realGaussianSum _) (integrable_sq_realGaussianSum _),
    integral_sq_realGaussianSum, integral_sq_realGaussianSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Variance at least one half makes the centered real Gaussian density at most one. -/
theorem gaussianReal_le_volume_of_half_le {v : ℝ≥0} (hv : (1 / 2 : ℝ) ≤ v) :
    gaussianReal 0 v ≤ volume := by
  have hv0 : 0 < (v : ℝ) := lt_of_lt_of_le (by norm_num) hv
  have h := gaussianReal_le_density_constant v (by exact_mod_cast hv0.ne')
  have hs : 1 ≤ Real.sqrt (2 * Real.pi * v) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have hc : (Real.sqrt (2 * Real.pi * v))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  exact h.trans (by
    calc
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹) • volume ≤ (1 : ℝ≥0∞) • volume := by
        gcongr
        simpa using ENNReal.ofReal_le_ofReal hc
      _ = volume := one_smul _ _)

/-- A real Gaussian projection with variance at least one half has a linear small-ball bound. -/
theorem realGaussianSum_small_ball {n : ℕ} (b : Fin n → ℝ)
    (hb : (1 / 2 : ℝ) ≤ ∑ k, b k ^ 2) {u : ℝ} (_hu : 0 ≤ u) :
    gaussianCoefficientMeasure n {g | |realGaussianSum b g| ≤ u} ≤ ENNReal.ofReal (2 * u) := by
  have hm : MeasurableSet (Icc (-u) u) := measurableSet_Icc
  have he : {g | |realGaussianSum b g| ≤ u} = realGaussianSum b ⁻¹' Icc (-u) u := by
    ext g
    simp only [mem_ofPred_eq, mem_preimage, mem_Icc, abs_le]
  rw [he, ← Measure.map_apply (measurable_realGaussianSum b) hm, map_realGaussianSum]
  have hv : (1 / 2 : ℝ) ≤ (Real.toNNReal (∑ k, b k ^ 2) : ℝ) :=
    hb.trans (Real.le_coe_toNNReal _)
  refine (gaussianReal_le_volume_of_half_le hv (Icc (-u) u)).trans_eq ?_
  rw [Real.volume_Icc]
  congr 1
  ring

/-- Every normalized complex coefficient vector has a real Gaussian projection
of variance at least one half, giving the uniform bound `2u`. -/
theorem complexGaussianSum_small_ball {n : ℕ} (a : Fin n → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) {u : ℝ} (hu : 0 ≤ u) :
    gaussianCoefficientMeasure n {g | ‖complexGaussianSum a g‖ ≤ u} ≤ ENNReal.ofReal (2 * u) := by
  have hsplit : (∑ k, (a k).re ^ 2) + (∑ k, (a k).im ^ 2) = 1 := by
    rw [← Finset.sum_add_distrib, ← ha]
    apply Finset.sum_congr rfl
    intro k _
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hbig : (1 / 2 : ℝ) ≤ ∑ k, (a k).re ^ 2 ∨ (1 / 2 : ℝ) ≤ ∑ k, (a k).im ^ 2 := by
    by_contra h
    push Not at h
    linarith
  rcases hbig with hre | him
  · refine (measure_mono (show {g | ‖complexGaussianSum a g‖ ≤ u} ⊆
        {g | |realGaussianSum (fun k => (a k).re) g| ≤ u} from ?_)).trans
      (realGaussianSum_small_ball _ hre hu)
    intro g hg
    change |realGaussianSum (fun k => (a k).re) g| ≤ u
    rw [← complexGaussianSum_re]
    exact (Complex.abs_re_le_norm _).trans hg
  · refine (measure_mono (show {g | ‖complexGaussianSum a g‖ ≤ u} ⊆
        {g | |realGaussianSum (fun k => (a k).im) g| ≤ u} from ?_)).trans
      (realGaussianSum_small_ball _ him hu)
    intro g hg
    change |realGaussianSum (fun k => (a k).im) g| ≤ u
    rw [← complexGaussianSum_im]
    exact (Complex.abs_im_le_norm _).trans hg

end Erdos522

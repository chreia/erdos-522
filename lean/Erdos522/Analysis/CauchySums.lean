/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Finite Cauchy sums in a half-plane

Reflecting each pole into the closed lower half-plane dominates the norm of a
Cauchy sum on the real axis. A fractional linear transform of the reflected sum
has nonnegative real part, bounded by one, and detects its large values.
Cauchy--Goursat on expanding rectangles bounds its real-axis integral. Dominated
convergence and Markov's inequality give the weak first-order estimate
`volume {x | y ≤ ‖∑ (x - pole)⁻¹‖} ≤ 16 * card / y` for `y > 0`.
Finite indexed families and multisets retain repeated poles with their multiplicities.
-/

noncomputable section

open scoped BigOperators
open Complex Metric
open MeasureTheory Filter
open scoped Topology

namespace Erdos522
namespace CauchySums

/-- Reflection of a complex number into the closed lower half-plane. -/
def lowerPole (z : ℂ) : ℂ := ⟨z.re, -|z.im|⟩

@[simp] theorem lowerPole_re (z : ℂ) : (lowerPole z).re = z.re := rfl

@[simp] theorem lowerPole_im (z : ℂ) : (lowerPole z).im = -|z.im| := rfl

/-- The Cauchy sum of a finite family, including repetitions. -/
def cauchySum {ι : Type*} [Fintype ι] (poles : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ i, (z - poles i)⁻¹

/-- A transform taking the closed lower half-plane into the unit disk. -/
def levelTransform (y : ℝ) (w : ℂ) : ℂ := w / (w - (y : ℂ) * I)

theorem normSq_real_sub_lowerPole (x : ℝ) (z : ℂ) :
    normSq ((x : ℂ) - lowerPole z) = normSq ((x : ℂ) - z) := by
  simp only [normSq_apply, sub_re, ofReal_re, lowerPole_re, sub_im, ofReal_im,
    lowerPole_im, zero_sub, neg_neg]
  nlinarith [sq_abs z.im]

theorem inv_real_sub_lowerPole_re (x : ℝ) (z : ℂ) :
    (((x : ℂ) - lowerPole z)⁻¹).re = (((x : ℂ) - z)⁻¹).re := by
  simp only [inv_re, sub_re, ofReal_re, lowerPole_re, normSq_real_sub_lowerPole]

theorem inv_real_sub_lowerPole_im (x : ℝ) (z : ℂ) :
    (((x : ℂ) - lowerPole z)⁻¹).im = -|(((x : ℂ) - z)⁻¹).im| := by
  simp only [inv_im, sub_im, ofReal_im, lowerPole_im, zero_sub, neg_neg,
    normSq_real_sub_lowerPole, abs_div, abs_of_nonneg (normSq_nonneg _), neg_div]

theorem cauchySum_lowerPole_re {ι : Type*} [Fintype ι]
    (poles : ι → ℂ) (x : ℝ) :
    (cauchySum (lowerPole ∘ poles) x).re = (cauchySum poles x).re := by
  simp only [cauchySum, re_sum, Function.comp_apply, inv_real_sub_lowerPole_re]

theorem abs_cauchySum_im_le {ι : Type*} [Fintype ι]
    (poles : ι → ℂ) (x : ℝ) :
    |(cauchySum poles x).im| ≤ -(cauchySum (lowerPole ∘ poles) x).im := by
  simp only [cauchySum, im_sum, Function.comp_apply, inv_real_sub_lowerPole_im,
    Finset.sum_neg_distrib, neg_neg]
  exact Finset.abs_sum_le_sum_abs _ _

/-- Reflection of all poles into one half-plane dominates the real-axis norm. -/
theorem norm_cauchySum_le_lowerPole {ι : Type*} [Fintype ι]
    (poles : ι → ℂ) (x : ℝ) :
    ‖cauchySum poles x‖ ≤ ‖cauchySum (lowerPole ∘ poles) x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, normSq_apply, cauchySum_lowerPole_re]
  have h := abs_cauchySum_im_le poles x
  have hsq := mul_self_le_mul_self (abs_nonneg (cauchySum poles x).im) h
  nlinarith [sq_abs (cauchySum poles x).im]

theorem levelTransform_denominator_ne_zero {w : ℂ} {y : ℝ}
    (hw : w.im ≤ 0) (hy : 0 < y) : w - (y : ℂ) * I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
    mul_zero, add_zero, zero_im] at hi
  linarith

theorem levelTransform_re (w : ℂ) (y : ℝ) :
    (levelTransform y w).re =
      (normSq w - y * w.im) / normSq (w - (y : ℂ) * I) := by
  simp only [levelTransform, div_re, sub_re, mul_re, ofReal_re, I_re,
    mul_zero, ofReal_im, I_im, mul_one, sub_zero, sub_im, mul_im, add_zero]
  rw [← add_div]
  congr 1
  simp only [normSq_apply]
  ring

theorem levelTransform_re_nonneg {w : ℂ} {y : ℝ}
    (hw : w.im ≤ 0) (hy : 0 ≤ y) : 0 ≤ (levelTransform y w).re := by
  rw [levelTransform_re]
  exact div_nonneg (sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos hy hw).trans
    (normSq_nonneg w))) (normSq_nonneg _)

theorem norm_le_levelTransform_denominator {w : ℂ} {y : ℝ}
    (hw : w.im ≤ 0) (hy : 0 ≤ y) : ‖w‖ ≤ ‖w - (y : ℂ) * I‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, normSq_apply, sub_re, mul_re, ofReal_re, I_re,
    mul_zero, ofReal_im, I_im, mul_one, sub_zero, sub_im, mul_im, add_zero]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hy hw]

theorem norm_levelTransform_le_one {w : ℂ} {y : ℝ}
    (hw : w.im ≤ 0) (hy : 0 ≤ y) : ‖levelTransform y w‖ ≤ 1 := by
  rw [levelTransform, norm_div]
  exact div_le_one_of_le₀ (norm_le_levelTransform_denominator hw hy) (norm_nonneg _)

theorem levelTransform_re_le_one {w : ℂ} {y : ℝ}
    (hw : w.im ≤ 0) (hy : 0 ≤ y) : (levelTransform y w).re ≤ 1 :=
  (re_le_norm _).trans (norm_levelTransform_le_one hw hy)

/-- The real part of the transform detects values above the level with factor two. -/
theorem half_le_levelTransform_re_iff {w : ℂ} {y : ℝ}
    (hw : w.im ≤ 0) (hy : 0 < y) :
    1 / 2 ≤ (levelTransform y w).re ↔ y ≤ ‖w‖ := by
  have hd : 0 < normSq (w - (y : ℂ) * I) :=
    normSq_pos.mpr (levelTransform_denominator_ne_zero hw hy)
  rw [levelTransform_re, le_div_iff₀ hd]
  have hyw : y ≤ ‖w‖ ↔ y ^ 2 ≤ normSq w := by
    rw [← Complex.sq_norm]
    exact (sq_le_sq₀ hy.le (norm_nonneg _)).symm
  rw [hyw]
  simp only [normSq_apply, sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im,
    I_im, mul_one, sub_zero, sub_im, mul_im, add_zero]
  constructor <;> intro h <;> nlinarith

theorem levelTransform_denominator_norm_ge {w : ℂ} {y : ℝ}
    (hw : w.im ≤ 0) : y ≤ ‖w - (y : ℂ) * I‖ := by
  have h := neg_le_abs (w - (y : ℂ) * I).im
  have hn := abs_im_le_norm (w - (y : ℂ) * I)
  simp only [sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
    mul_zero, add_zero] at h hn
  linarith

theorem norm_levelTransform_le_div {w : ℂ} {y : ℝ}
    (hw : w.im ≤ 0) (hy : 0 < y) : ‖levelTransform y w‖ ≤ ‖w‖ / y := by
  rw [levelTransform, norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hy
    (levelTransform_denominator_norm_ge hw)

theorem sub_pole_ne_zero {z p : ℂ} (hz : 0 < z.im) (hp : p.im ≤ 0) : z - p ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [sub_im, zero_im] at this
  linarith

theorem cauchySum_im_nonpos {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} (hp : ∀ i, (poles i).im ≤ 0) {z : ℂ} (hz : 0 ≤ z.im) :
    (cauchySum poles z).im ≤ 0 := by
  simp only [cauchySum, im_sum]
  apply Finset.sum_nonpos
  intro i _
  rw [inv_im]
  exact div_nonpos_of_nonpos_of_nonneg (by simp only [sub_im]; linarith [hp i])
    (normSq_nonneg _)

theorem norm_cauchySum_le {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} (hp : ∀ i, (poles i).im ≤ 0) {z : ℂ} (hz : 0 < z.im) :
    ‖cauchySum poles z‖ ≤ Fintype.card ι / z.im := by
  calc
    ‖cauchySum poles z‖ ≤ ∑ i, ‖(z - poles i)⁻¹‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (z.im)⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_inv]
      apply inv_anti₀ hz
      have h := im_le_norm (z - poles i)
      simp only [sub_im] at h
      linarith [hp i]
    _ = _ := by simp [div_eq_mul_inv]

theorem differentiableAt_cauchySum {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} (hp : ∀ i, (poles i).im ≤ 0) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (cauchySum poles) z := by
  apply DifferentiableAt.fun_sum
  intro i _
  exact (differentiableAt_id.sub_const _).inv (sub_pole_ne_zero hz (hp i))

theorem differentiableAt_transformed_cauchySum {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} (hp : ∀ i, (poles i).im ≤ 0) {z : ℂ} (hz : 0 < z.im)
    {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℂ (fun z ↦ levelTransform y (cauchySum poles z)) z := by
  have hf := differentiableAt_cauchySum hp hz
  exact hf.div (hf.sub_const _) (levelTransform_denominator_ne_zero
    (cauchySum_im_nonpos hp hz.le) hy)

theorem transformed_cauchySum_re_nonneg {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} (hp : ∀ i, (poles i).im ≤ 0) {z : ℂ} (hz : 0 ≤ z.im)
    {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ (levelTransform y (cauchySum poles z)).re :=
  levelTransform_re_nonneg (cauchySum_im_nonpos hp hz) hy

theorem transformed_cauchySum_re_le {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} (hp : ∀ i, (poles i).im ≤ 0) {z : ℂ} (hz : 0 < z.im)
    {y : ℝ} (hy : 0 < y) :
    (levelTransform y (cauchySum poles z)).re ≤ Fintype.card ι / (y * z.im) := by
  calc
    _ ≤ ‖levelTransform y (cauchySum poles z)‖ := re_le_norm _
    _ ≤ ‖cauchySum poles z‖ / y :=
      norm_levelTransform_le_div (cauchySum_im_nonpos hp hz.le) hy
    _ ≤ (Fintype.card ι / z.im) / y :=
      div_le_div_of_nonneg_right (norm_cauchySum_le hp hz) hy.le
    _ = _ := by ring

/-- A closed disk strictly above the real axis contains no pole of the transform. -/
theorem diffContOnCl_transformed_cauchySum {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} (hp : ∀ i, (poles i).im ≤ 0) {c : ℂ} {R : ℝ}
    (hR : |R| < c.im) {y : ℝ} (hy : 0 < y) :
    DiffContOnCl ℂ (fun z ↦ levelTransform y (cauchySum poles z)) (ball c |R|) := by
  apply DifferentiableOn.diffContOnCl
  intro z hz
  apply (differentiableAt_transformed_cauchySum hp ?_ hy).differentiableWithinAt
  have hd := closure_ball_subset_closedBall hz
  have hi := abs_im_le_norm (z - c)
  have hn := neg_le_abs (z - c).im
  rw [mem_closedBall, dist_eq_norm] at hd
  simp only [sub_im] at hi hn
  linarith

/-- The transformed Cauchy sum satisfies the complex mean-value identity. -/
theorem circleAverage_transformed_cauchySum {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} (hp : ∀ i, (poles i).im ≤ 0) {c : ℂ} {R : ℝ}
    (hR : |R| < c.im) {y : ℝ} (hy : 0 < y) :
    Real.circleAverage (fun z ↦ levelTransform y (cauchySum poles z)) c R =
      levelTransform y (cauchySum poles c) :=
  (diffContOnCl_transformed_cauchySum hp hR hy).circleAverage

/-- A circle mean multiplied by its height is bounded uniformly in the circle. -/
theorem circleAverage_transformed_cauchySum_re_le {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} (hp : ∀ i, (poles i).im ≤ 0) {c : ℂ} {R : ℝ}
    (hR : |R| < c.im) {y : ℝ} (hy : 0 < y) :
    (Real.circleAverage (fun z ↦ levelTransform y (cauchySum poles z)) c R).re ≤
      Fintype.card ι / (y * c.im) := by
  rw [circleAverage_transformed_cauchySum hp hR hy]
  exact transformed_cauchySum_re_le hp ((abs_nonneg R).trans_lt hR) hy

/-- Far from a bounded family of poles, a Cauchy sum decays inversely with distance. -/
theorem norm_cauchySum_le_of_pole_bound {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} {R : ℝ} (hR : 0 < R) (hp : ∀ i, ‖poles i‖ ≤ R / 2)
    {z : ℂ} (hz : R ≤ ‖z‖) :
    ‖cauchySum poles z‖ ≤ 2 * Fintype.card ι / R := by
  calc
    ‖cauchySum poles z‖ ≤ ∑ i, ‖(z - poles i)⁻¹‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, 2 / R := by
      apply Finset.sum_le_sum
      intro i _
      have hd : R / 2 ≤ ‖z - poles i‖ := by
        have ht := norm_le_norm_sub_add z (poles i)
        linarith [hp i]
      rw [norm_inv, ← one_div]
      calc
        _ ≤ 1 / (R / 2) := div_le_div_of_nonneg_left zero_le_one (by positivity) hd
        _ = _ := by ring
    _ = _ := by simp; ring

theorem norm_transformed_cauchySum_le_of_pole_bound {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} (hp : ∀ i, (poles i).im ≤ 0) {R : ℝ} (hR : 0 < R)
    (hpn : ∀ i, ‖poles i‖ ≤ R / 2) {z : ℂ} (hzi : 0 ≤ z.im) (hzn : R ≤ ‖z‖)
    {y : ℝ} (hy : 0 < y) :
    ‖levelTransform y (cauchySum poles z)‖ ≤ 2 * Fintype.card ι / (R * y) := by
  calc
    _ ≤ ‖cauchySum poles z‖ / y := norm_levelTransform_le_div
      (cauchySum_im_nonpos hp hzi) hy
    _ ≤ (2 * Fintype.card ι / R) / y :=
      div_le_div_of_nonneg_right (norm_cauchySum_le_of_pole_bound hR hpn hzn) hy.le
    _ = _ := by ring

/-- Cauchy--Goursat bounds the lower edge using uniform bounds on the other three edges. -/
theorem norm_integral_lower_edge_le {f : ℂ → ℂ} {R ε C : ℝ} (hR : 0 ≤ R)
    (hf : DifferentiableOn ℂ f
      (Set.Icc (-R) R ×ℂ Set.Icc ε (ε + R)))
    (ht : ∀ x ∈ Set.Icc (-R) R, ‖f ((x : ℂ) + (ε + R : ℝ) * I)‖ ≤ C)
    (hr : ∀ t ∈ Set.Icc ε (ε + R), ‖f ((R : ℂ) + (t : ℂ) * I)‖ ≤ C)
    (hl : ∀ t ∈ Set.Icc ε (ε + R), ‖f ((-R : ℝ) + (t : ℂ) * I)‖ ≤ C) :
    ‖∫ x in -R..R, f ((x : ℂ) + (ε : ℂ) * I)‖ ≤ 4 * R * C := by
  have hrect := integral_boundary_rect_eq_zero_of_differentiableOn f
    ((-R : ℝ) + (ε : ℂ) * I) ((R : ℂ) + (ε + R : ℝ) * I) (by
      simpa only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
        mul_one, sub_self, add_zero, add_im, mul_im, zero_add,
        Set.uIcc_of_le (show -R ≤ R by linarith),
        Set.uIcc_of_le (show ε ≤ ε + R by linarith)] using hf)
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    mul_one, sub_self, add_zero, add_im, mul_im, zero_add] at hrect
  have heq : (∫ x in -R..R, f ((x : ℂ) + (ε : ℂ) * I)) =
      ((∫ x in -R..R, f ((x : ℂ) + (ε + R : ℝ) * I)) -
        I • (∫ t in ε..ε + R, f ((R : ℂ) + (t : ℂ) * I))) +
        I • (∫ t in ε..ε + R, f ((-R : ℝ) + (t : ℂ) * I)) := by
    linear_combination hrect
  have hbtop : ‖∫ x in -R..R, f ((x : ℂ) + (ε + R : ℝ) * I)‖ ≤ 2 * R * C := by
    have hb : ∀ x ∈ Set.uIoc (-R) R,
        ‖f ((x : ℂ) + (ε + R : ℝ) * I)‖ ≤ C := by
      intro x hx
      rw [Set.uIoc_of_le (show -R ≤ R by linarith)] at hx
      exact ht x (Set.Ioc_subset_Icc_self hx)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    simpa only [sub_neg_eq_add, ← two_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * R),
      mul_comm C]
      using this
  have hbright : ‖∫ t in ε..ε + R, f ((R : ℂ) + (t : ℂ) * I)‖ ≤ R * C := by
    have hb : ∀ t ∈ Set.uIoc ε (ε + R), ‖f ((R : ℂ) + (t : ℂ) * I)‖ ≤ C := by
      intro t ht'
      rw [Set.uIoc_of_le (show ε ≤ ε + R by linarith)] at ht'
      exact hr t (Set.Ioc_subset_Icc_self ht')
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    simpa only [add_sub_cancel_left, abs_of_nonneg hR, mul_comm C] using this
  have hbleft : ‖∫ t in ε..ε + R, f ((-R : ℝ) + (t : ℂ) * I)‖ ≤ R * C := by
    have hb : ∀ t ∈ Set.uIoc ε (ε + R), ‖f ((-R : ℝ) + (t : ℂ) * I)‖ ≤ C := by
      intro t ht'
      rw [Set.uIoc_of_le (show ε ≤ ε + R by linarith)] at ht'
      exact hl t (Set.Ioc_subset_Icc_self ht')
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    simpa only [add_sub_cancel_left, abs_of_nonneg hR, mul_comm C] using this
  rw [heq]
  calc
    _ ≤ (‖∫ x in -R..R, f ((x : ℂ) + (ε + R : ℝ) * I)‖ +
        ‖I • (∫ t in ε..ε + R, f ((R : ℂ) + (t : ℂ) * I))‖) +
        ‖I • (∫ t in ε..ε + R, f ((-R : ℝ) + (t : ℂ) * I))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 2 * R * C + R * C + R * C := by
      simpa only [norm_smul, norm_I, one_mul] using add_le_add (add_le_add hbtop hbright) hbleft
    _ = _ := by ring

/-- The transformed sum has uniformly bounded integrals on horizontal segments
    above the real axis once the endpoints enclose twice the pole radii. -/
theorem norm_integral_transformed_cauchySum_le {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} (hp : ∀ i, (poles i).im ≤ 0) {R ε y : ℝ}
    (hR : 0 < R) (hpn : ∀ i, ‖poles i‖ ≤ R / 2) (hε : 0 < ε) (hy : 0 < y) :
    ‖∫ x in -R..R, levelTransform y (cauchySum poles ((x : ℂ) + (ε : ℂ) * I))‖ ≤
      8 * Fintype.card ι / y := by
  have hbound := norm_integral_lower_edge_le (C := 2 * Fintype.card ι / (R * y))
    (R := R) (ε := ε) hR.le (f := fun z ↦ levelTransform y (cauchySum poles z))
    (by
      intro z hz
      apply (differentiableAt_transformed_cauchySum hp ?_ hy).differentiableWithinAt
      exact hε.trans_le hz.2.1)
    (by
      intro x _
      apply norm_transformed_cauchySum_le_of_pole_bound hp hR hpn
      · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
          mul_zero, add_zero, zero_add]
        positivity
      · have hn := im_le_norm ((x : ℂ) + (ε + R : ℝ) * I)
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
          mul_zero, add_zero, zero_add] at hn
        linarith
      · exact hy)
    (by
      intro t ht
      apply norm_transformed_cauchySum_le_of_pole_bound hp hR hpn
      · simpa using (hε.trans_le ht.1).le
      · simpa using re_le_norm ((R : ℂ) + (t : ℂ) * I)
      · exact hy)
    (by
      intro t ht
      apply norm_transformed_cauchySum_le_of_pole_bound hp hR hpn
      · simpa using (hε.trans_le ht.1).le
      · have hn := (neg_le_abs ((-R : ℝ) + (t : ℂ) * I).re).trans
          (abs_re_le_norm ((-R : ℝ) + (t : ℂ) * I))
        simpa using hn
      · exact hy)
  convert hbound using 1
  field_simp [hR.ne', hy.ne']
  ring

theorem continuous_transformed_cauchySum_horizontal {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} (hp : ∀ i, (poles i).im ≤ 0) {ε y : ℝ}
    (hε : 0 < ε) (hy : 0 < y) :
    Continuous (fun x : ℝ ↦ levelTransform y (cauchySum poles ((x : ℂ) + (ε : ℂ) * I))) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (differentiableAt_transformed_cauchySum hp (by simpa using hε) hy).continuousAt.comp
  fun_prop

/-- A nonnegative real part allows restriction to any smaller horizontal interval. -/
theorem integral_re_transformed_cauchySum_le {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} (hp : ∀ i, (poles i).im ≤ 0) {A R ε y : ℝ}
    (hA : 0 ≤ A) (hAR : A ≤ R) (hR : 0 < R)
    (hpn : ∀ i, ‖poles i‖ ≤ R / 2) (hε : 0 < ε) (hy : 0 < y) :
    (∫ x in -A..A,
      (levelTransform y (cauchySum poles ((x : ℂ) + (ε : ℂ) * I))).re) ≤
      8 * Fintype.card ι / y := by
  have hc := continuous_transformed_cauchySum_horizontal hp hε hy
  calc
    _ ≤ ∫ x in -R..R,
        (levelTransform y (cauchySum poles ((x : ℂ) + (ε : ℂ) * I))).re := by
      apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) hAR
      · exact Filter.Eventually.of_forall (fun x ↦
          transformed_cauchySum_re_nonneg hp (by simpa using hε.le) hy.le)
      · exact (Complex.continuous_re.comp hc).intervalIntegrable _ _
    _ = (∫ x in -R..R,
        levelTransform y (cauchySum poles ((x : ℂ) + (ε : ℂ) * I))).re :=
      Complex.reCLM.intervalIntegral_comp_comm (hc.intervalIntegrable _ _)
    _ ≤ ‖∫ x in -R..R,
        levelTransform y (cauchySum poles ((x : ℂ) + (ε : ℂ) * I))‖ := re_le_norm _
    _ ≤ _ := norm_integral_transformed_cauchySum_le hp hR hpn hε hy

@[fun_prop] theorem measurable_cauchySum {ι : Type*} [Fintype ι] (poles : ι → ℂ) :
    Measurable (cauchySum poles) := by
  unfold cauchySum
  fun_prop

@[fun_prop] theorem measurable_levelTransform (y : ℝ) : Measurable (levelTransform y) := by
  unfold levelTransform
  fun_prop

theorem continuousAt_cauchySum {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} {z : ℂ} (hz : ∀ i, z ≠ poles i) :
    ContinuousAt (cauchySum poles) z := by
  have hi : ∀ i, ContinuousAt (fun z : ℂ ↦ (z - poles i)⁻¹) z := fun i ↦
    (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr (hz i))
  unfold cauchySum
  fun_prop

theorem continuousAt_levelTransform {w : ℂ} {y : ℝ}
    (hw : w.im ≤ 0) (hy : 0 < y) : ContinuousAt (levelTransform y) w :=
  continuousAt_id.div (continuousAt_id.sub continuousAt_const)
    (levelTransform_denominator_ne_zero hw hy)

/-- A bounded measurable nonnegative function obeys the half-level Markov bound
    on each finite interval. -/
theorem measure_half_level_le_of_integral_le {g : ℝ → ℝ} {A B : ℝ}
    (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (hA : 0 ≤ A) (hI : (∫ x in -A..A, g x) ≤ B) :
    (volume.restrict (Set.Ioc (-A) A)).real {x | 1 / 2 ≤ g x} ≤ 2 * B := by
  have hint : Integrable g (volume.restrict (Set.Ioc (-A) A)) :=
    (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
      (Eventually.of_forall (fun x ↦ by simpa [Real.norm_eq_abs, abs_of_nonneg (hg0 x)] using hg1 x))
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := volume.restrict (Set.Ioc (-A) A)) (Eventually.of_forall hg0) hint (1 / 2)
  rw [intervalIntegral.integral_of_le (show -A ≤ A by linarith)] at hI
  linarith

/-- Boundary integrals are obtained from horizontal integrals by dominated convergence.
    The exceptional set of real parts of the finitely many poles has measure zero. -/
theorem integral_re_transformed_cauchySum_boundary_le {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} (hp : ∀ i, (poles i).im ≤ 0) {A R y : ℝ}
    (hA : 0 ≤ A) (hAR : A ≤ R) (hR : 0 < R)
    (hpn : ∀ i, ‖poles i‖ ≤ R / 2) (hy : 0 < y) :
    (∫ x in -A..A, (levelTransform y (cauchySum poles (x : ℂ))).re) ≤
      8 * Fintype.card ι / y := by
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n ↦ by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have haep : ∀ᵐ x : ℝ, ∀ i, x ≠ (poles i).re :=
    ae_all_iff.mpr (fun i ↦ volume.ae_ne (poles i).re)
  have hlim : Tendsto (fun n ↦ ∫ x in -A..A,
      (levelTransform y (cauchySum poles ((x : ℂ) + (ε n : ℂ) * I))).re) atTop
      (𝓝 (∫ x in -A..A, (levelTransform y (cauchySum poles (x : ℂ))).re)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ 1)
    · exact Eventually.of_forall (fun n ↦ (Complex.continuous_re.comp
        (continuous_transformed_cauchySum_horizontal hp (hε n) hy)).aestronglyMeasurable)
    · refine Eventually.of_forall (fun n ↦ Eventually.of_forall (fun x _ ↦ ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg
        (transformed_cauchySum_re_nonneg hp (by simpa using (hε n).le) hy.le)]
      exact levelTransform_re_le_one (cauchySum_im_nonpos hp (by simpa using (hε n).le)) hy.le
    · exact intervalIntegrable_const
    · filter_upwards [haep] with x hx
      intro _
      have hxp : ∀ i, (x : ℂ) ≠ poles i := fun i h ↦ hx i (by
        have := congrArg Complex.re h
        simpa only [ofReal_re] using this)
      have hc := (continuousAt_levelTransform (cauchySum_im_nonpos hp (by simp)) hy).comp
        (continuousAt_cauchySum hxp)
      have hz : Tendsto (fun n ↦ (x : ℂ) + (ε n : ℂ) * I) atTop (𝓝 (x : ℂ)) := by
        simpa only [ofReal_zero, zero_mul, add_zero, Function.comp_apply] using
          tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto 0 |>.comp hεlim).mul_const I)
      exact Complex.continuous_re.continuousAt.tendsto.comp (hc.tendsto.comp hz)
  exact le_of_tendsto' hlim (fun n ↦ integral_re_transformed_cauchySum_le
    hp hA hAR hR hpn (hε n) hy)

/-- The real part of the transform has a uniform boundary integral on every finite interval. -/
theorem integral_re_transformed_cauchySum_boundary_le_card {ι : Type*} [Fintype ι]
    {poles : ι → ℂ} (hp : ∀ i, (poles i).im ≤ 0) {A y : ℝ}
    (hA : 0 ≤ A) (hy : 0 < y) :
    (∫ x in -A..A, (levelTransform y (cauchySum poles (x : ℂ))).re) ≤
      8 * Fintype.card ι / y := by
  let S : ℝ := ∑ i, ‖poles i‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ ↦ norm_nonneg _)
  have hpS : ∀ i, ‖poles i‖ ≤ S := fun i ↦
    Finset.single_le_sum (fun j _ ↦ norm_nonneg (poles j)) (Finset.mem_univ i)
  exact integral_re_transformed_cauchySum_boundary_le hp hA
    (R := 2 * (A + 1 + S)) (by linarith) (by positivity)
    (fun i ↦ by linarith [hpS i]) hy

/-- Finite Cauchy sums satisfy a weak first-order estimate, with multiplicities,
    uniformly on every bounded interval. -/
theorem measureReal_cauchySum_levelset_le {ι : Type*} [Fintype ι]
    (poles : ι → ℂ) {A y : ℝ} (hA : 0 ≤ A) (hy : 0 < y) :
    (volume.restrict (Set.Ioc (-A) A)).real
      {x : ℝ | y ≤ ‖cauchySum poles (x : ℂ)‖} ≤ 16 * Fintype.card ι / y := by
  let q : ι → ℂ := lowerPole ∘ poles
  have hq : ∀ i, (q i).im ≤ 0 := fun i ↦ neg_nonpos.mpr (abs_nonneg _)
  let g : ℝ → ℝ := fun x ↦ (levelTransform y (cauchySum q (x : ℂ))).re
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hg0 : ∀ x, 0 ≤ g x := fun x ↦
    transformed_cauchySum_re_nonneg hq (by simp) hy.le
  have hg1 : ∀ x, g x ≤ 1 := fun x ↦
    levelTransform_re_le_one (cauchySum_im_nonpos hq (by simp)) hy.le
  have hm := measure_half_level_le_of_integral_le hg hg0 hg1 hA
    (integral_re_transformed_cauchySum_boundary_le_card hq hA hy)
  have hsub : {x : ℝ | y ≤ ‖cauchySum poles (x : ℂ)‖} ⊆ {x | 1 / 2 ≤ g x} := by
    intro x hx
    exact (half_le_levelTransform_re_iff (cauchySum_im_nonpos hq (by simp)) hy).mpr
      (hx.trans (norm_cauchySum_le_lowerPole poles x))
  calc
    _ ≤ (volume.restrict (Set.Ioc (-A) A)).real {x | 1 / 2 ≤ g x} := measureReal_mono hsub
    _ ≤ 2 * (8 * Fintype.card ι / y) := hm
    _ = _ := by ring

/-- The extended-real form of the finite-window weak Cauchy estimate. -/
theorem measure_cauchySum_levelset_le {ι : Type*} [Fintype ι]
    (poles : ι → ℂ) {A y : ℝ} (hA : 0 ≤ A) (hy : 0 < y) :
    (volume.restrict (Set.Ioc (-A) A))
      {x : ℝ | y ≤ ‖cauchySum poles (x : ℂ)‖} ≤
      ENNReal.ofReal (16 * Fintype.card ι / y) := by
  have h := measureReal_cauchySum_levelset_le poles hA hy
  rw [measureReal_def] at h
  simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _)] using ENNReal.ofReal_le_ofReal h

/-- A finite Cauchy sum has a global weak first-order bound with universal constant sixteen. -/
theorem measure_cauchySum_levelset_global_le {ι : Type*} [Fintype ι]
    (poles : ι → ℂ) {y : ℝ} (hy : 0 < y) :
    volume {x : ℝ | y ≤ ‖cauchySum poles (x : ℂ)‖} ≤
      ENNReal.ofReal (16 * Fintype.card ι / y) := by
  let s : ℕ → Set ℝ := fun n ↦
    {x : ℝ | y ≤ ‖cauchySum poles (x : ℂ)‖} ∩ Set.Ioc (-(n : ℝ)) n
  have hs : Monotone s := by
    intro m n hmn x hx
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact ⟨hx.1, by constructor <;> linarith [hx.2.1, hx.2.2]⟩
  have heq : {x : ℝ | y ≤ ‖cauchySum poles (x : ℂ)‖} = ⋃ n, s n := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      exact Set.mem_iUnion.mpr ⟨n, hx, (abs_lt.mp hn).1, (abs_lt.mp hn).2.le⟩
    · intro hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact hn.1
  rw [heq, hs.measure_iUnion]
  apply iSup_le
  intro n
  simpa only [Measure.restrict_apply' measurableSet_Ioc] using
    measure_cauchySum_levelset_le poles (A := (n : ℝ)) (Nat.cast_nonneg _) hy

/-- Removing the real poles, or restricting to any measurable window, preserves
    the same weak bound. -/
theorem measure_cauchySum_levelset_on_le {ι : Type*} [Fintype ι]
    (poles : ι → ℂ) (s : Set ℝ) {y : ℝ} (hy : 0 < y) :
    volume {x : ℝ | x ∈ s ∧ y < ‖cauchySum poles (x : ℂ)‖} ≤
      ENNReal.ofReal (16 * Fintype.card ι / y) := by
  exact (measure_mono (fun _ hx ↦ hx.2.le)).trans
    (measure_cauchySum_levelset_global_le poles hy)

/-- The Cauchy sum of a multiset of poles. -/
def multisetCauchySum (poles : Multiset ℂ) (z : ℂ) : ℂ :=
  (poles.map (fun p ↦ (z - p)⁻¹)).sum

theorem cauchySum_toList_get (poles : Multiset ℂ) (z : ℂ) :
    cauchySum poles.toList.get z = multisetCauchySum poles z := by
  unfold cauchySum
  rw [← Fin.sum_ofFn]
  change (List.ofFn ((fun p : ℂ ↦ (z - p)⁻¹) ∘ poles.toList.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get, Multiset.sum_map_toList]
  rfl

/-- The weak Cauchy estimate for an arbitrary complex multiset, counting every pole
    with its multiplicity. -/
theorem measure_multisetCauchySum_levelset_le (poles : Multiset ℂ)
    {y : ℝ} (hy : 0 < y) :
    volume {x : ℝ | y ≤ ‖multisetCauchySum poles (x : ℂ)‖} ≤
      ENNReal.ofReal (16 * poles.card / y) := by
  simpa only [cauchySum_toList_get, Fintype.card_fin, Multiset.length_toList] using
    measure_cauchySum_levelset_global_le poles.toList.get hy

/-- The strict-level form on an arbitrary set, including the complement of the real poles. -/
theorem measure_multisetCauchySum_levelset_on_le (poles : Multiset ℂ) (s : Set ℝ)
    {y : ℝ} (hy : 0 < y) :
    volume {x : ℝ | x ∈ s ∧ y < ‖multisetCauchySum poles (x : ℂ)‖} ≤
      ENNReal.ofReal (16 * poles.card / y) := by
  exact (measure_mono (fun _ hx ↦ hx.2.le)).trans
    (measure_multisetCauchySum_levelset_le poles hy)

end CauchySums
end Erdos522

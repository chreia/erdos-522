/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Basic.ZeroCount
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantitative separation and barriers at regular roots

A quadratic Taylor-remainder bound controls the separation of regular roots
and the modulus on localization circles. A remainder estimate between distinct
roots yields disjoint localization balls with a common radius.
-/

noncomputable section
namespace Erdos522

/-- The second-order remainder bound forces two distinct regular roots apart.
This division-free form also covers a zero second-derivative bound. -/
theorem regular_root_separation_mul (P : Polynomial ℂ) {α β : ℂ} {M d₀ : ℝ}
    (hα : P.eval α = 0) (hβ : P.eval β = 0) (hne : α ≠ β)
    (hderiv : d₀ ≤ ‖P.derivative.eval α‖)
    (hrem : ‖P.eval β - P.eval α - P.derivative.eval α * (β - α)‖ ≤
      M / 2 * ‖β - α‖ ^ 2) :
    2 * d₀ ≤ M * ‖β - α‖ := by
  have hdist : 0 < ‖β - α‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hlin : ‖P.derivative.eval α‖ * ‖β - α‖ ≤ M / 2 * ‖β - α‖ ^ 2 := by
    simpa only [hα, hβ, sub_self, zero_sub, norm_neg, norm_mul] using hrem
  have hsmall := mul_le_mul_of_nonneg_right hderiv hdist.le
  nlinarith

/-- Usual quotient form of regular-root separation. -/
theorem regular_root_separation (P : Polynomial ℂ) {α β : ℂ} {M d₀ : ℝ}
    (hM : 0 < M) (hα : P.eval α = 0) (hβ : P.eval β = 0) (hne : α ≠ β)
    (hderiv : d₀ ≤ ‖P.derivative.eval α‖)
    (hrem : ‖P.eval β - P.eval α - P.derivative.eval α * (β - α)‖ ≤
      M / 2 * ‖β - α‖ ^ 2) :
    2 * d₀ / M ≤ dist α β := by
  rw [div_le_iff₀ hM, dist_eq_norm, norm_sub_rev]
  nlinarith [regular_root_separation_mul P hα hβ hne hderiv hrem]

/-- Boundary barrier at radius `2a/d₀`: the quadratic remainder consumes at
most `a/2`, so the polynomial has modulus at least `3a/2`. -/
theorem regular_root_boundary_barrier (P : Polynomial ℂ) {α z : ℂ} {M d₀ a : ℝ}
    (ha : 0 ≤ a) (hd : 0 < d₀) (hα : P.eval α = 0)
    (hderiv : d₀ ≤ ‖P.derivative.eval α‖) (hbudget : 4 * M * a ≤ d₀ ^ 2)
    (hradius : ‖z - α‖ = 2 * a / d₀)
    (hrem : ‖P.eval z - P.eval α - P.derivative.eval α * (z - α)‖ ≤
      M / 2 * ‖z - α‖ ^ 2) :
    3 * a / 2 ≤ ‖P.eval z‖ := by
  have hdist : ‖z - α‖ * d₀ = 2 * a := (eq_div_iff hd.ne').mp hradius
  have hlin : 2 * a ≤ ‖P.derivative.eval α * (z - α)‖ := by
    rw [norm_mul]
    nlinarith [mul_le_mul_of_nonneg_right hderiv (norm_nonneg (z - α))]
  have hquad : M / 2 * ‖z - α‖ ^ 2 ≤ a / 2 := by
    have hb := mul_le_mul_of_nonneg_right hbudget ha
    have he : d₀ ^ 2 * (M / 2 * ‖z - α‖ ^ 2) = 2 * M * a ^ 2 := by
      calc
        _ = M / 2 * (‖z - α‖ * d₀) ^ 2 := by ring
        _ = 2 * M * a ^ 2 := by rw [hdist]; ring
    nlinarith [sq_pos_of_pos hd]
  have hreverse : ‖P.derivative.eval α * (z - α)‖ ≤
      ‖P.eval z‖ + ‖P.eval z - P.derivative.eval α * (z - α)‖ := by
    calc
      _ = ‖P.eval z - (P.eval z - P.derivative.eval α * (z - α))‖ := by
        congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  simp only [hα, sub_zero] at hrem
  linarith

/-- Under the common-domain remainder hypothesis, the prescribed localization
balls are disjoint. No assumption of simple roots is made in this statement. -/
theorem regular_root_balls_disjoint (P : Polynomial ℂ) {α β : ℂ} {M d₀ a : ℝ}
    (hd : 0 < d₀) (hα : P.eval α = 0) (hβ : P.eval β = 0)
    (hne : α ≠ β) (hderiv : d₀ ≤ ‖P.derivative.eval α‖)
    (hbudget : 4 * M * a ≤ d₀ ^ 2)
    (hrem : ‖P.eval β - P.eval α - P.derivative.eval α * (β - α)‖ ≤
      M / 2 * ‖β - α‖ ^ 2) :
    Disjoint (Metric.ball α (2 * a / d₀)) (Metric.ball β (2 * a / d₀)) := by
  apply Metric.ball_disjoint_ball
  have hsep := regular_root_separation_mul P hα hβ hne hderiv hrem
  have hdist : 0 < ‖β - α‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hM : 0 < M := by nlinarith
  rw [dist_eq_norm, norm_sub_rev]
  have hquot : 2 * a / d₀ * d₀ = 2 * a := div_mul_cancel₀ _ hd.ne'
  have hscaled := congrArg (fun x : ℝ ↦ M * x) hquot
  have hMr : M * (2 * a / d₀ + 2 * a / d₀) ≤ d₀ := by
    apply (mul_le_mul_iff_left₀ hd).mp
    nlinarith
  apply (mul_le_mul_iff_right₀ hM).mp
  linarith

/-- A uniform second-derivative bound on a convex domain gives the quadratic
Taylor-remainder bound, including its factor `1/2`. -/
theorem polynomial_taylor_remainder (P : Polynomial ℂ) {D : Set ℂ} {α β : ℂ} {M : ℝ}
    (hD : Convex ℝ D) (hα : α ∈ D) (hβ : β ∈ D)
    (hbound : ∀ z ∈ D, ‖P.derivative.derivative.eval z‖ ≤ M) :
    ‖P.eval β - P.eval α - P.derivative.eval α * (β - α)‖ ≤
      M / 2 * ‖β - α‖ ^ 2 := by
  let line : ℝ → ℂ := AffineMap.lineMap α β
  let f : ℝ → ℂ := fun t ↦ P.eval (line t) - P.eval α -
    t • ((β - α) * P.derivative.eval α)
  let f' : ℝ → ℂ := fun t ↦ (β - α) *
    (P.derivative.eval (line t) - P.derivative.eval α)
  have hd : ∀ t, HasDerivAt f (f' t) t := by
    intro t
    have hc := ((P.hasFDerivAt (line t)).restrictScalars ℝ).comp_hasDerivAt t
      (show HasDerivAt line (β - α) t from AffineMap.hasDerivAt_lineMap)
    have ht := (hasDerivAt_id t).smul_const ((β - α) * P.derivative.eval α)
    convert (hc.sub_const (P.eval α)).sub ht using 1 <;>
      first | rfl | simp [f', ContinuousLinearMap.smulRight_apply, mul_sub]
  have hf : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    (show Continuous f from continuous_iff_continuousAt.mpr (fun t ↦ (hd t).continuousAt)).continuousOn
  have hline : ∀ t ∈ Set.Icc (0 : ℝ) 1, line t ∈ D := hD.mapsTo_lineMap hα hβ
  have hfp : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖f' t‖ ≤ (M * ‖β - α‖ ^ 2) * t := by
    intro t ht
    have hb := hD.norm_image_sub_le_of_norm_deriv_le
      (fun z _ ↦ P.derivative.differentiableAt)
      (fun z hz ↦ by simpa only [Polynomial.deriv] using hbound z hz)
      hα (hline t ⟨ht.1, ht.2.le⟩)
    have hn : ‖line t - α‖ = t * ‖β - α‖ := by
      simp [line, AffineMap.lineMap_apply_module', Real.norm_eq_abs,
        abs_of_nonneg ht.1]
    rw [hn] at hb
    calc
      ‖f' t‖ = ‖β - α‖ * ‖P.derivative.eval (line t) - P.derivative.eval α‖ := by
        simp [f']
      _ ≤ ‖β - α‖ * (M * (t * ‖β - α‖)) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = (M * ‖β - α‖ ^ 2) * t := by ring
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ (M * ‖β - α‖ ^ 2 / 2) * t ^ 2)
      ((M * ‖β - α‖ ^ 2) * t) t := by
    intro t
    convert ((hasDerivAt_id t).pow 2).const_mul (M * ‖β - α‖ ^ 2 / 2) using 1 <;>
      first | rfl | (norm_num; ring)
  have ha : ‖f 0‖ ≤ (M * ‖β - α‖ ^ 2 / 2) * (0 : ℝ) ^ 2 := by simp [f, line]
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary hf
    (fun t _ ↦ (hd t).hasDerivWithinAt) ha hB hfp (show (1 : ℝ) ∈ Set.Icc 0 1 by simp)
  simpa [f, line, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h

/-- Regular roots in a common convex domain obey the separation estimate. -/
theorem regular_root_separation_on_convex (P : Polynomial ℂ) {D : Set ℂ}
    {α β : ℂ} {M d₀ : ℝ} (hD : Convex ℝ D) (hM : 0 < M)
    (hαD : α ∈ D) (hβD : β ∈ D) (hα : P.eval α = 0) (hβ : P.eval β = 0)
    (hne : α ≠ β) (hderiv : d₀ ≤ ‖P.derivative.eval α‖)
    (hbound : ∀ z ∈ D, ‖P.derivative.derivative.eval z‖ ≤ M) :
    2 * d₀ / M ≤ dist α β :=
  regular_root_separation P hM hα hβ hne hderiv
    (polynomial_taylor_remainder P hD hαD hβD hbound)

/-- A nonvanishing derivative makes the root's algebraic multiplicity one. -/
theorem regular_root_multiplicity_one (P : Polynomial ℂ) {α : ℂ}
    (hα : P.eval α = 0) (hd : P.derivative.eval α ≠ 0) :
    P.rootMultiplicity α = 1 := by
  have hP : P ≠ 0 := by
    intro hp
    simp [hp] at hd
  have hpos := (Polynomial.rootMultiplicity_pos hP).mpr hα
  have hle : P.rootMultiplicity α ≤ 1 := by
    by_contra h
    have hr := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hP).mp (Nat.lt_of_not_ge h)
    exact hd hr.2
  omega

/-- A Taylor-remainder budget excludes every other root in the closed localization disk. -/
theorem regular_root_unique_in_closedBall (P : Polynomial ℂ) {α z : ℂ} {M d₀ a : ℝ}
    (hd : 0 < d₀) (hα : P.eval α = 0) (hz : P.eval z = 0)
    (hderiv : d₀ ≤ ‖P.derivative.eval α‖) (hbudget : 4 * M * a ≤ d₀ ^ 2)
    (hradius : ‖z - α‖ ≤ 2 * a / d₀)
    (hrem : ‖P.eval z - P.eval α - P.derivative.eval α * (z - α)‖ ≤
      M / 2 * ‖z - α‖ ^ 2) : z = α := by
  by_contra hne
  have hsep := regular_root_separation_mul P hα hz (Ne.symm hne) hderiv hrem
  have hdist : 0 < ‖z - α‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hM : 0 < M := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hradius hM.le
  have he := congrArg (fun x : ℝ ↦ M * x)
    (div_mul_cancel₀ (2 * a) hd.ne' : 2 * a / d₀ * d₀ = 2 * a)
  have hMs : M * (2 * a / d₀) ≤ d₀ / 2 := by
    apply (mul_le_mul_iff_left₀ hd).mp
    nlinarith
  linarith

/-- The local derivative and second-derivative bounds imply exactly one root,
counted with multiplicity, in the open localization disk. -/
theorem regular_root_count_ball (P : Polynomial ℂ) {α : ℂ} {M d₀ a : ℝ}
    (ha : 0 < a) (hd : 0 < d₀) (hα : P.eval α = 0)
    (hderiv : d₀ ≤ ‖P.derivative.eval α‖) (hbudget : 4 * M * a ≤ d₀ ^ 2)
    (hbound : ∀ z ∈ Metric.closedBall α (2 * a / d₀),
      ‖P.derivative.derivative.eval z‖ ≤ M) :
    zeroCountIn P (Metric.ball α (2 * a / d₀)) = 1 := by
  classical
  have hrad : 0 < 2 * a / d₀ := by positivity
  have hαD : α ∈ Metric.closedBall α (2 * a / d₀) := Metric.mem_closedBall_self hrad.le
  have hdne : P.derivative.eval α ≠ 0 := norm_pos_iff.mp (hd.trans_le hderiv)
  have hP : P ≠ 0 := by intro hp; simp [hp] at hdne
  have hf : P.roots.filter (fun z ↦ z ∈ Metric.ball α (2 * a / d₀)) =
      P.roots.filter (fun z ↦ z = α) := by
    apply Multiset.filter_congr
    intro z hz
    constructor
    · intro hzD
      have hzD' := Metric.ball_subset_closedBall hzD
      exact regular_root_unique_in_closedBall P hd hα
        ((Polynomial.mem_roots hP).mp hz) hderiv hbudget
        (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hzD')
        (polynomial_taylor_remainder P (convex_closedBall α _) hαD hzD' hbound)
    · intro h
      subst z
      exact Metric.mem_ball_self hrad
  simp only [zeroCountIn, hf, Multiset.filter_eq', Multiset.card_replicate,
    Polynomial.count_roots, regular_root_multiplicity_one P hα hdne]

/-- A preconnected sublevel set containing the center cannot cross a circle
on which the function's modulus is at least its sublevel threshold. -/
theorem preconnected_sublevel_subset_ball {f : ℂ → ℂ} {W : Set ℂ} {α : ℂ} {a s : ℝ}
    (hW : IsPreconnected W) (hα : α ∈ W) (hs : 0 < s)
    (hsub : ∀ z ∈ W, ‖f z‖ < a) (hbarrier : ∀ z, ‖z - α‖ = s → a ≤ ‖f z‖) :
    W ⊆ Metric.ball α s := by
  intro z hz
  by_contra h
  have hd : s ≤ ‖z - α‖ := by simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using h
  obtain ⟨v, hv, he⟩ := hW.intermediate_value hα hz
    ((continuous_id.sub continuous_const).norm.continuousOn)
    (show s ∈ Set.Icc ‖α - α‖ ‖z - α‖ by simpa using And.intro hs.le hd)
  exact (hsub v hv).not_ge (hbarrier v he)

/-- The sublevel component at a regular root lies in its localization disk. -/
theorem regular_root_sublevel_component_subset_ball (P : Polynomial ℂ) {α : ℂ}
    {M d₀ a : ℝ} (ha : 0 < a) (hd : 0 < d₀) (hα : P.eval α = 0)
    (hderiv : d₀ ≤ ‖P.derivative.eval α‖) (hbudget : 4 * M * a ≤ d₀ ^ 2)
    (hbound : ∀ z ∈ Metric.closedBall α (2 * a / d₀),
      ‖P.derivative.derivative.eval z‖ ≤ M) :
    connectedComponentIn {z | ‖P.eval z‖ < a} α ⊆ Metric.ball α (2 * a / d₀) := by
  have hrad : 0 < 2 * a / d₀ := by positivity
  apply preconnected_sublevel_subset_ball (f := fun z ↦ P.eval z) isPreconnected_connectedComponentIn
    (mem_connectedComponentIn (by simpa [hα] using ha)) hrad
    (fun z hz ↦ connectedComponentIn_subset {z | ‖P.eval z‖ < a} α hz)
  intro z hz
  have hzD : z ∈ Metric.closedBall α (2 * a / d₀) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz.le
  have hbar := regular_root_boundary_barrier P ha.le hd hα hderiv hbudget hz
    (polynomial_taylor_remainder P (convex_closedBall α _)
      (Metric.mem_closedBall_self hrad.le) hzD hbound)
  linarith

/-- A finite or infinite family of distinct regular roots in one convex domain
has pairwise disjoint localization balls under the common remainder budget. -/
theorem regular_root_family_disjoint {ι : Type*} (P : Polynomial ℂ) (z : ι → ℂ)
    {D : Set ℂ} {M d₀ a : ℝ} (hD : Convex ℝ D) (hd : 0 < d₀)
    (hinj : Function.Injective z) (hzD : ∀ i, z i ∈ D) (hroot : ∀ i, P.eval (z i) = 0)
    (hderiv : ∀ i, d₀ ≤ ‖P.derivative.eval (z i)‖) (hbudget : 4 * M * a ≤ d₀ ^ 2)
    (hbound : ∀ w ∈ D, ‖P.derivative.derivative.eval w‖ ≤ M) :
    Pairwise (fun i j ↦ Disjoint (Metric.ball (z i) (2 * a / d₀))
      (Metric.ball (z j) (2 * a / d₀))) := by
  intro i j hij
  exact regular_root_balls_disjoint P hd (hroot i) (hroot j) (hinj.ne hij)
    (hderiv i) hbudget (polynomial_taylor_remainder P hD (hzD i) (hzD j) hbound)

end Erdos522

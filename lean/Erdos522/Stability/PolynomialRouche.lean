/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Adapted from the circle-integral, argument-principle, topology, affine-homotopy,
and Rouché files in leanprover/hex-roots-mathlib, commit
9bcfb127d85e33c877d3e68d19385b115d7d45b9:
https://github.com/leanprover/hex-roots-mathlib/tree/9bcfb127d85e33c877d3e68d19385b115d7d45b9
-/
/-
Modifications copyright (c) 2026 Sebastien Kawada.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted for the formalization of Erdős Problem #522 by Sebastien Kawada.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Nat
import Erdos522.Basic.ZeroCount
import Erdos522.Stability.RootMatching
import Erdos522.Stability.RootIsolation


/-!
# Polynomial logarithmic derivatives on circles

Partial fractions and circle integrals give the polynomial argument principle.
Root multisets are retained
throughout, so repeated roots contribute with their multiplicity.
-/

open Complex Metric Polynomial Set

namespace Erdos522.PolynomialCircle

noncomputable section

/-- The logarithmic derivative of a complex polynomial is the sum of its
reciprocal linear factors, counted over the root multiset. -/
theorem logDeriv_eq_sum (p : ℂ[X]) {z : ℂ} (hz : p.eval z ≠ 0) :
    p.derivative.eval z / p.eval z =
      (p.roots.map fun a => (z - a)⁻¹).sum := by
  simpa only [one_div] using
    (IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hz

/-- A reciprocal linear factor is circle integrable exactly when its pole is
not on the circle (apart from the degenerate zero-radius case). -/
theorem subInv_circleIntegrable {c a : ℂ} {R : ℝ}
    (ha : a ∉ sphere c |R|) :
    CircleIntegrable (fun z : ℂ => (z - a)⁻¹) c R := by
  exact circleIntegrable_sub_inv_iff.mpr (Or.inr ha)

/-- A pole strictly inside a positive-radius circle contributes `2πi`. -/
theorem integral_subInv_inside {c a : ℂ} {R : ℝ} (ha : a ∈ ball c R) :
    (∮ z in C(c, R), (z - a)⁻¹) = 2 * Real.pi * I :=
  circleIntegral.integral_sub_inv_of_mem_ball ha

/-- A pole outside the closed disc contributes zero. -/
theorem integral_subInv_outside {c a : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (ha : a ∉ closedBall c R) :
    (∮ z in C(c, R), (z - a)⁻¹) = 0 := by
  have hne : ∀ z ∈ closure (ball c R), z - a ≠ 0 := by
    intro z hz hza
    apply ha
    have : z = a := sub_eq_zero.mp hza
    subst z
    exact closure_ball_subset_closedBall hz
  exact ((differentiable_id.diffContOnCl.sub_const a).inv hne).circleIntegral_eq_zero hR

/-- A finite multiset sum of reciprocal linear factors is circle integrable
when none of its poles lies on the circle. -/
private theorem sum_subInv_circleIntegrable {roots : Multiset ℂ}
    {c : ℂ} {R : ℝ} (hroots : ∀ a ∈ roots, a ∉ sphere c |R|) :
    CircleIntegrable (fun z => (roots.map fun a => (z - a)⁻¹).sum) c R := by
  induction roots using Multiset.induction_on with
  | empty =>
      simp only [Multiset.map_zero, Multiset.sum_zero]
      exact circleIntegrable_const 0 c R
  | @cons a roots ih =>
      have ha := subInv_circleIntegrable (hroots a (Multiset.mem_cons_self a roots))
      have htail := ih (fun b hb => hroots b (Multiset.mem_cons_of_mem hb))
      apply (circleIntegrable_congr ?_).mpr (ha.add htail)
      intro z hz
      simp only [Multiset.map_cons, Multiset.sum_cons, Pi.add_apply]

/-- Circle integration commutes with a finite multiset sum of reciprocal
linear factors when none of the poles lies on the circle. -/
theorem integral_sum_subInv {roots : Multiset ℂ} {c : ℂ} {R : ℝ}
    (hroots : ∀ a ∈ roots, a ∉ sphere c |R|) :
    (∮ z in C(c, R), (roots.map fun a => (z - a)⁻¹).sum) =
      (roots.map fun a => ∮ z in C(c, R), (z - a)⁻¹).sum := by
  induction roots using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | @cons a roots ih =>
      have ha := subInv_circleIntegrable (hroots a (Multiset.mem_cons_self a roots))
      have htail : ∀ b ∈ roots, b ∉ sphere c |R| :=
        fun b hb => hroots b (Multiset.mem_cons_of_mem hb)
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [circleIntegral.integral_add ha (sum_subInv_circleIntegrable htail), ih htail]

/-- If a polynomial has no root on a nonnegative-radius circle, then its
logarithmic derivative is circle integrable. -/
theorem logDeriv_circleIntegrable {p : ℂ[X]} (hp : p ≠ 0)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ z ∈ sphere c R, p.eval z ≠ 0) :
    CircleIntegrable (fun z => p.derivative.eval z / p.eval z) c R := by
  let terms : ℂ → ℂ := fun z => (p.roots.map fun a => (z - a)⁻¹).sum
  have hterms : CircleIntegrable terms c R := by
    dsimp only [terms]
    apply sum_subInv_circleIntegrable
    intro a haRoot haSphere
    rw [abs_of_nonneg hR] at haSphere
    exact hboundary a haSphere ((mem_roots hp).mp haRoot)
  apply (circleIntegrable_congr ?_).mpr hterms
  intro z hz
  have hz' : z ∈ sphere c R := by simpa [abs_of_nonneg hR] using hz
  exact logDeriv_eq_sum p (hboundary z hz')

/-- The circle integral of a polynomial logarithmic derivative is the
multiset sum of its reciprocal-factor integrals. -/
theorem integral_logDeriv_eq_sum {p : ℂ[X]} (hp : p ≠ 0)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ z ∈ sphere c R, p.eval z ≠ 0) :
    (∮ z in C(c, R), p.derivative.eval z / p.eval z) =
      (p.roots.map fun a => ∮ z in C(c, R), (z - a)⁻¹).sum := by
  have hroots : ∀ a ∈ p.roots, a ∉ sphere c |R| := by
    intro a haRoot haSphere
    rw [abs_of_nonneg hR] at haSphere
    exact hboundary a haSphere ((mem_roots hp).mp haRoot)
  calc
    (∮ z in C(c, R), p.derivative.eval z / p.eval z) =
        ∮ z in C(c, R), (p.roots.map fun a => (z - a)⁻¹).sum := by
      apply circleIntegral.integral_congr hR
      intro z hz
      exact logDeriv_eq_sum p (hboundary z hz)
    _ = _ := integral_sum_subInv hroots

end

end Erdos522.PolynomialCircle


/-!
# Topology for polynomial argument-principle homotopies

Fixed-circle integrals are continuous in an external parameter, and continuous
discrete-valued functions are constant on real intervals.
-/

open Complex Set

namespace Erdos522.PolynomialCircle

noncomputable section

/-- A fixed-circle integral varies continuously when the integrand restricted
to the parameter-times-circle parametrization is jointly continuous. -/
theorem continuous_circleIntegral {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f : X → ℂ → E}
    (c : ℂ) (R : ℝ)
    (hf : Continuous fun q : X × ℝ => f q.1 (circleMap c R q.2)) :
    Continuous fun x => ∮ z in C(c, R), f x z := by
  simp only [circleIntegral]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  apply Continuous.smul
  · rw [show (fun q : X × ℝ => deriv (circleMap c R) q.2) =
        fun q => circleMap 0 R q.2 * I by funext q; rw [deriv_circleMap]]
    fun_prop
  · exact hf

/-- A fixed-circle integral of a quotient varies continuously if numerator
and denominator are jointly continuous on the parameterized circle and the
denominator never vanishes there. -/
theorem continuous_circleIntegral_div {X : Type*} [TopologicalSpace X]
    {f g : X → ℂ → ℂ} (c : ℂ) (R : ℝ)
    (hf : Continuous fun q : X × ℝ => f q.1 (circleMap c R q.2))
    (hg : Continuous fun q : X × ℝ => g q.1 (circleMap c R q.2))
    (hzero : ∀ q : X × ℝ, g q.1 (circleMap c R q.2) ≠ 0) :
    Continuous fun x => ∮ z in C(c, R), f x z / g x z := by
  apply continuous_circleIntegral c R
  exact hf.div hg hzero

/-- A fixed-circle integral of a quotient varies continuously on a parameter
set when the data are jointly continuous and the denominator is nonzero only
over that set. -/
theorem continuousOn_circleIntegral_div {X : Type*} [TopologicalSpace X]
    {f g : X → ℂ → ℂ} {s : Set X} (c : ℂ) (R : ℝ)
    (hf : ContinuousOn (fun q : X × ℝ => f q.1 (circleMap c R q.2)) (s ×ˢ univ))
    (hg : ContinuousOn (fun q : X × ℝ => g q.1 (circleMap c R q.2)) (s ×ˢ univ))
    (hzero : ∀ x ∈ s, ∀ θ : ℝ, g x (circleMap c R θ) ≠ 0) :
    ContinuousOn (fun x => ∮ z in C(c, R), f x z / g x z) s := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_circleIntegral_div c R
  · simpa only [Function.comp_def] using hf.comp_continuous
      (show Continuous (fun q : s × ℝ => ((q.1 : X), q.2)) by fun_prop)
      (fun q => ⟨q.1.2, mem_univ q.2⟩)
  · simpa only [Function.comp_def] using hg.comp_continuous
      (show Continuous (fun q : s × ℝ => ((q.1 : X), q.2)) by fun_prop)
      (fun q => ⟨q.1.2, mem_univ q.2⟩)
  · exact fun q => hzero q.1.1 q.1.2 q.2

/-- The normalized integral of a quotient varies continuously on a parameter
set under a nonvanishing hypothesis restricted to that set. -/
theorem continuousOn_normalizedCircleIntegral_div {X : Type*} [TopologicalSpace X]
    {f g : X → ℂ → ℂ} {s : Set X} (c : ℂ) (R : ℝ)
    (hf : ContinuousOn (fun q : X × ℝ => f q.1 (circleMap c R q.2)) (s ×ˢ univ))
    (hg : ContinuousOn (fun q : X × ℝ => g q.1 (circleMap c R q.2)) (s ×ˢ univ))
    (hzero : ∀ x ∈ s, ∀ θ : ℝ, g x (circleMap c R θ) ≠ 0) :
    ContinuousOn (fun x =>
      (2 * Real.pi * I)⁻¹ * ∮ z in C(c, R), f x z / g x z) s :=
  continuous_const.continuousOn.mul (continuousOn_circleIntegral_div c R hf hg hzero)

/-- Continuity on a set of a real cast detects continuity on that set of a
natural-valued map. -/
theorem continuousOn_nat_of_cast {X : Type*} [TopologicalSpace X] {f : X → ℕ}
    {s : Set X} (hf : ContinuousOn (fun x => (f x : ℝ)) s) : ContinuousOn f s := by
  exact Nat.isClosedEmbedding_coe_real.isInducing.continuousOn_iff.mpr hf

/-- Continuity on a set of a complex cast detects continuity on that set of a
natural-valued map. -/
theorem continuousOn_nat_of_complexCast {X : Type*} [TopologicalSpace X]
    {f : X → ℕ} {s : Set X} (hf : ContinuousOn (fun x => (f x : ℂ)) s) :
    ContinuousOn f s := by
  apply continuousOn_nat_of_cast
  exact Complex.continuous_re.continuousOn.comp hf fun _ _ => mem_univ _

/-- Continuity on a set of a real cast detects continuity on that set of an
integer-valued map. -/
theorem continuousOn_int_of_cast {X : Type*} [TopologicalSpace X] {f : X → ℤ}
    {s : Set X} (hf : ContinuousOn (fun x => (f x : ℝ)) s) : ContinuousOn f s := by
  exact Int.isClosedEmbedding_coe_real.isInducing.continuousOn_iff.mpr hf

/-- Continuity on a set of a complex cast detects continuity on that set of an
integer-valued map. -/
theorem continuousOn_int_of_complexCast {X : Type*} [TopologicalSpace X]
    {f : X → ℤ} {s : Set X} (hf : ContinuousOn (fun x => (f x : ℂ)) s) :
    ContinuousOn f s := by
  apply continuousOn_int_of_cast
  exact Complex.continuous_re.continuousOn.comp hf fun _ _ => mem_univ _

/-- A continuous map from a real interval to a discrete space has equal
values at its endpoints. -/
theorem eq_endpoints_of_continuousOn {Y : Type*} [TopologicalSpace Y]
    [DiscreteTopology Y] {a b : ℝ} (hab : a ≤ b) {f : ℝ → Y}
    (hf : ContinuousOn f (Icc a b)) : f a = f b :=
  (ordConnected_Icc.isPreconnected).constant hf
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)

/-- A natural-valued map has equal endpoint values when its complex cast is
continuous on the intervening interval.

The complex cast detects continuity of the natural-valued map. -/
theorem nat_eq_endpoints_of_complexCast {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℕ}
    (hf : ContinuousOn (fun x => (f x : ℂ)) (Icc a b)) : f a = f b :=
  eq_endpoints_of_continuousOn hab (continuousOn_nat_of_complexCast hf)

/-- An integer-valued map has equal endpoint values when its complex cast is
continuous on the intervening interval.

This is the integer-valued counterpart of `nat_eq_endpoints_of_complexCast`. -/
theorem int_eq_endpoints_of_complexCast {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℤ}
    (hf : ContinuousOn (fun x => (f x : ℂ)) (Icc a b)) : f a = f b :=
  eq_endpoints_of_continuousOn hab (continuousOn_int_of_complexCast hf)

end

end Erdos522.PolynomialCircle


/-!
# The argument principle for complex polynomials

This module identifies the normalized circle integral of a polynomial's
logarithmic derivative with its number of roots in the enclosed open disc,
counted with multiplicity.
-/

open Complex Metric Polynomial Set

namespace Erdos522.PolynomialCircle

noncomputable section

/-- Number of roots of `p` in the open disc, counted with multiplicity. -/
noncomputable def rootsInDisc (p : ℂ[X]) (c : ℂ) (R : ℝ) : ℕ := by
  classical
  exact p.roots.countP fun a => a ∈ ball c R

/-- A reciprocal factor whose pole is neither inside nor on a nonnegative-
radius circle has integral zero. -/
theorem integral_subInv_outside_of_not_mem {c a : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (haSphere : a ∉ sphere c R) (haBall : a ∉ ball c R) :
    (∮ z in C(c, R), (z - a)⁻¹) = 0 := by
  apply integral_subInv_outside hR
  intro hclosed
  apply haSphere
  rw [mem_sphere]
  rw [mem_closedBall] at hclosed
  exact le_antisymm hclosed (not_lt.mp (haBall ∘ mem_ball.mpr))

/-- The unnormalized logarithmic-derivative integral is `2πi` times the
number of roots in the open disc, counted with multiplicity. -/
theorem integral_logDeriv_eq_rootCount {p : ℂ[X]} (hp : p ≠ 0)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ z ∈ sphere c R, p.eval z ≠ 0) :
    (∮ z in C(c, R), p.derivative.eval z / p.eval z) =
      (rootsInDisc p c R : ℂ) * (2 * Real.pi * I) := by
  classical
  rw [integral_logDeriv_eq_sum hp hR hboundary]
  have hroot : ∀ a ∈ p.roots, a ∉ sphere c R := by
    intro a haRoot haSphere
    exact hboundary a haSphere ((mem_roots hp).mp haRoot)
  have hsum : ∀ roots : Multiset ℂ,
      (∀ a ∈ roots, a ∉ sphere c R) →
      (roots.map fun a => ∮ z in C(c, R), (z - a)⁻¹).sum =
        (roots.countP (fun a => a ∈ ball c R) : ℂ) * (2 * Real.pi * I) := by
    intro roots
    induction roots using Multiset.induction_on with
    | empty => simp
    | @cons a roots ih =>
        intro hnone
        have ha := hnone a (Multiset.mem_cons_self a roots)
        have htail : ∀ b ∈ roots, b ∉ sphere c R :=
          fun b hb => hnone b (Multiset.mem_cons_of_mem hb)
        rw [Multiset.map_cons, Multiset.sum_cons, Multiset.countP_cons, ih htail]
        by_cases hin : a ∈ ball c R
        · rw [ite_eq_left hin, integral_subInv_inside hin]
          push_cast
          ring
        · rw [ite_eq_right hin, integral_subInv_outside_of_not_mem hR ha hin]
          simp
  simpa only [rootsInDisc] using hsum p.roots hroot

/-- Polynomial argument principle on a nonnegative-radius circle: the
normalized logarithmic-derivative integral is the number of roots in the open
disc, counted with multiplicity. The case `R = 0` is degenerate and
both sides vanish. -/
theorem argumentPrinciple {p : ℂ[X]} (hp : p ≠ 0)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ z ∈ sphere c R, p.eval z ≠ 0) :
    (2 * Real.pi * I)⁻¹ *
        ∮ z in C(c, R), p.derivative.eval z / p.eval z =
      (rootsInDisc p c R : ℂ) := by
  rw [integral_logDeriv_eq_rootCount hp hR hboundary]
  field_simp [Real.pi_ne_zero]

/-- Under the argument-principle hypotheses, equality of two normalized
logarithmic-derivative integrals is equivalent to equality of their natural
root counts. -/
theorem rootsInDisc_eq_iff {p q : ℂ[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hpBoundary : ∀ z ∈ sphere c R, p.eval z ≠ 0)
    (hqBoundary : ∀ z ∈ sphere c R, q.eval z ≠ 0) :
    rootsInDisc p c R = rootsInDisc q c R ↔
      (2 * Real.pi * I)⁻¹ *
          ∮ z in C(c, R), p.derivative.eval z / p.eval z =
        (2 * Real.pi * I)⁻¹ *
          ∮ z in C(c, R), q.derivative.eval z / q.eval z := by
  rw [argumentPrinciple hp hR hpBoundary, argumentPrinciple hq hR hqBoundary]
  norm_cast

end


end Erdos522.PolynomialCircle


/-!
# Root counts along an affine polynomial homotopy

The affine path from `g` to `f` has constant root count in a fixed disc when
it remains nonzero on the boundary circle for parameters in `[0, 1]`.  Rouché's boundary inequality implies this nonvanishing condition.
-/

open Complex Metric Polynomial Set

namespace Erdos522.PolynomialCircle

noncomputable section

/-- The affine polynomial path from `g` at `t = 0` to `f` at `t = 1`. -/
def affineHomotopy (f g : ℂ[X]) (t : ℝ) : ℂ[X] :=
  g + C (t : ℂ) * (f - g)

namespace affineHomotopy

@[simp]
theorem zero (f g : ℂ[X]) : affineHomotopy f g 0 = g := by
  simp [affineHomotopy]

@[simp]
theorem one (f g : ℂ[X]) : affineHomotopy f g 1 = f := by
  simp [affineHomotopy]

@[simp]
theorem eval (f g : ℂ[X]) (t : ℝ) (z : ℂ) :
    (affineHomotopy f g t).eval z =
      g.eval z + (t : ℂ) * (f.eval z - g.eval z) := by
  simp [affineHomotopy]

@[simp]
theorem derivative (f g : ℂ[X]) (t : ℝ) :
    (affineHomotopy f g t).derivative =
      affineHomotopy f.derivative g.derivative t := by
  simp [affineHomotopy]

/-- Evaluation of the affine path along a fixed parameterized circle is
jointly continuous in the homotopy parameter and circle parameter. -/
theorem continuous_eval (f g : ℂ[X]) (c : ℂ) (R : ℝ) :
    Continuous fun q : ℝ × ℝ =>
      (affineHomotopy f g q.1).eval (circleMap c R q.2) := by
  rw [show (fun q : ℝ × ℝ =>
      (affineHomotopy f g q.1).eval (circleMap c R q.2)) =
    fun q => g.eval (circleMap c R q.2) + (q.1 : ℂ) *
      (f.eval (circleMap c R q.2) - g.eval (circleMap c R q.2)) by
    funext q
    rw [eval]]
  fun_prop

/-- Derivative evaluation of the affine path along a fixed parameterized
circle is jointly continuous in both parameters. -/
theorem continuous_derivativeEval (f g : ℂ[X]) (c : ℂ) (R : ℝ) :
    Continuous fun q : ℝ × ℝ =>
      (affineHomotopy f g q.1).derivative.eval (circleMap c R q.2) := by
  rw [show (fun q : ℝ × ℝ =>
      (affineHomotopy f g q.1).derivative.eval (circleMap c R q.2)) =
    fun q => g.derivative.eval (circleMap c R q.2) + (q.1 : ℂ) *
      (f.derivative.eval (circleMap c R q.2) -
        g.derivative.eval (circleMap c R q.2)) by
    funext q
    rw [derivative, eval]]
  fun_prop

/-- The root count of a boundary-nonvanishing affine polynomial homotopy is
continuous on its parameter interval. -/
theorem continuous_rootsInDisc {f g : ℂ[X]} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R)
    (hboundary : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ sphere c R,
      (affineHomotopy f g t).eval z ≠ 0) :
    ContinuousOn (fun t => rootsInDisc (affineHomotopy f g t) c R)
      (Icc (0 : ℝ) 1) := by
  have hpoly : ∀ t ∈ Icc (0 : ℝ) 1, affineHomotopy f g t ≠ 0 := by
    intro t ht hp
    have hn := hboundary t ht (circleMap c R 0) (circleMap_mem_sphere c hR 0)
    simp [hp] at hn
  apply continuousOn_nat_of_complexCast
  have hintegral := continuousOn_normalizedCircleIntegral_div
    (f := fun t z => (affineHomotopy f g t).derivative.eval z)
    (g := fun t z => (affineHomotopy f g t).eval z)
    (s := Icc (0 : ℝ) 1) c R
    (continuous_derivativeEval f g c R).continuousOn
    (continuous_eval f g c R).continuousOn
    (fun t ht θ => hboundary t ht (circleMap c R θ) (circleMap_mem_sphere c hR θ))
  apply hintegral.congr
  intro t ht
  exact (argumentPrinciple (hpoly t ht) hR
    (hboundary t ht)).symm

/-- A boundary-nonvanishing affine homotopy has equal root counts at its two
endpoints. -/
theorem rootsInDisc_eq {f g : ℂ[X]} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R)
    (hboundary : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ sphere c R,
      (affineHomotopy f g t).eval z ≠ 0) :
    rootsInDisc g c R = rootsInDisc f c R := by
  have h := eq_endpoints_of_continuousOn (a := (0 : ℝ)) (b := 1) (by norm_num)
    (continuous_rootsInDisc hR hboundary)
  simpa using h

end affineHomotopy

end


end Erdos522.PolynomialCircle


/-!
# Rouché's theorem for complex polynomials on circles

The classical and symmetric norm inequalities exclude zeros of the affine
path on the boundary circle.  Root-count equality then follows from the
homotopy theorem.
-/

open Complex Metric Polynomial Set

namespace Erdos522.PolynomialCircle

noncomputable section

/-- Classical Rouché theorem for complex polynomials on a circle, with roots
counted with multiplicity in the enclosed open disc. -/
theorem rouche {f g : ℂ[X]} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ z ∈ sphere c R, ‖f.eval z - g.eval z‖ < ‖g.eval z‖) :
    rootsInDisc f c R = rootsInDisc g c R := by
  apply (affineHomotopy.rootsInDisc_eq hR ?_).symm
  intro t ht z hz hzero
  rw [affineHomotopy.eval] at hzero
  let d := f.eval z - g.eval z
  change g.eval z + (t : ℂ) * d = 0 at hzero
  have hg : g.eval z = -(t : ℂ) * d := by
    linear_combination hzero
  have hnorm : ‖g.eval z‖ = t * ‖d‖ := by
    rw [hg, norm_mul, norm_neg, norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have hle : ‖g.eval z‖ ≤ ‖d‖ := by
    rw [hnorm]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  exact (not_le_of_gt (by simpa only [d] using h z hz)) hle

/-- Symmetric Rouché theorem: strictness in the triangle inequality on the
boundary circle is enough to give equal root counts in the disc. -/
theorem rouche_symmetric {f g : ℂ[X]} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ z ∈ sphere c R,
      ‖f.eval z - g.eval z‖ < ‖f.eval z‖ + ‖g.eval z‖) :
    rootsInDisc f c R = rootsInDisc g c R := by
  apply (affineHomotopy.rootsInDisc_eq hR ?_).symm
  intro t ht z hz hzero
  rw [affineHomotopy.eval] at hzero
  let d := f.eval z - g.eval z
  change g.eval z + (t : ℂ) * d = 0 at hzero
  have hg : g.eval z = -(t : ℂ) * d := by
    linear_combination hzero
  have hf : f.eval z = ((1 - t : ℝ) : ℂ) * d := by
    push_cast
    linear_combination hzero
  have hnormg : ‖g.eval z‖ = t * ‖d‖ := by
    rw [hg, norm_mul, norm_neg, norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have hnormf : ‖f.eval z‖ = (1 - t) * ‖d‖ := by
    rw [hf, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]
  have hsum : ‖d‖ = ‖f.eval z‖ + ‖g.eval z‖ := by
    rw [hnormf, hnormg]
    ring
  have hlt : ‖d‖ < ‖f.eval z‖ + ‖g.eval z‖ := by
    simpa only [d] using h z hz
  rw [← hsum] at hlt
  exact (lt_irrefl _ hlt)

end


end Erdos522.PolynomialCircle


namespace Erdos522

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Rouché's boundary inequality preserves the number of polynomial roots
in an open disk, counted with multiplicity. -/
theorem polynomial_rouche_root_count (P G : Polynomial ℂ) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hboundary : ∀ z ∈ Metric.sphere c R, ‖G.eval z‖ < ‖P.eval z‖) :
    zeroCountIn (P + G) (Metric.ball c R) = zeroCountIn P (Metric.ball c R) := by
  have h := PolynomialCircle.rouche (f := P + G) (g := P) (c := c) hR
    (by simpa only [Polynomial.eval_add, add_sub_cancel_left] using hboundary)
  simpa only [PolynomialCircle.rootsInDisc, zeroCountIn,
    ← Multiset.countP_eq_card_filter] using h

/-- A polynomial with no zero on a sphere has the same root count in its
open and closed disks. -/
theorem zeroCountIn_closedBall_eq_ball (P : Polynomial ℂ) (c : ℂ) (R : ℝ)
    (hboundary : ∀ z ∈ Metric.sphere c R, P.eval z ≠ 0) :
    zeroCountIn P (Metric.closedBall c R) = zeroCountIn P (Metric.ball c R) := by
  classical
  unfold zeroCountIn
  congr 1
  apply Multiset.filter_congr
  intro z hz
  constructor
  · intro hzD
    have hzroot := (Polynomial.mem_roots'.mp hz).2
    have hd := Metric.mem_closedBall.mp hzD
    have hne : dist z c ≠ R := by
      intro he
      exact hboundary z (Metric.mem_sphere.mpr he) hzroot
    exact Metric.mem_ball.mpr (lt_of_le_of_ne hd hne)
  · intro hzD
    exact Metric.ball_subset_closedBall hzD

/-- Strict Rouché domination also preserves closed-disk root counts, since
neither polynomial can vanish on the boundary. -/
theorem polynomial_rouche_closed_root_count (P G : Polynomial ℂ) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hboundary : ∀ z ∈ Metric.sphere c R, ‖G.eval z‖ < ‖P.eval z‖) :
    zeroCountIn (P + G) (Metric.closedBall c R) = zeroCountIn P (Metric.closedBall c R) := by
  have hP : ∀ z ∈ Metric.sphere c R, P.eval z ≠ 0 := by
    intro z hz he
    have h := hboundary z hz
    simp only [he, norm_zero] at h
    exact (norm_nonneg _).not_gt h
  have hQ : ∀ z ∈ Metric.sphere c R, (P + G).eval z ≠ 0 := by
    intro z hz he
    have he' : G.eval z = -(P.eval z) := by
      rw [Polynomial.eval_add] at he
      linear_combination he
    have h := hboundary z hz
    rw [he', norm_neg] at h
    exact h.false
  rw [zeroCountIn_closedBall_eq_ball _ _ _ hP,
    zeroCountIn_closedBall_eq_ball _ _ _ hQ]
  exact polynomial_rouche_root_count P G c R hR hboundary

/-- Boundary domination on disjoint localization disks gives the full
root-count matching estimate, with the positive part of the actual degree change. -/
theorem polynomial_root_matching_on_disks {ι : Type*} [Fintype ι]
    (P G : Polynomial ℂ) (c : ι → ℂ) (R : ι → ℝ) (r : ℝ)
    (hR : ∀ i, 0 ≤ R i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (R i)) (Metric.ball (c j) (R j)))
    (hP : ∀ i, zeroCountIn P (Metric.ball (c i) (R i)) = 1)
    (hboundary : ∀ i z, z ∈ Metric.sphere (c i) (R i) → ‖G.eval z‖ < ‖P.eval z‖) :
    Nat.dist (closedZeroCount (P + G) r) (closedZeroCount P r) ≤
      (Finset.univ.filter (fun i ↦ ∃ z ∈ closure (Metric.ball (c i) (R i)), ‖z‖ = r)).card +
        (P.natDegree - Fintype.card ι) + ((P + G).natDegree - P.natDegree) := by
  apply disjoint_domain_root_matching P (P + G) (fun i ↦ Metric.ball (c i) (R i)) r
    hdisj (fun i ↦ (convex_ball (c i) (R i)).isPreconnected) hP
  intro i
  rw [polynomial_rouche_root_count P G (c i) (R i) (hR i) (hboundary i), hP i]

/-- A perturbation smaller than `a` on the localization circle preserves its
single root, counted with multiplicity. -/
theorem regular_root_perturbation_count (P G : Polynomial ℂ) {α : ℂ} {M d₀ a : ℝ}
    (ha : 0 < a) (hd : 0 < d₀) (hα : P.eval α = 0)
    (hderiv : d₀ ≤ ‖P.derivative.eval α‖) (hbudget : 4 * M * a ≤ d₀ ^ 2)
    (hbound : ∀ z ∈ Metric.closedBall α (2 * a / d₀),
      ‖P.derivative.derivative.eval z‖ ≤ M)
    (hG : ∀ z ∈ Metric.sphere α (2 * a / d₀), ‖G.eval z‖ < a) :
    zeroCountIn (P + G) (Metric.ball α (2 * a / d₀)) = 1 := by
  have hrad : 0 < 2 * a / d₀ := by positivity
  rw [polynomial_rouche_root_count P G α (2 * a / d₀) hrad.le]
  · exact regular_root_count_ball P ha hd hα hderiv hbudget hbound
  · intro z hz
    have hr : ‖z - α‖ = 2 * a / d₀ := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    have hzD : z ∈ Metric.closedBall α (2 * a / d₀) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hr.le
    have hb := regular_root_boundary_barrier P ha.le hd hα hderiv hbudget hr
      (polynomial_taylor_remainder P (convex_closedBall α _)
        (Metric.mem_closedBall_self hrad.le) hzD hbound)
    exact (hG z hz).trans_le (by linarith)

/-- Regular roots in a common convex domain yield disjoint perturbation-stable
disks and hence a closed-disk root-count comparison for every target radius. -/
theorem regular_root_family_matching {ι : Type*} [Fintype ι]
    (P G : Polynomial ℂ) (z : ι → ℂ) {D : Set ℂ} {M d₀ a : ℝ} (r : ℝ)
    (ha : 0 < a) (hd : 0 < d₀) (hD : Convex ℝ D) (hinj : Function.Injective z)
    (hroot : ∀ i, P.eval (z i) = 0) (hderiv : ∀ i, d₀ ≤ ‖P.derivative.eval (z i)‖)
    (hbudget : 4 * M * a ≤ d₀ ^ 2)
    (hdisks : ∀ i, Metric.closedBall (z i) (2 * a / d₀) ⊆ D)
    (hbound : ∀ w ∈ D, ‖P.derivative.derivative.eval w‖ ≤ M)
    (hG : ∀ i w, w ∈ Metric.sphere (z i) (2 * a / d₀) → ‖G.eval w‖ < a) :
    Nat.dist (closedZeroCount (P + G) r) (closedZeroCount P r) ≤
      (Finset.univ.filter (fun i ↦ ∃ w ∈ closure (Metric.ball (z i) (2 * a / d₀)),
        ‖w‖ = r)).card + (P.natDegree - Fintype.card ι) +
        ((P + G).natDegree - P.natDegree) := by
  have hrad : 0 < 2 * a / d₀ := by positivity
  have hzD : ∀ i, z i ∈ D := fun i ↦ hdisks i (Metric.mem_closedBall_self hrad.le)
  have hlocal : ∀ i w, w ∈ Metric.closedBall (z i) (2 * a / d₀) →
      ‖P.derivative.derivative.eval w‖ ≤ M := fun i w hw ↦ hbound w (hdisks i hw)
  apply disjoint_domain_root_matching P (P + G)
    (fun i ↦ Metric.ball (z i) (2 * a / d₀)) r
    (regular_root_family_disjoint P z hD hd hinj hzD hroot hderiv hbudget hbound)
    (fun i ↦ (convex_ball (z i) (2 * a / d₀)).isPreconnected)
  · intro i
    exact regular_root_count_ball P ha hd (hroot i) (hderiv i) hbudget (hlocal i)
  · intro i
    exact regular_root_perturbation_count P G ha hd (hroot i) (hderiv i) hbudget
      (hlocal i) (hG i)

end
end Erdos522

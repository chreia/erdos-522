/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.HolomorphicZeroCount
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Meromorphic.IsolatedZeros

/-!
# Factoring the zeros of a holomorphic function

On a compact set without isolated points, a holomorphic function with finite
orders factors pointwise into its finite zero product and a nonvanishing
holomorphic function. The exponents retain the analytic multiplicities.
-/

noncomputable section
open Filter MeromorphicOn Metric Set
open scoped Topology BigOperators
namespace Erdos522

/-- The zero divisor of a holomorphic function gives an entire finite product. -/
theorem analyticAt_zero_product {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (z : ℂ) :
    AnalyticAt ℂ (∏ᶠ u : ℂ, (fun w : ℂ => w - u) ^ divisor f U u) z := by
  apply analyticAt_finprod
  intro u
  have hn := hf.divisor_nonneg u
  rw [← Int.toNat_of_nonneg hn, zpow_natCast]
  fun_prop

/-- Analytic functions agreeing outside a discrete subset of a set without isolated
    points agree at every point of the set. -/
theorem analytic_eqOn_of_codiscrete {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hU : Preperfect U) (heq : f =ᶠ[codiscreteWithin U] g) : Set.EqOn f g U := by
  intro z hz
  have h := (hf z hz).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    (hg z hz).meromorphicAt hz hU heq
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hf z hz).continuousAt.mono_left nhdsWithin_le_nhds)
    ((hg z hz).continuousAt.mono_left nhdsWithin_le_nhds) h

/-- Removing all divisor zeros on a compact set leaves a holomorphic factor
    which is nonzero throughout that set. The identity also holds at the zeros. -/
theorem exists_nonvanishing_analytic_factor {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsCompact U) (hperfect : Preperfect U)
    (horder : ∀ u : U, meromorphicOrderAt f u ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ (∀ z ∈ U, g z ≠ 0) ∧
      ∀ z ∈ U, f z = (∏ᶠ u : ℂ, (z - u) ^ divisor f U u) * g z := by
  obtain ⟨g, hg, hg0, heq⟩ := hf.meromorphicOn.extract_zeros_poles horder
    ((divisor f U).finiteSupport hU)
  have hprod : AnalyticOnNhd ℂ (∏ᶠ u : ℂ, (fun w : ℂ => w - u) ^ divisor f U u) U :=
    fun z _ => analyticAt_zero_product hf z
  have hid := analytic_eqOn_of_codiscrete hf (hprod.smul hg) hperfect heq
  refine ⟨g, hg, fun z hz => hg0 ⟨z, hz⟩, ?_⟩
  intro z hz
  have hfinite : Function.HasFiniteMulSupport
      (fun u : ℂ => (fun w : ℂ => w - u) ^ divisor f U u) := by
    apply ((divisor f U).finiteSupport hU).subset
    intro u hu
    by_contra h
    have hz : divisor f U u = 0 := by simpa only [Function.mem_support, not_not] using h
    exact hu (by simp [hz])
  have h := hid hz
  simpa only [Pi.smul_apply, smul_eq_mul, finprod_apply hfinite, Pi.pow_apply] using h

/-- A nonzero entire function has finite meromorphic order everywhere. -/
theorem meromorphicOrderAt_ne_top_of_entire {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : f ≠ 0) (z : ℂ) :
    meromorphicOrderAt f z ≠ ⊤ := by
  rw [(hf z (mem_univ z)).meromorphicOrderAt_eq]
  have hn := analyticOrderAt_ne_top_of_entire hf hne z
  lift analyticOrderAt f z to ℕ using hn with n hn
  simp

/-- On a closed disk of positive radius, an entire nonzero function factors into
    its exact zero divisor and a holomorphic function without zeros. -/
theorem exists_nonvanishing_factor_on_closedBall {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : f ≠ 0) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) ∧
      (∀ z ∈ closedBall c R, g z ≠ 0) ∧
      ∀ z ∈ closedBall c R, f z =
        (∏ᶠ u : ℂ, (z - u) ^ divisor f (closedBall c R) u) * g z := by
  apply exists_nonvanishing_analytic_factor (hf.mono (subset_univ _)) (isCompact_closedBall c R)
  · rw [← closure_ball c hR.ne']
    exact isOpen_ball.perfect_closure.2
  · intro u
    exact meromorphicOrderAt_ne_top_of_entire hf hne u

/-- The zero product is a finite product of natural powers indexed by the support
    of its divisor, including roots on the boundary of the compact domain. -/
theorem zero_product_eq_finite_product {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsCompact U) (z : ℂ) :
    (∏ᶠ u : ℂ, (z - u) ^ divisor f U u) =
      ∏ u ∈ ((divisor f U).finiteSupport hU).toFinset, (z - u) ^ (divisor f U u).toNat := by
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ ?_ ((divisor f U).finiteSupport hU)]
  · apply Finset.prod_congr rfl
    intro u _
    rw [← zpow_natCast, Int.toNat_of_nonneg (hf.divisor_nonneg u)]
  · intro u hu
    by_contra h
    have hz : divisor f U u = 0 := by simpa only [Function.mem_support, not_not] using h
    exact hu (by simp [hz])

end Erdos522

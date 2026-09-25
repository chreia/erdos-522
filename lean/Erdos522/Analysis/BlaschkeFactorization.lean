/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.HolomorphicFactorization
import Mathlib.Analysis.Complex.AbsMax

/-!
# Finite Blaschke factorization

The interior zero divisor of a holomorphic function determines a finite Blaschke
product. Dividing out this product leaves a holomorphic function without zeros
in the open disk and preserves boundary norms. The factorization holds at every
point of the closed disk, including the zeros.
-/

noncomputable section

open Filter Function MeromorphicOn Metric Set
open scoped Topology ComplexConjugate BigOperators

namespace Erdos522

/-- A Blaschke factor for a zero at `w` in the disk of radius `R`. -/
def blaschkeFactor (R : ℝ) (w z : ℂ) : ℂ :=
  (R : ℂ) * (z - w) / ((R : ℂ) ^ 2 - conj w * z)

/-- The usual Blaschke factor is the inverse of the canonical factor. -/
theorem blaschkeFactor_eq_inv_canonicalFactor (R : ℝ) (w z : ℂ) :
    blaschkeFactor R w z = (Complex.canonicalFactor R w z)⁻¹ := by
  simp only [blaschkeFactor, Complex.canonicalFactor_apply, inv_div]

/-- The denominator of a Blaschke factor does not vanish on the closed disk. -/
theorem blaschkeFactor_denominator_ne_zero {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ closedBall 0 R) :
    (R : ℂ) ^ 2 - conj w * z ≠ 0 := by
  have hR := pos_of_mem_ball hw
  have hwR : ‖w‖ < R := mem_ball_zero_iff.mp hw
  have hzR : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  have hnorm : ‖conj w * z‖ < ‖(R : ℂ) ^ 2‖ := by
    rw [norm_mul, Complex.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR]
    calc
      ‖w‖ * ‖z‖ ≤ ‖w‖ * R := mul_le_mul_of_nonneg_left hzR (norm_nonneg _)
      _ < R * R := mul_lt_mul_of_pos_right hwR hR
      _ = R ^ 2 := (pow_two R).symm
  exact sub_ne_zero.mpr (ne_of_apply_ne norm hnorm.ne).symm

/-- Each Blaschke factor is holomorphic near the closed disk. -/
theorem analyticOnNhd_blaschkeFactor {R : ℝ} {w : ℂ} (hw : w ∈ ball 0 R) :
    AnalyticOnNhd ℂ (blaschkeFactor R w) (closedBall 0 R) := by
  intro z hz
  unfold blaschkeFactor
  fun_prop (disch := exact blaschkeFactor_denominator_ne_zero hw hz)

/-- A Blaschke factor has norm one on the boundary circle. -/
theorem norm_blaschkeFactor_on_sphere {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ sphere 0 R) :
    ‖blaschkeFactor R w z‖ = 1 := by
  rw [blaschkeFactor_eq_inv_canonicalFactor, norm_inv,
    Complex.norm_canonicalFactor_eval_circle_eq_one hw hz, inv_one]

/-- The finite Blaschke product prescribed by the interior zero divisor.
The natural exponents are the exact multiplicities for holomorphic functions. -/
def finiteBlaschkeProduct (f : ℂ → ℂ) (R : ℝ) : ℂ → ℂ :=
  ∏ᶠ u : ℂ, (blaschkeFactor R u) ^ (divisor f (ball 0 R) u).toNat

/-- Holomorphy of the finite divisor product on the closed disk. -/
theorem analyticOnNhd_finiteBlaschkeProduct (f : ℂ → ℂ) (R : ℝ) :
    AnalyticOnNhd ℂ (finiteBlaschkeProduct f R) (closedBall 0 R) := by
  intro z hz
  apply analyticAt_finprod
  intro u
  by_cases hu : u ∈ ball (0 : ℂ) R
  · exact ((analyticOnNhd_blaschkeFactor hu) z hz).pow _
  · have hdiv : divisor f (ball 0 R) u = 0 :=
      (divisor f (ball 0 R)).apply_eq_zero_of_notMem hu
    simp only [hdiv, Int.toNat_zero, pow_zero]
    exact analyticAt_const

/-- The Blaschke product is the native canonical product with the opposite divisor. -/
theorem finiteBlaschkeProduct_eq_canonical_product {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    finiteBlaschkeProduct f R =
      ∏ᶠ u : ℂ, (Complex.canonicalFactor R u) ^ (-divisor f (ball 0 R) u) := by
  unfold finiteBlaschkeProduct
  apply finprod_congr
  intro u
  funext z
  have hn := (hf.mono ball_subset_closedBall).divisor_nonneg u
  rw [← Int.toNat_of_nonneg hn]
  simp only [Int.toNat_natCast, Pi.pow_apply, zpow_neg, zpow_natCast,
    blaschkeFactor_eq_inv_canonicalFactor, inv_pow]

/-- The finite product written explicitly over the divisor support. -/
theorem finiteBlaschkeProduct_apply {f : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicOn f (closedBall 0 R)) (z : ℂ) :
    finiteBlaschkeProduct f R z =
      ∏ u ∈ hf.divisor_ball_support_finite.toFinset,
        blaschkeFactor R u z ^ (divisor f (ball 0 R) u).toNat := by
  unfold finiteBlaschkeProduct
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ ?_ hf.divisor_ball_support_finite]
  · simp only [Finset.prod_apply, Pi.pow_apply]
  · intro u hu
    by_contra h
    have hn : divisor f (ball 0 R) u = 0 := by simpa only [mem_support, not_not] using h
    exact hu (by simp [hn])

/-- The full interior divisor product has norm one on the boundary circle. -/
theorem norm_finiteBlaschkeProduct_on_sphere {f : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicOn f (closedBall 0 R)) {z : ℂ} (hz : z ∈ sphere 0 R) :
    ‖finiteBlaschkeProduct f R z‖ = 1 := by
  rw [finiteBlaschkeProduct_apply hf, norm_prod]
  apply Finset.prod_eq_one
  intro u hu
  have hu' := (divisor f (ball 0 R)).supportWithinDomain
    (hf.divisor_ball_support_finite.mem_toFinset.mp hu)
  rw [norm_pow, norm_blaschkeFactor_on_sphere hu' hz, one_pow]

/-- A holomorphic boundary bound extends to the entire closed disk. -/
theorem norm_le_on_closedBall_of_sphere_bound {g : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hbound : ∀ z ∈ sphere 0 R, ‖g z‖ ≤ M) {z : ℂ} (hz : z ∈ closedBall 0 R) :
    ‖g z‖ ≤ M := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := ball (0 : ℂ) R) isBounded_ball
    (hg.differentiableOn.diffContOnCl_ball subset_rfl)
  · intro w hw
    exact hbound w (frontier_ball_subset_sphere hw)
  · simpa only [closure_ball (0 : ℂ) hR.ne'] using hz

/-- The finite Blaschke product is bounded by one throughout the disk. -/
theorem norm_finiteBlaschkeProduct_le_one {f : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicOn f (closedBall 0 R)) (hR : 0 < R)
    {z : ℂ} (hz : z ∈ closedBall 0 R) :
    ‖finiteBlaschkeProduct f R z‖ ≤ 1 := by
  exact norm_le_on_closedBall_of_sphere_bound hR
    (analyticOnNhd_finiteBlaschkeProduct f R)
    (fun w hw => (norm_finiteBlaschkeProduct_on_sphere hf hw).le) hz

/-- Removing the interior zero divisor yields a nonvanishing holomorphic factor;
the pointwise identity and boundary norm equality include boundary zeros of `f`. -/
theorem exists_blaschke_factorization {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hR : 0 < R)
    (horder : ∀ u : closedBall (0 : ℂ) R, meromorphicOrderAt f u ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ z ∈ ball 0 R, g z ≠ 0) ∧
      (∀ z ∈ closedBall 0 R, f z = finiteBlaschkeProduct f R z * g z) ∧
      (∀ z ∈ sphere 0 R, ‖g z‖ = ‖f z‖) := by
  obtain ⟨g, D⟩ := hf.meromorphicOn.exists_canonicalDecomp horder
  have hg : AnalyticOnNhd ℂ g (closedBall 0 R) := by
    apply D.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd.mp
    intro z
    change 0 ≤ divisor g (closedBall 0 R) z
    rw [D.divisor_eq_divisor hR]
    exact (hf.mono sphere_subset_closedBall).divisor_nonneg z
  have heq : ∀ z ∈ closedBall 0 R, f z = finiteBlaschkeProduct f R z * g z := by
    apply analytic_eqOn_of_codiscrete hf ((analyticOnNhd_finiteBlaschkeProduct f R).mul hg)
    · rw [← closure_ball (0 : ℂ) hR.ne']
      exact isOpen_ball.perfect_closure.2
    · have hD := D.eventuallyEq
      rw [← finiteBlaschkeProduct_eq_canonical_product hf] at hD
      filter_upwards [hD] with z hz
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply] using hz
  refine ⟨g, hg, D.ne_zero, heq, ?_⟩
  intro z hz
  have h := congrArg norm (heq z (sphere_subset_closedBall hz))
  rw [norm_mul, norm_finiteBlaschkeProduct_on_sphere hf.meromorphicOn hz, one_mul] at h
  exact h.symm

/-- A boundary majorant for the original function is also a disk majorant for
the holomorphic quotient after its interior zeros have been removed. -/
theorem exists_bounded_blaschke_factorization {f : ℂ → ℂ} {R M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hR : 0 < R)
    (horder : ∀ u : closedBall (0 : ℂ) R, meromorphicOrderAt f u ≠ ⊤)
    (hbound : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ M) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ z ∈ ball 0 R, g z ≠ 0) ∧
      (∀ z ∈ closedBall 0 R, f z = finiteBlaschkeProduct f R z * g z) ∧
      (∀ z ∈ sphere 0 R, ‖g z‖ = ‖f z‖) ∧
      (∀ z ∈ closedBall 0 R, ‖g z‖ ≤ M) := by
  obtain ⟨g, hg, hg0, heq, hnorm⟩ := exists_blaschke_factorization hf hR horder
  refine ⟨g, hg, hg0, heq, hnorm, ?_⟩
  intro z hz
  exact norm_le_on_closedBall_of_sphere_bound hR hg
    (fun w hw => (hnorm w hw).le.trans (hbound w hw)) hz

/-- For an entire nonzero function the finite-product exponents are precisely
the natural analytic orders of its interior zeros. -/
theorem finiteBlaschkeProduct_apply_of_entire {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : f ≠ 0) (z : ℂ) :
    finiteBlaschkeProduct f R z =
      ∏ u ∈ (hf.meromorphicOn.mono_set
        (subset_univ (closedBall (0 : ℂ) R))).divisor_ball_support_finite.toFinset,
        blaschkeFactor R u z ^ analyticOrderNatAt f u := by
  rw [finiteBlaschkeProduct_apply (hf.meromorphicOn.mono_set (subset_univ _))]
  apply Finset.prod_congr rfl
  intro u hu
  have hu' := (divisor f (ball 0 R)).supportWithinDomain
    ((hf.meromorphicOn.mono_set
      (subset_univ (closedBall (0 : ℂ) R))).divisor_ball_support_finite.mem_toFinset.mp hu)
  rw [divisor_eq_analyticOrderNatAt hf hne hu', Int.toNat_natCast]

/-- An entire nonzero function admits the bounded factorization on every disk
of positive radius. -/
theorem exists_bounded_blaschke_factorization_of_entire {f : ℂ → ℂ} {R M : ℝ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : f ≠ 0) (hR : 0 < R)
    (hbound : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ M) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ z ∈ ball 0 R, g z ≠ 0) ∧
      (∀ z ∈ closedBall 0 R, f z = finiteBlaschkeProduct f R z * g z) ∧
      (∀ z ∈ sphere 0 R, ‖g z‖ = ‖f z‖) ∧
      (∀ z ∈ closedBall 0 R, ‖g z‖ ≤ M) :=
  exists_bounded_blaschke_factorization (hf.mono (subset_univ _)) hR
    (fun u => meromorphicOrderAt_ne_top_of_entire hf hne u) hbound

end Erdos522

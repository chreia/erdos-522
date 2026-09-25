/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.BlaschkeFactorization
import Erdos522.Analysis.LogarithmicDerivative

/-!
# Quantitative estimates for finite Blaschke products

A Blaschke factor is bounded below by its linear zero factor. Its logarithmic
derivative is a simple pole plus an analytic correction, bounded by the inverse
distance to the outer circle. Summing these corrections counts zeros with their
natural multiplicities.
-/

noncomputable section

open Filter Function MeromorphicOn Metric Set
open scoped Topology ComplexConjugate BigOperators

namespace Erdos522

/-- On a smaller disk a Blaschke factor dominates its linear zero factor. -/
theorem norm_blaschkeFactor_ge {R r : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ closedBall 0 r) (hrR : r ≤ R) :
    ‖z - w‖ / (R + r) ≤ ‖blaschkeFactor R w z‖ := by
  have hR := pos_of_mem_ball hw
  have hr := nonneg_of_mem_closedBall hz
  have hwR : ‖w‖ ≤ R := (mem_ball_zero_iff.mp hw).le
  have hzR : ‖z‖ ≤ r := mem_closedBall_zero_iff.mp hz
  have hzouter : z ∈ closedBall (0 : ℂ) R := closedBall_subset_closedBall hrR hz
  have hden := norm_pos_iff.mpr (blaschkeFactor_denominator_ne_zero hw hzouter)
  have hdenle : ‖(R : ℂ) ^ 2 - conj w * z‖ ≤ R * (R + r) := by
    calc
      _ ≤ ‖(R : ℂ) ^ 2‖ + ‖conj w * z‖ := norm_sub_le _ _
      _ = R ^ 2 + ‖w‖ * ‖z‖ := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
          norm_mul, Complex.norm_conj]
      _ ≤ R ^ 2 + R * r := add_le_add_right
        (mul_le_mul hwR hzR (norm_nonneg _) hR.le) _
      _ = R * (R + r) := by ring
  rw [blaschkeFactor, norm_div, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR]
  apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg hR hr) hden).mpr
  nlinarith [mul_le_mul_of_nonneg_left hdenle (norm_nonneg (z - w))]

/-- Away from its zero a Blaschke factor is nonzero throughout the closed disk. -/
theorem blaschkeFactor_ne_zero {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ closedBall 0 R) (hzw : z ≠ w) :
    blaschkeFactor R w z ≠ 0 := by
  rw [blaschkeFactor_eq_inv_canonicalFactor]
  exact inv_ne_zero (Complex.canonicalFactor_ne_zero hw hz hzw)

/-- The logarithmic derivative splits into the zero pole and an analytic correction. -/
theorem logDeriv_blaschkeFactor {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ closedBall 0 R) (hzw : z ≠ w) :
    logDeriv (blaschkeFactor R w) z =
      1 / (z - w) + conj w / ((R : ℂ) ^ 2 - conj w * z) := by
  have hR : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pos_of_mem_ball hw).ne'
  have hden := blaschkeFactor_denominator_ne_zero hw hz
  have hnum : (R : ℂ) * (z - w) ≠ 0 := mul_ne_zero hR (sub_ne_zero.mpr hzw)
  change logDeriv (fun v : ℂ => (R : ℂ) * (v - w) /
    ((R : ℂ) ^ 2 - conj w * v)) z = _
  rw [logDeriv_fun_div z hnum hden (by fun_prop) (by fun_prop),
    logDeriv_const_mul z (R : ℂ) hR]
  have hlinear : deriv (fun v : ℂ => v - w) z = 1 :=
    ((hasDerivAt_id z).sub_const w).deriv
  have hdenD : deriv (fun v : ℂ => (R : ℂ) ^ 2 - conj w * v) z = -conj w := by
    simp
  rw [logDeriv_apply, logDeriv_apply, hlinear, hdenD]
  ring

/-- The analytic correction is controlled by the distance between the radii. -/
theorem norm_blaschke_logarithmic_correction_le {R r : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ closedBall 0 r) (hrR : r < R) :
    ‖conj w / ((R : ℂ) ^ 2 - conj w * z)‖ ≤ 1 / (R - r) := by
  have hR := pos_of_mem_ball hw
  have hr := nonneg_of_mem_closedBall hz
  have hwR : ‖w‖ ≤ R := (mem_ball_zero_iff.mp hw).le
  have hzR : ‖z‖ ≤ r := mem_closedBall_zero_iff.mp hz
  have hzouter : z ∈ closedBall (0 : ℂ) R := closedBall_subset_closedBall hrR.le hz
  have hden := norm_pos_iff.mpr (blaschkeFactor_denominator_ne_zero hw hzouter)
  have hdenle : R ^ 2 - ‖w‖ * r ≤ ‖(R : ℂ) ^ 2 - conj w * z‖ := by
    calc
      _ ≤ R ^ 2 - ‖w‖ * ‖z‖ := sub_le_sub_left
        (mul_le_mul_of_nonneg_left hzR (norm_nonneg _)) _
      _ = ‖(R : ℂ) ^ 2‖ - ‖conj w * z‖ := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
          norm_mul, Complex.norm_conj]
      _ ≤ _ := norm_sub_norm_le _ _
  rw [norm_div, Complex.norm_conj]
  apply (div_le_div_iff₀ hden (sub_pos.mpr hrR)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hwR hR.le]

/-- A finite product obeys the product of the individual lower bounds. -/
theorem norm_weighted_blaschke_product_ge {ι : Type*} (s : Finset ι)
    (w : ι → ℂ) (n : ι → ℕ) {R r : ℝ} {z : ℂ}
    (hw : ∀ i ∈ s, w i ∈ ball 0 R) (hz : z ∈ closedBall 0 r) (hrR : r ≤ R) :
    (∏ i ∈ s, (‖z - w i‖ / (R + r)) ^ n i) ≤
      ‖∏ i ∈ s, blaschkeFactor R (w i) z ^ n i‖ := by
  rw [norm_prod]
  apply Finset.prod_le_prod₀
  · intro i hi
    have hR := pos_of_mem_ball (hw i hi)
    have hr := nonneg_of_mem_closedBall hz
    positivity
  · intro i hi
    rw [norm_pow]
    have hR := pos_of_mem_ball (hw i hi)
    have hr := nonneg_of_mem_closedBall hz
    exact pow_le_pow_left₀ (by positivity) (norm_blaschkeFactor_ge (hw i hi) hz hrR) _

/-- The logarithmic derivative of a weighted finite product is the sum of its
pole terms and its analytic corrections. -/
theorem logDeriv_weighted_blaschke_product {ι : Type*} (s : Finset ι)
    (w : ι → ℂ) (n : ι → ℕ) {R : ℝ} {z : ℂ}
    (hw : ∀ i ∈ s, w i ∈ ball 0 R) (hz : z ∈ closedBall 0 R)
    (hzw : ∀ i ∈ s, z ≠ w i) :
    logDeriv (fun v => ∏ i ∈ s, blaschkeFactor R (w i) v ^ n i) z =
      (∑ i ∈ s, (n i : ℂ) / (z - w i)) +
        ∑ i ∈ s, (n i : ℂ) * (conj (w i) / ((R : ℂ) ^ 2 - conj (w i) * z)) := by
  rw [logDeriv_fun_prod (f := fun i v => blaschkeFactor R (w i) v ^ n i) (x := z)
    (fun i hi => pow_ne_zero _ (blaschkeFactor_ne_zero (hw i hi) hz (hzw i hi)))
    (fun i hi => ((analyticOnNhd_blaschkeFactor (hw i hi)) z hz).differentiableAt.pow _)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [logDeriv_fun_pow ((analyticOnNhd_blaschkeFactor (hw i hi)) z hz).differentiableAt,
    logDeriv_blaschkeFactor (hw i hi) hz (hzw i hi)]
  ring

/-- The summed analytic correction is at most the total multiplicity divided
by the distance to the boundary circle. -/
theorem norm_weighted_blaschke_correction_sum_le {ι : Type*} (s : Finset ι)
    (w : ι → ℂ) (n : ι → ℕ) {R r : ℝ} {z : ℂ}
    (hw : ∀ i ∈ s, w i ∈ ball 0 R) (hz : z ∈ closedBall 0 r) (hrR : r < R) :
    ‖∑ i ∈ s, (n i : ℂ) * (conj (w i) / ((R : ℂ) ^ 2 - conj (w i) * z))‖ ≤
      (∑ i ∈ s, (n i : ℝ)) / (R - r) := by
  calc
    _ ≤ ∑ i ∈ s, ‖(n i : ℂ) * (conj (w i) / ((R : ℂ) ^ 2 - conj (w i) * z))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, (n i : ℝ) * (1 / (R - r)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (norm_blaschke_logarithmic_correction_le (hw i hi) hz hrR) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Removing the pole sum leaves a uniformly bounded logarithmic-derivative error. -/
theorem norm_logDeriv_weighted_blaschke_product_sub_pole_sum_le {ι : Type*}
    (s : Finset ι) (w : ι → ℂ) (n : ι → ℕ) {R r : ℝ} {z : ℂ}
    (hw : ∀ i ∈ s, w i ∈ ball 0 R) (hz : z ∈ closedBall 0 r) (hrR : r < R)
    (hzw : ∀ i ∈ s, z ≠ w i) :
    ‖logDeriv (fun v => ∏ i ∈ s, blaschkeFactor R (w i) v ^ n i) z -
      ∑ i ∈ s, (n i : ℂ) / (z - w i)‖ ≤ (∑ i ∈ s, (n i : ℝ)) / (R - r) := by
  rw [logDeriv_weighted_blaschke_product s w n hw
    (closedBall_subset_closedBall hrR.le hz) hzw, add_sub_cancel_left]
  exact norm_weighted_blaschke_correction_sum_le s w n hw hz hrR

/-- A nonzero value is distinct from every point in the interior zero divisor. -/
theorem ne_of_mem_interior_divisor_support {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) {z u : ℂ} (hfz : f z ≠ 0)
    (hu : u ∈ (divisor f (ball 0 R)).support) : z ≠ u := by
  intro hzu
  subst u
  have hz := (divisor f (ball 0 R)).supportWithinDomain hu
  have hdiv : divisor f (ball 0 R) z = 0 := by
    rw [(hf.mono ball_subset_closedBall).divisor_apply hz,
      ((hf.mono ball_subset_closedBall) z hz).analyticOrderAt_eq_zero.mpr hfz]
    simp
  exact hu hdiv

/-- The natural multiplicity sum equals the integer mass of the interior divisor. -/
theorem sum_interior_divisor_multiplicities_eq {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    (∑ u ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
      ((divisor f (ball 0 R) u).toNat : ℝ)) =
        ((∑ᶠ u, divisor f (ball 0 R) u : ℤ) : ℝ) := by
  rw [finsum_eq_sum_of_support_subset_of_finite _ (subset_refl _)
    hf.meromorphicOn.divisor_ball_support_finite, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact_mod_cast Int.toNat_of_nonneg ((hf.mono ball_subset_closedBall).divisor_nonneg u)

/-- The interior multiplicity sum is bounded by the closed-disk divisor mass. -/
theorem sum_interior_divisor_multiplicities_le_closed_divisor {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    (∑ u ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
      ((divisor f (ball 0 R) u).toNat : ℝ)) ≤
        ((∑ᶠ u, divisor f (closedBall 0 R) u : ℤ) : ℝ) := by
  rw [sum_interior_divisor_multiplicities_eq hf]
  exact_mod_cast (show (∑ᶠ u, divisor f (ball 0 R) u) ≤
      ∑ᶠ u, divisor f (closedBall 0 R) u from by
    apply finsum_le_finsum hf.meromorphicOn.divisor_ball_support_finite
      ((divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall _ _))
    intro u
    by_cases hu : u ∈ ball (0 : ℂ) R
    · rw [(hf.mono ball_subset_closedBall).divisor_apply hu,
        hf.divisor_apply (ball_subset_closedBall hu)]
    · rw [(divisor f (ball 0 R)).apply_eq_zero_of_notMem hu]
      exact hf.divisor_nonneg u)

/-- The actual divisor product differs from its pole sum by at most the
interior multiplicity count divided by the distance to the outer circle. -/
theorem norm_logDeriv_finiteBlaschkeProduct_sub_pole_sum_le {f : ℂ → ℂ} {R r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) {z : ℂ}
    (hz : z ∈ closedBall 0 r) (hrR : r < R) (hfz : f z ≠ 0) :
    ‖logDeriv (finiteBlaschkeProduct f R) z -
      ∑ u ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
        ((divisor f (ball 0 R) u).toNat : ℂ) / (z - u)‖ ≤
      (∑ u ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
        ((divisor f (ball 0 R) u).toNat : ℝ)) / (R - r) := by
  have heq : finiteBlaschkeProduct f R = fun v =>
      ∏ u ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
        blaschkeFactor R u v ^ (divisor f (ball 0 R) u).toNat := by
    funext v
    exact finiteBlaschkeProduct_apply hf.meromorphicOn v
  rw [heq]
  apply norm_logDeriv_weighted_blaschke_product_sub_pole_sum_le
  · intro u hu
    exact (divisor f (ball 0 R)).supportWithinDomain
      (hf.meromorphicOn.divisor_ball_support_finite.mem_toFinset.mp hu)
  · exact hz
  · exact hrR
  · intro u hu
    exact ne_of_mem_interior_divisor_support hf hfz
      (hf.meromorphicOn.divisor_ball_support_finite.mem_toFinset.mp hu)

/-- Removing the interior Blaschke product can only increase the modulus. -/
theorem norm_le_blaschke_quotient_norm {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicOn f (closedBall 0 R)) (hR : 0 < R)
    (heq : ∀ z ∈ closedBall 0 R, f z = finiteBlaschkeProduct f R z * g z)
    {z : ℂ} (hz : z ∈ closedBall 0 R) : ‖f z‖ ≤ ‖g z‖ := by
  rw [heq z hz, norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_finiteBlaschkeProduct_le_one hf hR hz)
    (norm_nonneg _)).trans_eq (one_mul _)

/-- The disk maximum of the holomorphic quotient dominates that of the original function. -/
theorem diskNorm_le_blaschke_quotient_diskNorm {f g : ℂ → ℂ} {R r : ℝ}
    (hf : MeromorphicOn f (closedBall 0 R)) (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hg : ContinuousOn g (closedBall 0 r))
    (heq : ∀ z ∈ closedBall 0 R, f z = finiteBlaschkeProduct f R z * g z) :
    diskNorm f 0 r ≤ diskNorm g 0 r := by
  apply csSup_le
  · exact ⟨‖f 0‖, 0, mem_closedBall_self hr, rfl⟩
  · rintro y ⟨z, hz, rfl⟩
    exact (norm_le_blaschke_quotient_norm hf hR heq
      (closedBall_subset_closedBall hrR hz)).trans (norm_le_diskNorm hg hz)

/-- For an entire nonzero function the logarithmic derivative consists of its
interior pole sum, a Blaschke correction, and a zero-free quotient term. Growth
from the inner disk bounds the last term by `200 S/r`. -/
theorem norm_logDeriv_le_pole_sum_add_growth {f : ℂ → ℂ} {R r M S : ℝ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : f ≠ 0) (hr : 0 < r)
    (h2rR : 2 * r ≤ R) (hM : 0 < M)
    (hbound : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ M)
    (hgrowth : Real.log (M / diskNorm f 0 r) ≤ S) {z : ℂ}
    (hz : z ∈ closedBall 0 r) (hfz : f z ≠ 0) :
    ‖logDeriv f z‖ ≤
      ‖∑ u ∈ (hf.meromorphicOn.mono_set
          (subset_univ (closedBall (0 : ℂ) R))).divisor_ball_support_finite.toFinset,
        ((divisor f (ball 0 R) u).toNat : ℂ) / (z - u)‖ +
      (∑ u ∈ (hf.meromorphicOn.mono_set
          (subset_univ (closedBall (0 : ℂ) R))).divisor_ball_support_finite.toFinset,
        ((divisor f (ball 0 R) u).toNat : ℝ)) / (R - r) + 200 * S / r := by
  have hR : 0 < R := lt_of_lt_of_le (by linarith) h2rR
  have hrR : r < R := by linarith
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 R := closedBall_subset_ball hrR
  have hclosed : closedBall (0 : ℂ) r ⊆ closedBall 0 R :=
    closedBall_subset_closedBall hrR.le
  obtain ⟨g, hg, hg0, heq, _, hgbound⟩ :=
    exists_bounded_blaschke_factorization_of_entire hf hne hR hbound
  obtain ⟨v, hv, hfv, hmax⟩ := exists_max_norm_in_closedBall
    (hf.continuousOn.mono (subset_univ (closedBall (0 : ℂ) r)))
    (exists_ne_zero_in_closedBall hf hne 0 hr)
  have hfvpos := norm_pos_iff.mpr hfv
  have hgvpos := norm_pos_iff.mpr (hg0 v (hsub hv))
  have hfvle : ‖f v‖ ≤ ‖g v‖ :=
    norm_le_blaschke_quotient_norm (hf.meromorphicOn.mono_set (subset_univ _)) hR heq
      (hclosed hv)
  have hggrowth : Real.log (M / ‖g v‖) ≤ S := by
    have hratio := div_le_div_of_nonneg_left hM.le hfvpos hfvle
    have hlog := Real.log_le_log (div_pos hM hgvpos) hratio
    exact hlog.trans (by simpa only [diskNorm_eq_of_isMax hv hmax] using hgrowth)
  have htwor : ball (0 : ℂ) (2 * r) ⊆ ball 0 R := ball_subset_ball h2rR
  have hgder : ‖logDeriv g z‖ ≤ 200 * S / r :=
    norm_logarithmicDerivative_le_inner_disk hr hM
      (hg.mono (htwor.trans ball_subset_closedBall))
      (fun u hu => hg0 u (htwor hu))
      (fun u hu => hgbound u (ball_subset_closedBall (htwor hu))) hv hz hggrowth
  have hBz : finiteBlaschkeProduct f R z ≠ 0 := by
    have hprod : finiteBlaschkeProduct f R z * g z ≠ 0 := by rwa [← heq z (hclosed hz)]
    exact (mul_ne_zero_iff.mp hprod).1
  have hevent : f =ᶠ[𝓝 z] (fun u => finiteBlaschkeProduct f R u * g u) := by
    filter_upwards [isOpen_ball.mem_nhds (hsub hz)] with u hu
    exact heq u (ball_subset_closedBall hu)
  have hlogeq : logDeriv f z = logDeriv (finiteBlaschkeProduct f R) z + logDeriv g z := by
    have h := (logDeriv_congr_nhds hevent).self_of_nhds
    rw [logDeriv_fun_mul z hBz (hg0 z (hsub hz))
      ((analyticOnNhd_finiteBlaschkeProduct f R) z (hclosed hz)).differentiableAt
      (hg z (hclosed hz)).differentiableAt] at h
    exact h
  have hB := norm_logDeriv_finiteBlaschkeProduct_sub_pole_sum_le
    (hf.mono (subset_univ (closedBall (0 : ℂ) R))) hz hrR hfz
  have htriangle := norm_le_norm_sub_add (logDeriv (finiteBlaschkeProduct f R) z)
    (∑ u ∈ (hf.meromorphicOn.mono_set
        (subset_univ (closedBall (0 : ℂ) R))).divisor_ball_support_finite.toFinset,
      ((divisor f (ball 0 R) u).toNat : ℂ) / (z - u))
  rw [hlogeq]
  exact (norm_add_le _ _).trans (by linarith)

/-- A single Blaschke factor has norm at most one on the closed disk. -/
theorem norm_blaschkeFactor_le_one {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ closedBall 0 R) :
    ‖blaschkeFactor R w z‖ ≤ 1 :=
  norm_le_on_closedBall_of_sphere_bound (pos_of_mem_ball hw)
    (analyticOnNhd_blaschkeFactor hw)
    (fun _ hu => (norm_blaschkeFactor_on_sphere hw hu).le) hz

/-- In the radius-four disk, a factor on a radius-`r` disk centered within
distance one half of the origin is bounded by the clipped distance to its zero. -/
theorem norm_blaschkeFactor_four_le_clipped_distance {x w z : ℂ} {r : ℝ}
    (hw : w ∈ ball 0 4) (hx : ‖x‖ ≤ 1 / 2) (hz : z ∈ closedBall x r)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖blaschkeFactor 4 w z‖ ≤ max r (min 1 ‖x - w‖) := by
  have hzxr : ‖z - x‖ ≤ r := mem_closedBall_iff_norm.mp hz
  have hzsmall : ‖z‖ ≤ 3 / 2 := by
    have h := norm_le_norm_sub_add z x
    linarith
  have hzfour : z ∈ closedBall (0 : ℂ) 4 := mem_closedBall_zero_iff.mpr (by linarith)
  by_cases hd : ‖x - w‖ ≤ 1
  · rw [min_eq_right hd]
    have hwfour : ‖w‖ ≤ 4 := (mem_ball_zero_iff.mp hw).le
    have hden : 10 ≤ ‖(4 : ℂ) ^ 2 - conj w * z‖ := by
      have h := norm_sub_norm_le ((4 : ℂ) ^ 2) (conj w * z)
      norm_num [norm_mul] at h ⊢
      have hmul := mul_le_mul hwfour hzsmall (norm_nonneg z) (by norm_num : (0 : ℝ) ≤ 4)
      nlinarith
    have hnum : ‖z - w‖ ≤ r + ‖x - w‖ := by
      exact (norm_sub_le_norm_sub_add_norm_sub z x w).trans (add_le_add_left hzxr _)
    have hmax0 : 0 ≤ max r ‖x - w‖ := hr.trans (le_max_left _ _)
    have hmaxr := le_max_left r ‖x - w‖
    have hmaxd := le_max_right r ‖x - w‖
    rw [blaschkeFactor, norm_div, norm_mul]
    norm_num at hden ⊢
    rw [← le_max_iff]
    apply (div_le_iff₀ (by linarith : 0 < ‖(16 : ℂ) - conj w * z‖)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hden hmax0]
  · rw [min_eq_left (le_of_not_ge hd), max_eq_right hr1]
    exact norm_blaschkeFactor_le_one hw hzfour

/-- The clipped factor estimate multiplies with each zero's natural multiplicity. -/
theorem norm_weighted_blaschke_product_four_le {ι : Type*} (s : Finset ι)
    (w : ι → ℂ) (n : ι → ℕ) {x z : ℂ} {r : ℝ}
    (hw : ∀ i ∈ s, w i ∈ ball 0 4) (hx : ‖x‖ ≤ 1 / 2)
    (hz : z ∈ closedBall x r) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖∏ i ∈ s, blaschkeFactor 4 (w i) z ^ n i‖ ≤
      ∏ i ∈ s, (max r (min 1 ‖x - w i‖)) ^ n i := by
  rw [norm_prod]
  apply Finset.prod_le_prod₀
  · intro i _
    exact norm_nonneg _
  · intro i hi
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_blaschkeFactor_four_le_clipped_distance (hw i hi) hx hz hr hr1) _

/-- The actual interior divisor product satisfies the clipped-distance bound. -/
theorem norm_finiteBlaschkeProduct_four_le {f : ℂ → ℂ}
    (hf : MeromorphicOn f (closedBall 0 4)) {x z : ℂ} {r : ℝ}
    (hx : ‖x‖ ≤ 1 / 2) (hz : z ∈ closedBall x r) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖finiteBlaschkeProduct f 4 z‖ ≤
      ∏ u ∈ hf.divisor_ball_support_finite.toFinset,
        (max r (min 1 ‖x - u‖)) ^ (divisor f (ball 0 4) u).toNat := by
  rw [finiteBlaschkeProduct_apply hf]
  apply norm_weighted_blaschke_product_four_le
  · intro u hu
    exact (divisor f (ball 0 4)).supportWithinDomain
      (hf.divisor_ball_support_finite.mem_toFinset.mp hu)
  · exact hx
  · exact hz
  · exact hr
  · exact hr1

/-- A boundary majorant on the radius-four disk controls every small recentered
disk by the clipped distances to all interior zeros, with their multiplicities. -/
theorem diskNorm_le_clipped_interior_zero_product {f : ℂ → ℂ} {x : ℂ} {r M : ℝ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : f ≠ 0)
    (hbound : ∀ z ∈ sphere 0 4, ‖f z‖ ≤ M)
    (hx : ‖x‖ ≤ 1 / 2) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    diskNorm f x r ≤ M *
      ∏ u ∈ (hf.meromorphicOn.mono_set
          (subset_univ (closedBall (0 : ℂ) 4))).divisor_ball_support_finite.toFinset,
        (max r (min 1 ‖x - u‖)) ^ (divisor f (ball 0 4) u).toNat := by
  obtain ⟨g, _, _, heq, _, hgbound⟩ :=
    exists_bounded_blaschke_factorization_of_entire hf hne (by norm_num : (0 : ℝ) < 4) hbound
  let P := ∏ u ∈ (hf.meromorphicOn.mono_set
      (subset_univ (closedBall (0 : ℂ) 4))).divisor_ball_support_finite.toFinset,
    (max r (min 1 ‖x - u‖)) ^ (divisor f (ball 0 4) u).toNat
  have hP : 0 ≤ P := by
    apply Finset.prod_nonneg
    intro u _
    exact pow_nonneg (hr.trans (le_max_left _ _)) _
  apply csSup_le
  · exact ⟨‖f x‖, x, mem_closedBall_self hr, rfl⟩
  · rintro y ⟨z, hz, rfl⟩
    have hz4 : z ∈ closedBall (0 : ℂ) 4 := by
      have hzx := mem_closedBall_iff_norm.mp hz
      have htri := norm_le_norm_sub_add z x
      rw [mem_closedBall_zero_iff]
      linarith
    have hB := norm_finiteBlaschkeProduct_four_le
      (hf.meromorphicOn.mono_set (subset_univ (closedBall (0 : ℂ) 4))) hx hz hr hr1
    change ‖f z‖ ≤ M * P
    rw [heq z hz4, norm_mul]
    exact (mul_le_mul hB (hgbound z hz4) (norm_nonneg _) hP).trans_eq (mul_comm P M)

end Erdos522

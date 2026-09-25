/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.BlaschkeEstimates
import Erdos522.Analysis.ExponentialGrowth
import Erdos522.Analysis.LogarithmicPotential
import Erdos522.Analysis.MultiplicityLabels

/-!
# Logarithmic potentials of exponential-polynomial zeros

Growth between disks bounds the clipped logarithmic potential of the interior
zero divisor. The effective degree is the number of exponential terms minus
one, while every zero is retained with its analytic multiplicity.
-/

noncomputable section

open MeromorphicOn Metric Set
open scoped BigOperators

namespace Erdos522

/-- Every disk of positive radius has positive maximum modulus for an entire
nonzero function. -/
theorem diskNorm_pos_of_entire {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : f ≠ 0) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    0 < diskNorm f x r := by
  obtain ⟨z, hz, hfz⟩ := exists_ne_zero_in_closedBall hf hne x hr
  exact (norm_pos_iff.mpr hfz).trans_le
    (norm_le_diskNorm (hf.continuousOn.mono (subset_univ _)) hz)

/-- The logarithm of a clipped distance is the negative clipped potential. -/
theorem log_max_exp_neg_min_eq {d T : ℝ} (hd : 0 < d) (hT : 0 ≤ T) :
    Real.log (max (Real.exp (-T)) (min 1 d)) = -min T (max (-Real.log d) 0) := by
  have he : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hT)
  by_cases hd1 : d ≤ 1
  · rw [min_eq_right hd1]
    have hlog : Real.log d ≤ 0 := Real.log_nonpos hd.le hd1
    rw [max_eq_left (neg_nonneg.mpr hlog)]
    by_cases hed : Real.exp (-T) ≤ d
    · rw [max_eq_right hed]
      have h := (Real.le_log_iff_exp_le hd).mpr hed
      rw [min_eq_right (by linarith : -Real.log d ≤ T)]
      ring
    · have hde : d ≤ Real.exp (-T) := (lt_of_not_ge hed).le
      rw [max_eq_left hde, Real.log_exp]
      have h := (Real.log_le_iff_le_exp hd).mpr hde
      rw [min_eq_left (by linarith : T ≤ -Real.log d)]
  · have h1d : 1 ≤ d := le_of_not_ge hd1
    rw [min_eq_left h1d, max_eq_right he, Real.log_one]
    have hlog : 0 ≤ Real.log d := Real.log_nonneg h1d
    rw [max_eq_right (neg_nonpos.mpr hlog), min_eq_right hT, neg_zero]

/-- A real-point version in the logarithmic-potential notation. -/
theorem log_clipped_distance_eq_negative_clipped_potential {u : ℂ} {x T : ℝ}
    (hxu : (x : ℂ) ≠ u) (hT : 0 ≤ T) :
    Real.log (max (Real.exp (-T)) (min 1 ‖(x : ℂ) - u‖)) =
      -min T (negativeLogPotential u x) :=
  log_max_exp_neg_min_eq (norm_pos_iff.mpr (sub_ne_zero.mpr hxu)) hT

/-- Growth from a small disk centered near the origin controls the full
radius-four disk, with outer recentered radius five. -/
theorem diskNorm_four_le_recentered_exponential_growth {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ)
    (hne : complexExponentialSum s c ζ ≠ 0) {σ r : ℝ} {x : ℂ}
    (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, ‖ζ j‖ ≤ σ)
    (hx : ‖x‖ ≤ 1 / 2) (hr : 0 < r) (hr1 : r ≤ 1) :
    diskNorm (complexExponentialSum s c ζ) 0 4 ≤
      Real.exp (5 * σ) * (40 * Real.exp 1 / r) ^ (s.card - 1) *
        diskNorm (complexExponentialSum s c ζ) x r := by
  have hf := analyticOnNhd_complexExponentialSum s c ζ
  have hsmallpos := diskNorm_pos_of_entire hf hne x hr
  apply csSup_le
  · exact ⟨‖complexExponentialSum s c ζ 0‖, 0, mem_closedBall_self (by norm_num), rfl⟩
  · rintro y ⟨z, hz, rfl⟩
    have hz5 : dist z x ≤ 5 := by
      have hz4 := mem_closedBall_zero_iff.mp hz
      rw [dist_eq_norm]
      have h := norm_sub_le z x
      linarith
    have h := norm_complexExponentialSum_le_disk_universal s hs c ζ hσ hζ hr
      (by linarith : r ≤ 5) hsmallpos.le x z
      (fun w hw => norm_le_diskNorm (hf.continuousOn.mono (subset_univ _)) hw) hz5
    rw [show σ * 5 = 5 * σ by ring,
      show 8 * Real.exp 1 * 5 / r = 40 * Real.exp 1 / r by ring] at h
    convert h using 1
    ring

/-- The total interior-four zero multiplicity is linear in spectral radius
and term count. -/
theorem interior_four_zero_mass_complexExponentialSum_le {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ)
    (hne : complexExponentialSum s c ζ ≠ 0) {σ : ℝ}
    (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, ‖ζ j‖ ≤ σ) :
    (∑ u ∈ ((analyticOnNhd_complexExponentialSum s c ζ).meromorphicOn.mono_set
        (subset_univ (closedBall (0 : ℂ) 4))).divisor_ball_support_finite.toFinset,
      ((divisor (complexExponentialSum s c ζ) (ball 0 4) u).toNat : ℝ)) ≤
      48 * σ + 18 * ((s.card : ℝ) - 1) := by
  have h := sum_interior_divisor_multiplicities_le_closed_divisor
    ((analyticOnNhd_complexExponentialSum s c ζ).mono (subset_univ (closedBall (0 : ℂ) 4)))
  refine h.trans ?_
  convert sum_divisor_complexExponentialSum_le_linear_explicit s hs c ζ hne hσ hζ
    (by norm_num : (0 : ℝ) < 4) 0 using 1
  ring

/-- The clipped logarithmic potential of all interior-four zeros has effective
degree equal to the term count minus one. -/
theorem clipped_interior_zero_potential_complexExponentialSum_le {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ)
    (hne : complexExponentialSum s c ζ ≠ 0) {σ x T : ℝ}
    (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, ‖ζ j‖ ≤ σ)
    (hx : |x| ≤ 1 / 2) (hT : 0 ≤ T) (hfx : complexExponentialSum s c ζ x ≠ 0) :
    (∑ u ∈ ((analyticOnNhd_complexExponentialSum s c ζ).meromorphicOn.mono_set
        (subset_univ (closedBall (0 : ℂ) 4))).divisor_ball_support_finite.toFinset,
      ((divisor (complexExponentialSum s c ζ) (ball 0 4) u).toNat : ℝ) *
        min T (negativeLogPotential u x)) ≤
      5 * σ + ((s.card : ℝ) - 1) * Real.log (40 * Real.exp 1) +
        ((s.card : ℝ) - 1) * T := by
  let f := complexExponentialSum s c ζ
  have hf := analyticOnNhd_complexExponentialSum s c ζ
  let Z := (hf.meromorphicOn.mono_set
    (subset_univ (closedBall (0 : ℂ) 4))).divisor_ball_support_finite.toFinset
  let n := fun u => (divisor f (ball 0 4) u).toNat
  let r := Real.exp (-T)
  let A := Real.exp (5 * σ) * (40 * Real.exp 1 / r) ^ (s.card - 1)
  let P := ∏ u ∈ Z, (max r (min 1 ‖(x : ℂ) - u‖)) ^ n u
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hT)
  have hx' : ‖(x : ℂ)‖ ≤ 1 / 2 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx
  have hM4 : 0 < diskNorm f 0 4 := diskNorm_pos_of_entire hf hne 0 (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  have hP : 0 < P := by
    apply Finset.prod_pos
    intro u _
    exact pow_pos (hr.trans_le (le_max_left _ _)) _
  have hsmall : diskNorm f x r ≤ diskNorm f 0 4 * P :=
    diskNorm_le_clipped_interior_zero_product hf hne
      (fun z hz => norm_le_diskNorm (hf.continuousOn.mono (subset_univ _))
        (sphere_subset_closedBall hz)) hx' hr.le hr1
  have hgrowth : diskNorm f 0 4 ≤ A * diskNorm f x r :=
    diskNorm_four_le_recentered_exponential_growth s hs c ζ hne hσ hζ hx' hr hr1
  have hAP : 1 ≤ A * P := by
    have h := hgrowth.trans (mul_le_mul_of_nonneg_left hsmall hA.le)
    nlinarith
  have hlog : 0 ≤ Real.log A + Real.log P := by
    rw [← Real.log_mul hA.ne' hP.ne']
    exact Real.log_nonneg hAP
  have hn : 1 ≤ s.card := Finset.one_le_card.mpr hs
  have hlogA : Real.log A =
      5 * σ + ((s.card : ℝ) - 1) * Real.log (40 * Real.exp 1) +
        ((s.card : ℝ) - 1) * T := by
    dsimp [A]
    rw [Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ (by positivity)),
      Real.log_exp, Real.log_pow, Real.log_div (by positivity) hr.ne',
      show Real.log r = -T from Real.log_exp _, Nat.cast_sub hn, Nat.cast_one]
    ring
  have hlogP : Real.log P = -(∑ u ∈ Z, (n u : ℝ) * min T (negativeLogPotential u x)) := by
    dsimp [P]
    rw [Real.log_prod (fun u _ => pow_ne_zero _ (ne_of_gt (hr.trans_le (le_max_left _ _)))),
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    have hxu : (x : ℂ) ≠ u := ne_of_mem_interior_divisor_support
      (hf.mono (subset_univ (closedBall (0 : ℂ) 4))) hfx
      ((hf.meromorphicOn.mono_set
        (subset_univ (closedBall (0 : ℂ) 4))).divisor_ball_support_finite.mem_toFinset.mp hu)
    rw [Real.log_pow, log_clipped_distance_eq_negative_clipped_potential hxu hT]
    ring
  rw [hlogA, hlogP] at hlog
  change (∑ u ∈ Z, (n u : ℝ) * min T (negativeLogPotential u x)) ≤ _
  linarith

/-- On the unit interval the negative logarithm of the radius-four Blaschke
product is bounded by the zero potentials plus `log 5` per multiplicity. -/
theorem negative_log_norm_finiteBlaschkeProduct_four_le_potential
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 4)) {x : ℝ}
    (hx : |x| ≤ 1) (hfx : f x ≠ 0) :
    -Real.log ‖finiteBlaschkeProduct f 4 x‖ ≤
      (∑ u ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
        ((divisor f (ball 0 4) u).toNat : ℝ)) * Real.log 5 +
      ∑ u ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
        ((divisor f (ball 0 4) u).toNat : ℝ) * negativeLogPotential u x := by
  let Z := hf.meromorphicOn.divisor_ball_support_finite.toFinset
  let n := fun u => (divisor f (ball 0 4) u).toNat
  let P := ∏ u ∈ Z, (‖(x : ℂ) - u‖ / 5) ^ n u
  have hdist (u : ℂ) (hu : u ∈ Z) : 0 < ‖(x : ℂ) - u‖ := by
    apply norm_pos_iff.mpr
    exact sub_ne_zero.mpr (ne_of_mem_interior_divisor_support hf hfx
      (hf.meromorphicOn.divisor_ball_support_finite.mem_toFinset.mp hu))
  have hP : 0 < P := Finset.prod_pos fun u hu =>
    pow_pos (div_pos (hdist u hu) (by norm_num)) _
  have hB : P ≤ ‖finiteBlaschkeProduct f 4 x‖ := by
    rw [finiteBlaschkeProduct_apply hf.meromorphicOn]
    convert norm_weighted_blaschke_product_ge Z id n
      (fun u hu => (divisor f (ball 0 4)).supportWithinDomain
        (hf.meromorphicOn.divisor_ball_support_finite.mem_toFinset.mp hu))
      (show (x : ℂ) ∈ closedBall 0 1 by
        simpa only [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hx)
      (by norm_num : (1 : ℝ) ≤ 4) using 1 <;> norm_num [P, Z, n]
  have hlogB := Real.log_le_log hP hB
  have hlogP : -Real.log P ≤ (∑ u ∈ Z, (n u : ℝ)) * Real.log 5 +
      ∑ u ∈ Z, (n u : ℝ) * negativeLogPotential u x := by
    dsimp [P]
    rw [Real.log_prod (fun u hu => pow_ne_zero _ (ne_of_gt (div_pos (hdist u hu) (by norm_num)))),
      ← Finset.sum_neg_distrib, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u hu
    rw [Real.log_pow, Real.log_div (hdist u hu).ne' (by norm_num)]
    have hpot : -Real.log ‖(x : ℂ) - u‖ ≤ negativeLogPotential u x := le_max_left _ _
    nlinarith [mul_le_mul_of_nonneg_left hpot (Nat.cast_nonneg (n u) : (0 : ℝ) ≤ n u)]
  exact (neg_le_neg hlogB).trans hlogP

/-- A boundary majorant and inner-disk growth control the full logarithmic
defect by the zero potentials, with the exact Harnack constant `25`. -/
theorem log_diskNorm_sub_log_norm_le_zero_potential {f : ℂ → ℂ} {M H : ℝ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : f ≠ 0) (hM : 0 < M)
    (hbound : ∀ z ∈ sphere 0 4, ‖f z‖ ≤ M)
    (hgrowth : Real.log (M / diskNorm f 0 1) ≤ H) {x : ℝ}
    (hx : |x| ≤ 1) (hfx : f x ≠ 0) :
    Real.log (diskNorm f 0 1) - Real.log ‖f x‖ ≤ 25 * H +
      (∑ u ∈ (hf.meromorphicOn.mono_set
          (subset_univ (closedBall (0 : ℂ) 4))).divisor_ball_support_finite.toFinset,
        ((divisor f (ball 0 4) u).toNat : ℝ)) * Real.log 5 +
      ∑ u ∈ (hf.meromorphicOn.mono_set
          (subset_univ (closedBall (0 : ℂ) 4))).divisor_ball_support_finite.toFinset,
        ((divisor f (ball 0 4) u).toNat : ℝ) * negativeLogPotential u x := by
  obtain ⟨g, hg, hg0, heq, _, hgbound⟩ :=
    exists_bounded_blaschke_factorization_of_entire hf hne (by norm_num : (0 : ℝ) < 4) hbound
  obtain ⟨v, hv, hfv, hmax⟩ := exists_max_norm_in_closedBall
    (hf.continuousOn.mono (subset_univ (closedBall (0 : ℂ) 1)))
    (exists_ne_zero_in_closedBall hf hne 0 (by norm_num : (0 : ℝ) < 1))
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 4 := closedBall_subset_ball (by norm_num)
  have hsub2 : ball (0 : ℂ) 2 ⊆ ball 0 4 := ball_subset_ball (by norm_num)
  have hx1 : (x : ℂ) ∈ closedBall 0 1 := by
    simpa only [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hx
  have hfvgv := norm_le_blaschke_quotient_norm
    (hf.meromorphicOn.mono_set (subset_univ _)) (by norm_num : (0 : ℝ) < 4) heq
    (ball_subset_closedBall (hsub hv))
  have hgvpos := norm_pos_iff.mpr (hg0 v (hsub hv))
  have hggrowth : Real.log (M / ‖g v‖) ≤ H := by
    have hratio := div_le_div_of_nonneg_left hM.le (norm_pos_iff.mpr hfv) hfvgv
    exact (Real.log_le_log (div_pos hM hgvpos) hratio).trans
      (by simpa only [diskNorm_eq_of_isMax hv hmax] using hgrowth)
  have hglower := norm_ge_of_zero_free_logarithmic_growth hM
    (hg.mono (hsub2.trans ball_subset_closedBall)) (fun z hz => hg0 z (hsub2 hz))
    (fun z hz => hgbound z (ball_subset_closedBall (hsub2 hz))) hv hx1 hggrowth
  have hglog : Real.log M - Real.log ‖g x‖ ≤ 25 * H := by
    have h := Real.log_le_log (mul_pos hM (Real.exp_pos _)) hglower
    rw [Real.log_mul hM.ne' (Real.exp_ne_zero _), Real.log_exp] at h
    linarith
  have hM1 : Real.log (diskNorm f 0 1) ≤ Real.log M := by
    rw [diskNorm_eq_of_isMax hv hmax]
    exact Real.log_le_log (norm_pos_iff.mpr hfv)
      (hfvgv.trans (hgbound v (ball_subset_closedBall (hsub hv))))
  have hx4 := ball_subset_closedBall (hsub hx1)
  have hBne : finiteBlaschkeProduct f 4 x ≠ 0 := by
    have hp : finiteBlaschkeProduct f 4 x * g x ≠ 0 := by rwa [← heq x hx4]
    exact (mul_ne_zero_iff.mp hp).1
  have hlogfx : Real.log ‖f x‖ =
      Real.log ‖finiteBlaschkeProduct f 4 x‖ + Real.log ‖g x‖ := by
    rw [heq x hx4, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hBne)
      (norm_ne_zero_iff.mpr (hg0 x (hsub hx1)))]
  have hB := negative_log_norm_finiteBlaschkeProduct_four_le_potential
    (hf.mono (subset_univ _)) hx hfx
  rw [hlogfx]
  linarith

/-- Bounded spectrum controls the pointwise logarithmic defect through the
full interior-zero potential. -/
theorem log_diskNorm_sub_log_norm_complexExponentialSum_le {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ)
    (hne : complexExponentialSum s c ζ ≠ 0) {σ x : ℝ}
    (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, ‖ζ j‖ ≤ σ)
    (hx : |x| ≤ 1) (hfx : complexExponentialSum s c ζ x ≠ 0) :
    Real.log (diskNorm (complexExponentialSum s c ζ) 0 1) -
      Real.log ‖complexExponentialSum s c ζ x‖ ≤
      25 * (4 * σ + ((s.card : ℝ) - 1) * Real.log (32 * Real.exp 1)) +
      (∑ u ∈ ((analyticOnNhd_complexExponentialSum s c ζ).meromorphicOn.mono_set
          (subset_univ (closedBall (0 : ℂ) 4))).divisor_ball_support_finite.toFinset,
        ((divisor (complexExponentialSum s c ζ) (ball 0 4) u).toNat : ℝ)) * Real.log 5 +
      ∑ u ∈ ((analyticOnNhd_complexExponentialSum s c ζ).meromorphicOn.mono_set
          (subset_univ (closedBall (0 : ℂ) 4))).divisor_ball_support_finite.toFinset,
        ((divisor (complexExponentialSum s c ζ) (ball 0 4) u).toNat : ℝ) *
          negativeLogPotential u x := by
  let f := complexExponentialSum s c ζ
  have hf := analyticOnNhd_complexExponentialSum s c ζ
  let M₁ := diskNorm f 0 1
  have hM₁ : 0 < M₁ := diskNorm_pos_of_entire hf hne 0 (by norm_num)
  let M := Real.exp (4 * σ) * M₁ * (32 * Real.exp 1) ^ (s.card - 1)
  have hM : 0 < M := by dsimp [M]; positivity
  have hbound : ∀ z ∈ sphere (0 : ℂ) 4, ‖f z‖ ≤ M := by
    intro z hz
    have h := norm_complexExponentialSum_le_disk_universal s hs c ζ hσ hζ
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 4) hM₁.le 0 z
      (fun w hw => norm_le_diskNorm (hf.continuousOn.mono (subset_univ _)) hw)
      (sphere_subset_closedBall hz)
    simpa only [M, mul_one, div_one, show 8 * Real.exp 1 * 4 = 32 * Real.exp 1 by ring,
      show σ * 4 = 4 * σ by ring] using h
  have hgrowth : Real.log (M / diskNorm f 0 1) ≤
      4 * σ + ((s.card : ℝ) - 1) * Real.log (32 * Real.exp 1) := by
    have heq : M / diskNorm f 0 1 =
        Real.exp (4 * σ) * (32 * Real.exp 1) ^ (s.card - 1) := by
      dsimp [M, M₁]
      field_simp [hM₁.ne']
      exact div_self hM₁.ne'
    rw [heq, Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ (by positivity)),
      Real.log_exp, Real.log_pow, Nat.cast_sub (Finset.one_le_card.mpr hs), Nat.cast_one]
  exact log_diskNorm_sub_log_norm_le_zero_potential hf hne hM hbound hgrowth hx hfx

/-- One fixed labelled zero family simultaneously represents the mass bound,
the pointwise defect, and every clipped-potential inequality. -/
theorem exists_complexExponentialSum_zero_potential_labels {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ)
    (hne : complexExponentialSum s c ζ ≠ 0) {σ : ℝ}
    (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, ‖ζ j‖ ≤ σ) :
    ∃ N : ℕ, ∃ w : Fin N → ℂ,
      (N : ℝ) ≤ 48 * σ + 18 * ((s.card : ℝ) - 1) ∧
      (∀ x : ℝ, |x| ≤ 1 → complexExponentialSum s c ζ x ≠ 0 →
        Real.log (diskNorm (complexExponentialSum s c ζ) 0 1) -
          Real.log ‖complexExponentialSum s c ζ x‖ ≤
          25 * (4 * σ + ((s.card : ℝ) - 1) * Real.log (32 * Real.exp 1)) +
            N * Real.log 5 + ∑ i, negativeLogPotential (w i) x) ∧
      (∀ x : ℝ, |x| ≤ 1 / 2 → complexExponentialSum s c ζ x ≠ 0 →
        ∀ T : ℝ, 0 ≤ T → (∑ i, min T (negativeLogPotential (w i) x)) ≤
          5 * σ + ((s.card : ℝ) - 1) * Real.log (40 * Real.exp 1) +
            ((s.card : ℝ) - 1) * T) := by
  have hf := analyticOnNhd_complexExponentialSum s c ζ
  let Z := (hf.meromorphicOn.mono_set
    (subset_univ (closedBall (0 : ℂ) 4))).divisor_ball_support_finite.toFinset
  let n := fun u => (divisor (complexExponentialSum s c ζ) (ball 0 4) u).toNat
  let N := multiplicityLabelCount Z n
  let w := multiplicityLabel Z n
  have hN : (N : ℝ) = ∑ u ∈ Z, (n u : ℝ) := by
    dsimp [N]
    rw [multiplicityLabelCount_eq_sum, Nat.cast_sum]
  have hsum (p : ℂ → ℝ) : (∑ i, p (w i)) = ∑ u ∈ Z, (n u : ℝ) * p u := by
    simpa only [w, nsmul_eq_mul] using sum_multiplicityLabel Z n p
  refine ⟨N, w, ?_, ?_, ?_⟩
  · rw [hN]
    exact interior_four_zero_mass_complexExponentialSum_le s hs c ζ hne hσ hζ
  · intro x hx hfx
    rw [hsum (fun u => negativeLogPotential u x), hN]
    exact log_diskNorm_sub_log_norm_complexExponentialSum_le s hs c ζ hne hσ hζ hx hfx
  · intro x hx hfx T hT
    rw [hsum (fun u => min T (negativeLogPotential u x))]
    exact clipped_interior_zero_potential_complexExponentialSum_le s hs c ζ hne hσ hζ hx hT hfx

end Erdos522

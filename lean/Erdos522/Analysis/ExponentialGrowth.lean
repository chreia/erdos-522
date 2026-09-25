/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ExponentialRecurrence
import Erdos522.Analysis.ExponentialZeroCount

/-!
# Universal exponential growth and linear zero counts

The binomial recurrence controls growth between concentric disks with a base
independent of the number of frequencies. Jensen's formula then bounds the
multiplicity-counted number of zeros by a linear function of the spectral
radius and the number of terms.
-/

noncomputable section
open MeromorphicOn Metric Set
namespace Erdos522

/-- An exponential polynomial on a larger complex disk is controlled by its
values on a concentric smaller disk, with the spectral radius recorded
explicitly in the exponential growth factor. -/
theorem norm_complexExponentialSum_le_disk_universal {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ)
    {σ r R M : ℝ} (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, ‖ζ j‖ ≤ σ)
    (hr : 0 < r) (hrR : r ≤ R) (hM : 0 ≤ M) (z₀ z : ℂ)
    (hsmall : ∀ w : ℂ, dist w z₀ ≤ r → ‖complexExponentialSum s c ζ w‖ ≤ M)
    (hz : dist z z₀ ≤ R) :
    ‖complexExponentialSum s c ζ z‖ ≤
      Real.exp (σ * R) * M * (8 * Real.exp 1 * R / r) ^ (s.card - 1) := by
  let θ : ℂ := NormedSpace.normalize (z - z₀)
  let t : ℝ := ‖z - z₀‖
  have hθ : ‖θ‖ ≤ 1 := by
    by_cases h : z - z₀ = 0
    · simp [θ, h]
    · exact (NormedSpace.norm_normalize h).le
  have hray : z₀ + θ * (t : ℂ) = z := by
    have h := NormedSpace.norm_smul_normalize (z - z₀)
    change (t : ℂ) * θ = z - z₀ at h
    rw [mul_comm, h]
    abel
  have hfreq : ∀ j ∈ s, (ζ j * θ).re ≤ σ := by
    intro j hj
    calc
      _ ≤ ‖ζ j * θ‖ := Complex.re_le_norm _
      _ = ‖ζ j‖ * ‖θ‖ := norm_mul _ _
      _ ≤ ‖ζ j‖ * 1 := mul_le_mul_of_nonneg_left hθ (norm_nonneg _)
      _ ≤ σ := by simpa only [mul_one] using hζ j hj
  have hinit : ∀ y ∈ Set.Icc (0 : ℝ) (0 + r),
      ‖complexExponentialSum s (fun j => c j * Complex.exp (ζ j * z₀))
        (fun j => ζ j * θ) y‖ ≤ M := by
    intro y hy
    rw [← complexExponentialSum_ray]
    apply hsmall
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hy.1]
    have hmul := mul_le_mul_of_nonneg_right hθ hy.1
    linarith [hy.2]
  have hpoint : t ∈ Set.Icc (0 : ℝ) (0 + R) := by
    constructor
    · exact norm_nonneg _
    · simpa only [t, dist_eq_norm, zero_add] using hz
  have h := norm_complexExponentialSum_le_interval_universal s hs
    (fun j => c j * Complex.exp (ζ j * z₀)) (fun j => ζ j * θ)
    hσ hfreq hr hrR hM hinit hpoint
  rw [← complexExponentialSum_ray, hray] at h
  exact h


/-- Jensen's bound for all zeros in a closed disk. The bound is linear in the number of terms, including when exponents
coincide or coefficients vanish. -/
theorem sum_divisor_complexExponentialSum_le_linear {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ)
    (hne : complexExponentialSum s c ζ ≠ 0)
    {σ r : ℝ} (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, ‖ζ j‖ ≤ σ) (hr : 0 < r) (z₀ : ℂ) :
    ((∑ᶠ z, divisor (complexExponentialSum s c ζ) (closedBall z₀ r) z : ℤ) : ℝ) ≤
      (4 * σ * r + ((s.card : ℝ) - 1) * Real.log (32 * Real.exp 1)) /
        Real.log ((3 : ℝ) / 2) := by
  let f := complexExponentialSum s c ζ
  let A : ℝ := Real.exp (4 * σ * r) * (32 * Real.exp 1) ^ (s.card - 1)
  have hn : 1 ≤ s.card := Finset.one_le_card.mpr hs
  have hA : 0 < A := by dsimp [A]; positivity
  have hf := analyticOnNhd_complexExponentialSum s c ζ
  have hfsmall : ContinuousOn f (closedBall z₀ r) := hf.continuousOn.mono (subset_univ _)
  obtain ⟨u, hu, hfu, hmax⟩ := exists_max_norm_in_closedBall hfsmall
    (complexExponentialSum_ne_zero_in_closedBall s c ζ hne z₀ hr)
  have hbound : ∀ z ∈ closedBall z₀ (4 * r), ‖f z‖ ≤ A * ‖f u‖ := by
    intro z hz
    have h := norm_complexExponentialSum_le_disk_universal s hs c ζ hσ hζ hr
      (show r ≤ 4 * r by linarith) (norm_nonneg (f u)) z₀ z
      (fun w hw => hmax w hw) hz
    have hratio : 8 * Real.exp 1 * (4 * r) / r = 32 * Real.exp 1 := by
      field_simp
      ring
    rw [hratio] at h
    have hexp : σ * (4 * r) = 4 * σ * r := by ring
    rw [hexp] at h
    dsimp [A]
    nlinarith
  have hj := sum_divisor_le_of_recentered_growth hr hA
    (hf.mono (subset_univ _)) hu hfu hbound
  have hlog : Real.log A =
      4 * σ * r + ((s.card : ℝ) - 1) * Real.log (32 * Real.exp 1) := by
    dsimp [A]
    rw [Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ (by positivity)),
      Real.log_exp, Real.log_pow, Nat.cast_sub hn, Nat.cast_one]
  rw [hlog] at hj
  exact hj

/-- A numerical zero-count bound linear in both spectral radius and term count. -/
theorem sum_divisor_complexExponentialSum_le_linear_explicit {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ)
    (hne : complexExponentialSum s c ζ ≠ 0)
    {σ r : ℝ} (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, ‖ζ j‖ ≤ σ) (hr : 0 < r) (z₀ : ℂ) :
    ((∑ᶠ z, divisor (complexExponentialSum s c ζ) (closedBall z₀ r) z : ℤ) : ℝ) ≤
      12 * σ * r + 18 * ((s.card : ℝ) - 1) := by
  have hn : (1 : ℝ) ≤ s.card := by exact_mod_cast Finset.one_le_card.mpr hs
  have hlog : (1 : ℝ) / 3 ≤ Real.log ((3 : ℝ) / 2) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlogpos : 0 < Real.log ((3 : ℝ) / 2) := by linarith
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hlognonneg : 0 ≤ Real.log (32 * Real.exp 1) := Real.log_nonneg (by linarith)
  have hlogupper : Real.log (32 * Real.exp 1) ≤ 6 := by
    have h2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp,
      show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hnumer : 4 * σ * r + ((s.card : ℝ) - 1) * Real.log (32 * Real.exp 1) ≤
      4 * σ * r + 6 * ((s.card : ℝ) - 1) := by
    nlinarith
  refine (sum_divisor_complexExponentialSum_le_linear s hs c ζ hne hσ hζ hr z₀).trans ?_
  apply (div_le_iff₀ hlogpos).mpr
  have hnonneg : 0 ≤ 12 * σ * r + 18 * ((s.card : ℝ) - 1) := by positivity
  nlinarith

/-- The real harmonic normalization uses the exact angular multiplier `2πi`. -/
theorem finiteExponentialSum_eq_complexExponentialSum {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) (x : ℝ) :
    finiteExponentialSum s c ν x =
      complexExponentialSum s c (fun j => frequencyMultiplier (ν j)) x := by
  apply Finset.sum_congr rfl
  intro j _
  simp only [angularCharacter, fourier_coe_apply, frequencyMultiplier,
    Int.cast_one, Complex.ofReal_one, mul_one, div_one, Complex.ofReal_mul]
  congr 2
  ring

/-- Harmonic interval propagation with a universal base. -/
theorem norm_finiteExponentialSum_le_initial_interval_universal {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c : ι → ℂ) (ν : ι → ℝ)
    {a l L M x : ℝ} (hl : 0 < l) (hlL : l ≤ L) (hM : 0 ≤ M)
    (hinit : ∀ y ∈ Set.Icc a (a + l), ‖finiteExponentialSum s c ν y‖ ≤ M)
    (hx : x ∈ Set.Icc a (a + L)) :
    ‖finiteExponentialSum s c ν x‖ ≤
      M * (8 * Real.exp 1 * L / l) ^ (s.card - 1) := by
  simp_rw [finiteExponentialSum_eq_complexExponentialSum] at hinit ⊢
  have h := norm_complexExponentialSum_le_interval_universal s hs c
    (fun j => frequencyMultiplier (ν j)) (σ := 0) (by norm_num)
    (by intro j _; simp [frequencyMultiplier, Complex.mul_re]) hl hlL hM hinit hx
  simpa only [zero_mul, Real.exp_zero, one_mul] using h

/-- The interval form of a harmonic Turán estimate. Frequencies need not be
separated or distinct; the bound counts the terms in the supplied sum. -/
theorem norm_finiteExponentialSum_le_subinterval_universal {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c : ι → ℂ) (ν : ι → ℝ)
    {A B a b M x : ℝ} (ha : A ≤ a) (hab : a < b) (hb : b ≤ B) (hM : 0 ≤ M)
    (hsmall : ∀ y ∈ Set.Icc a b, ‖finiteExponentialSum s c ν y‖ ≤ M)
    (hx : x ∈ Set.Icc A B) :
    ‖finiteExponentialSum s c ν x‖ ≤
      M * (8 * Real.exp 1 * (B - A) / (b - a)) ^ (s.card - 1) := by
  have hl : 0 < b - a := sub_pos.mpr hab
  have hlL : b - a ≤ B - A := by linarith
  by_cases hax : a ≤ x
  · apply norm_finiteExponentialSum_le_initial_interval_universal s hs c ν
      (a := a) (l := b - a) (L := B - A) (x := x) hl hlL hM
    · intro y hy
      apply hsmall y
      constructor <;> linarith [hy.1, hy.2]
    · constructor <;> linarith [hx.2]
  · have hr := norm_finiteExponentialSum_le_initial_interval_universal s hs c (fun j => -ν j)
      (a := -b) (l := b - a) (L := B - A) (x := -x) hl hlL hM
    have hsmall' : ∀ y ∈ Set.Icc (-b) (-b + (b - a)),
        ‖finiteExponentialSum s c (fun j => -ν j) y‖ ≤ M := by
      intro y hy
      rw [← finiteExponentialSum_neg]
      apply hsmall (-y)
      constructor <;> linarith [hy.1, hy.2]
    have hpoint : -x ∈ Set.Icc (-b) (-b + (B - A)) := by
      constructor <;> linarith [hx.1]
    simpa only [← finiteExponentialSum_neg, neg_neg] using hr hsmall' hpoint


end Erdos522

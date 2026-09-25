/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.DiscreteExponentialSums
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Exponential propagation and growth on complex disks

Contracting geometric modes satisfy the same finite-difference induction as
unit-modulus modes. Rescaling by a common modulus bound introduces an explicit
exponential growth factor. Applying the resulting interval estimate along a
complex ray bounds an exponential polynomial on concentric disks.
-/

noncomputable section
open scoped BigOperators
namespace Erdos522

/-- A contracting multiplier does not increase the accumulated first-order error. -/
theorem norm_le_initial_add_sum_difference_of_norm_le_one (f : ℕ → ℂ) (z : ℂ)
    (hz : ‖z‖ ≤ 1) (k : ℕ) :
    ‖f k‖ ≤ ‖f 0‖ + ∑ j ∈ Finset.range k, ‖f (j + 1) - z * f j‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h := norm_add_le (z * f k) (f (k + 1) - z * f k)
      rw [show z * f k + (f (k + 1) - z * f k) = f (k + 1) by ring,
        norm_mul] at h
      have hm := mul_le_mul_of_nonneg_right hz (norm_nonneg (f k))
      rw [Finset.sum_range_succ]
      nlinarith

/-- Initial values of a finite contracting geometric sum control all later
values, with a bound independent of the locations of its modes. -/
theorem norm_geometricSum_le_of_norm_le_one {ι : Type*} (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ j ∈ s, ‖z j‖ ≤ 1) {M : ℝ} (hM : 0 ≤ M)
    (hinit : ∀ k < s.card, ‖geometricSum s c z k‖ ≤ M) (k : ℕ) :
    ‖geometricSum s c z k‖ ≤ M * (2 * ((k : ℝ) + 1)) ^ (s.card - 1) := by
  classical
  induction s using Finset.induction generalizing c M k with
  | empty => simp [geometricSum, hM]
  | @insert a s ha ih =>
      by_cases hs : s = ∅
      · subst s
        have h0 := hinit 0 (by simp)
        have hca : ‖c a‖ ≤ M := by simpa [geometricSum] using h0
        have hp : ‖z a‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) (hz a (by simp))
        simpa [geometricSum, norm_mul, norm_pow] using
          (mul_le_mul_of_nonneg_left hp (norm_nonneg (c a))).trans (by simpa using hca)
      · have hn : 1 ≤ s.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
        have hza : ‖z a‖ ≤ 1 := hz a (Finset.mem_insert_self _ _)
        let f : ℕ → ℂ := geometricSum (insert a s) c z
        let d : ι → ℂ := fun j => c j * (z j - z a)
        have hd (j : ℕ) : geometricSum s d z j = f (j + 1) - z a * f j :=
          (geometricSum_difference_insert s a ha c z j).symm
        have hf0 : ‖f 0‖ ≤ M := hinit 0 (by simp only [Finset.card_insert_of_notMem ha]; omega)
        have hdinit : ∀ j < s.card, ‖geometricSum s d z j‖ ≤ 2 * M := by
          intro j hj
          rw [hd]
          have hj0 := hinit j (by simp only [Finset.card_insert_of_notMem ha]; omega)
          have hj1 := hinit (j + 1) (by simp only [Finset.card_insert_of_notMem ha]; omega)
          have htri := norm_sub_le (f (j + 1)) (z a * f j)
          rw [norm_mul] at htri
          have hzmul := mul_le_mul_of_nonneg_right hza (norm_nonneg (f j))
          change ‖f j‖ ≤ M at hj0
          change ‖f (j + 1)‖ ≤ M at hj1
          linarith
        have hdbound (j : ℕ) := ih d (fun i hi => hz i (Finset.mem_insert_of_mem hi))
          (mul_nonneg (by norm_num) hM) hdinit j
        have hbase : 1 ≤ 2 * ((k : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) k; linarith
        have hpow : 1 ≤ (2 * ((k : ℝ) + 1)) ^ (s.card - 1) := one_le_pow₀ hbase
        have hsum : (∑ j ∈ Finset.range k, ‖f (j + 1) - z a * f j‖) ≤
            (k : ℝ) * (2 * M * (2 * ((k : ℝ) + 1)) ^ (s.card - 1)) := by
          calc
            _ ≤ ∑ _j ∈ Finset.range k,
                2 * M * (2 * ((k : ℝ) + 1)) ^ (s.card - 1) := by
              apply Finset.sum_le_sum
              intro j hj
              rw [← hd]
              refine (hdbound j).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
              apply pow_le_pow_left₀ (by positivity)
              have hjk : (j : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
              linarith
            _ = _ := by simp
        have htel := norm_le_initial_add_sum_difference_of_norm_le_one f (z a) hza k
        have hpoweq : (2 * ((k : ℝ) + 1)) ^ s.card =
            (2 * ((k : ℝ) + 1)) ^ (s.card - 1) * (2 * ((k : ℝ) + 1)) := by
          rw [← pow_succ]
          congr 1
          omega
        simp only [Finset.card_insert_of_notMem ha, Nat.add_sub_cancel]
        change ‖f k‖ ≤ _
        rw [hpoweq]
        have hm : M ≤ M * (2 * ((k : ℝ) + 1)) ^ (s.card - 1) :=
          le_mul_of_one_le_right hM hpow
        nlinarith


/-- Dividing all geometric modes by one scalar divides the value at step `k`
by its `k`-th power. -/
theorem geometricSum_div_modes {ι : Type*} (s : Finset ι) (c z : ι → ℂ)
    (R : ℂ) (k : ℕ) :
    geometricSum s c (fun j => z j / R) k = geometricSum s c z k / R ^ k := by
  simp only [geometricSum, div_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A common modulus bound contributes exactly its power at the target step. -/
theorem norm_geometricSum_le_of_norm_le {ι : Type*} (s : Finset ι) (c z : ι → ℂ)
    {R M : ℝ} (hR : 1 ≤ R) (hz : ∀ j ∈ s, ‖z j‖ ≤ R) (hM : 0 ≤ M)
    (hinit : ∀ j < s.card, ‖geometricSum s c z j‖ ≤ M) (k : ℕ) :
    ‖geometricSum s c z k‖ ≤ R ^ k * M * (2 * ((k : ℝ) + 1)) ^ (s.card - 1) := by
  have hR0 : 0 < R := by linarith
  have hnorm (j : ℕ) : ‖geometricSum s c (fun i => z i / (R : ℂ)) j‖ =
      ‖geometricSum s c z j‖ / R ^ j := by
    rw [geometricSum_div_modes, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR0]
  have hnormalized : ∀ i ∈ s, ‖z i / (R : ℂ)‖ ≤ 1 := by
    intro i hi
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    exact (div_le_one hR0).mpr (hz i hi)
  have hinitial : ∀ j < s.card, ‖geometricSum s c (fun i => z i / (R : ℂ)) j‖ ≤ M := by
    intro j hj
    rw [hnorm]
    exact (div_le_iff₀ (pow_pos hR0 j)).mpr
      ((hinit j hj).trans (le_mul_of_one_le_right hM (one_le_pow₀ hR)))
  have h := norm_geometricSum_le_of_norm_le_one s c _ hnormalized hM hinitial k
  rw [hnorm] at h
  have hmul := (div_le_iff₀ (pow_pos hR0 k)).mp h
  nlinarith

/-- An entire exponential polynomial with complex exponents. -/
def complexExponentialSum {ι : Type*} (s : Finset ι) (c ζ : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ s, c j * Complex.exp (ζ j * z)

/-- Restriction to a real arithmetic progression is a geometric sum. -/
theorem complexExponentialSum_progression {ι : Type*} (s : Finset ι)
    (c ζ : ι → ℂ) (a h : ℝ) (k : ℕ) :
    complexExponentialSum s c ζ ((a + (k : ℝ) * h : ℝ) : ℂ) =
      geometricSum s (fun j => c j * Complex.exp (ζ j * a))
        (fun j => Complex.exp (ζ j * h)) k := by
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  rw [mul_add, Complex.exp_add,
    show ζ j * ((k : ℂ) * (h : ℂ)) = (k : ℂ) * (ζ j * h) by ring,
    Complex.exp_nat_mul]
  ring

/-- Propagation on a nonnegative-step progression with explicit real-part growth. -/
theorem norm_complexExponentialSum_le_of_progression {ι : Type*} (s : Finset ι)
    (c ζ : ι → ℂ) {σ M : ℝ} (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, (ζ j).re ≤ σ)
    (hM : 0 ≤ M) (a h : ℝ) (hh : 0 ≤ h)
    (hinit : ∀ j < s.card, ‖complexExponentialSum s c ζ ((a + (j : ℝ) * h : ℝ) : ℂ)‖ ≤ M)
    (k : ℕ) :
    ‖complexExponentialSum s c ζ ((a + (k : ℝ) * h : ℝ) : ℂ)‖ ≤
      Real.exp (σ * ((k : ℝ) * h)) * M * (2 * ((k : ℝ) + 1)) ^ (s.card - 1) := by
  have hmodes : ∀ j ∈ s, ‖Complex.exp (ζ j * (h : ℂ))‖ ≤ Real.exp (σ * h) := by
    intro j hj
    rw [Complex.norm_exp, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hζ j hj) hh)
  simp_rw [complexExponentialSum_progression] at hinit ⊢
  have h := norm_geometricSum_le_of_norm_le s _ _
    (Real.one_le_exp (mul_nonneg hσ hh)) hmodes hM hinit k
  rw [← Real.exp_nat_mul] at h
  convert h using 1
  congr 3
  ring

/-- Propagation from an initial real subinterval for arbitrary complex exponents.
Only an upper bound on their real parts enters the exponential factor. -/
theorem norm_complexExponentialSum_le_initial_interval {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ)
    {σ a l L M x : ℝ} (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, (ζ j).re ≤ σ)
    (hl : 0 < l) (hlL : l ≤ L) (hM : 0 ≤ M)
    (hinit : ∀ y ∈ Set.Icc a (a + l), ‖complexExponentialSum s c ζ y‖ ≤ M)
    (hx : x ∈ Set.Icc a (a + L)) :
    ‖complexExponentialSum s c ζ x‖ ≤
      Real.exp (σ * L) * M * (8 * (s.card : ℝ) * L / l) ^ (s.card - 1) := by
  let Q : ℝ := (s.card : ℝ) * L / l
  let k : ℕ := ⌈Q⌉₊ + 1
  have hn : (1 : ℝ) ≤ s.card := by exact_mod_cast Finset.one_le_card.mpr hs
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    apply (le_div_iff₀ hl).mpr
    nlinarith
  have hk : 0 < k := by dsimp [k]; omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hklo : Q ≤ (k : ℝ) := by
    dsimp [k]
    push_cast
    linarith [Nat.le_ceil Q]
  have hkhi : (k : ℝ) < Q + 2 := by
    dsimp [k]
    push_cast
    linarith [Nat.ceil_lt_add_one (show 0 ≤ Q by linarith)]
  have hscale : (s.card : ℝ) * L ≤ (k : ℝ) * l := (div_le_iff₀ hl).mp hklo
  let h : ℝ := (x - a) / k
  have hh : 0 ≤ h := div_nonneg (sub_nonneg.mpr hx.1) hkR.le
  have hgrid (j : ℕ) (hj : j < s.card) : a + (j : ℝ) * h ∈ Set.Icc a (a + l) := by
    constructor
    · linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hh]
    · have hjR : (j : ℝ) ≤ s.card := by exact_mod_cast Nat.le_of_lt hj
      have hmul : (j : ℝ) * (x - a) ≤ (s.card : ℝ) * L :=
        mul_le_mul hjR (by linarith [hx.2]) (sub_nonneg.mpr hx.1) (Nat.cast_nonneg _)
      have hjh : (j : ℝ) * h ≤ l := by
        dsimp [h]
        rw [← mul_div_assoc, div_le_iff₀ hkR]
        exact hmul.trans (by simpa only [mul_comm] using hscale)
      linarith
  have hsample : ∀ j < s.card,
      ‖complexExponentialSum s c ζ ((a + (j : ℝ) * h : ℝ) : ℂ)‖ ≤ M := by
    intro j hj
    exact hinit (a + (j : ℝ) * h) (hgrid j hj)
  have hp := norm_complexExponentialSum_le_of_progression s c ζ
    (σ := σ) (M := M) hσ hζ hM a h hh hsample k
  have hstep : (k : ℝ) * h = x - a := by
    dsimp only [h]
    exact mul_div_cancel₀ _ hkR.ne'
  have hxgrid : a + (k : ℝ) * h = x := by rw [hstep]; ring
  rw [hxgrid, hstep] at hp
  refine hp.trans ?_
  have hexp : Real.exp (σ * (x - a)) ≤ Real.exp (σ * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hx.2]) hσ)
  have hbase : 2 * ((k : ℝ) + 1) ≤ 8 * (s.card : ℝ) * L / l := by
    have heq : 8 * (s.card : ℝ) * L / l = 8 * Q := by dsimp [Q]; ring
    rw [heq]
    linarith
  exact mul_le_mul (mul_le_mul_of_nonneg_right hexp hM)
    (pow_le_pow_left₀ (by positivity) hbase (s.card - 1)) (by positivity)
    (mul_nonneg (Real.exp_pos _).le hM)

/-- Restriction of an entire exponential polynomial to a complex line. -/
theorem complexExponentialSum_ray {ι : Type*} (s : Finset ι)
    (c ζ : ι → ℂ) (z₀ θ : ℂ) (x : ℝ) :
    complexExponentialSum s c ζ (z₀ + θ * x) =
      complexExponentialSum s (fun j => c j * Complex.exp (ζ j * z₀))
        (fun j => ζ j * θ) x := by
  apply Finset.sum_congr rfl
  intro j _
  have he : ζ j * (z₀ + θ * (x : ℂ)) = ζ j * z₀ + (ζ j * θ) * x := by ring
  rw [he, Complex.exp_add]
  ring

/-- An exponential polynomial on a larger complex disk is controlled by its
values on a concentric smaller disk, with the spectral radius recorded
explicitly in the exponential growth factor. -/
theorem norm_complexExponentialSum_le_of_disk {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ)
    {σ r R M : ℝ} (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, ‖ζ j‖ ≤ σ)
    (hr : 0 < r) (hrR : r ≤ R) (hM : 0 ≤ M) (z₀ z : ℂ)
    (hsmall : ∀ w : ℂ, dist w z₀ ≤ r → ‖complexExponentialSum s c ζ w‖ ≤ M)
    (hz : dist z z₀ ≤ R) :
    ‖complexExponentialSum s c ζ z‖ ≤
      Real.exp (σ * R) * M * (8 * (s.card : ℝ) * R / r) ^ (s.card - 1) := by
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
  have h := norm_complexExponentialSum_le_initial_interval s hs
    (fun j => c j * Complex.exp (ζ j * z₀)) (fun j => ζ j * θ)
    hσ hfreq hr hrR hM hinit hpoint
  rw [← complexExponentialSum_ray, hray] at h
  exact h

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ComplexExponentialPropagation
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# Binomial propagation of finite exponential sums

Repeated summation of a frequency-eliminating difference yields a binomial
coefficient. Its factorial denominator removes the number of frequencies from
the base of interval and disk growth estimates.
-/

noncomputable section
open scoped BigOperators
namespace Erdos522

/-- The hockey-stick identity including the empty range. -/
theorem sum_range_choose_add (k n : ℕ) :
    (∑ j ∈ Finset.range k, (j + n).choose n) = (k + n).choose (n + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      simpa only [Nat.succ_add, Nat.choose_succ_succ] using Nat.add_comm _ _

/-- Initial values of a contracting geometric sum give a binomial growth bound. -/
theorem norm_geometricSum_le_binomial {ι : Type*} (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ j ∈ s, ‖z j‖ ≤ 1) {M : ℝ} (hM : 0 ≤ M)
    (hinit : ∀ k < s.card, ‖geometricSum s c z k‖ ≤ M) (k : ℕ) :
    ‖geometricSum s c z k‖ ≤
      M * 2 ^ (s.card - 1) * ((k + (s.card - 1)).choose (s.card - 1) : ℝ) := by
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
        have hsum : (∑ j ∈ Finset.range k, ‖f (j + 1) - z a * f j‖) ≤
            M * 2 ^ s.card * ((k + (s.card - 1)).choose s.card : ℝ) := by
          calc
            _ ≤ ∑ j ∈ Finset.range k,
                2 * M * 2 ^ (s.card - 1) * ((j + (s.card - 1)).choose (s.card - 1) : ℝ) := by
              apply Finset.sum_le_sum
              intro j _
              rw [← hd]
              exact hdbound j
            _ = M * 2 ^ s.card * ((k + (s.card - 1)).choose s.card : ℝ) := by
              rw [← Finset.mul_sum, ← Nat.cast_sum, sum_range_choose_add]
              rw [show s.card - 1 + 1 = s.card by omega]
              rw [show (2 : ℝ) ^ s.card = 2 ^ (s.card - 1) * 2 by
                rw [← pow_succ]; congr 1; omega]
              ring
        have htel := norm_le_initial_add_sum_difference_of_norm_le_one f (z a) hza k
        have hchoose : 1 ≤ ((k + (s.card - 1)).choose (s.card - 1) : ℝ) := by
          exact_mod_cast Nat.choose_pos (Nat.le_add_left _ _)
        have hpow : (1 : ℝ) ≤ 2 ^ s.card := one_le_pow₀ (by norm_num)
        have hpascal : ((k + s.card).choose s.card : ℝ) =
            ((k + (s.card - 1)).choose s.card : ℝ) +
              ((k + (s.card - 1)).choose (s.card - 1) : ℝ) := by
          have h := Nat.choose_succ_succ (k + (s.card - 1)) (s.card - 1)
          have htop : k + (s.card - 1) + 1 = k + s.card := by omega
          rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, htop,
            show s.card - 1 + 1 = s.card by omega] at h
          exact_mod_cast h.trans (Nat.add_comm _ _)
        simp only [Finset.card_insert_of_notMem ha, Nat.add_sub_cancel]
        change ‖f k‖ ≤ _
        rw [hpascal, mul_add]
        have hm : M ≤ M * 2 ^ s.card *
            ((k + (s.card - 1)).choose (s.card - 1) : ℝ) := by
          exact (le_mul_of_one_le_right hM hpow).trans
            (le_mul_of_one_le_right (by positivity) hchoose)
        linarith

/-- The elementary factorial bound from the exponential series gives the
usual exponential estimate for a binomial coefficient. -/
theorem choose_le_exp_mul_div_pow (k n : ℕ) (hn : 0 < n) :
    (k.choose n : ℝ) ≤ (Real.exp 1 * k / n) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg (α := ℝ) n) n
  have heq : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [heq] at hfac
  calc
    _ ≤ (k : ℝ) ^ n / n.factorial := Nat.choose_le_pow_div n k
    _ = ((k : ℝ) / n) ^ n * ((n : ℝ) ^ n / n.factorial) := by
      rw [div_pow]
      field_simp
    _ ≤ ((k : ℝ) / n) ^ n * Real.exp 1 ^ n :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = (Real.exp 1 * k / n) ^ n := by rw [← mul_pow]; congr 1; ring

/-- A common mode-modulus bound contributes its power to the binomial estimate. -/
theorem norm_geometricSum_le_binomial_of_norm_le {ι : Type*}
    (s : Finset ι) (c z : ι → ℂ)
    {R M : ℝ} (hR : 1 ≤ R) (hz : ∀ j ∈ s, ‖z j‖ ≤ R) (hM : 0 ≤ M)
    (hinit : ∀ j < s.card, ‖geometricSum s c z j‖ ≤ M) (k : ℕ) :
    ‖geometricSum s c z k‖ ≤
      R ^ k * M * 2 ^ (s.card - 1) * ((k + (s.card - 1)).choose (s.card - 1) : ℝ) := by
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
  have h := norm_geometricSum_le_binomial s c _ hnormalized hM hinitial k
  rw [hnorm] at h
  have hmul := (div_le_iff₀ (pow_pos hR0 k)).mp h
  nlinarith

/-- Binomial propagation along a real arithmetic progression. -/
theorem norm_complexExponentialSum_le_binomial_progression {ι : Type*} (s : Finset ι)
    (c ζ : ι → ℂ) {σ M : ℝ} (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, (ζ j).re ≤ σ)
    (hM : 0 ≤ M) (a h : ℝ) (hh : 0 ≤ h)
    (hinit : ∀ j < s.card, ‖complexExponentialSum s c ζ ((a + (j : ℝ) * h : ℝ) : ℂ)‖ ≤ M)
    (k : ℕ) :
    ‖complexExponentialSum s c ζ ((a + (k : ℝ) * h : ℝ) : ℂ)‖ ≤
      Real.exp (σ * ((k : ℝ) * h)) * M * 2 ^ (s.card - 1) *
        ((k + (s.card - 1)).choose (s.card - 1) : ℝ) := by
  have hmodes : ∀ j ∈ s, ‖Complex.exp (ζ j * (h : ℂ))‖ ≤ Real.exp (σ * h) := by
    intro j hj
    rw [Complex.norm_exp, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hζ j hj) hh)
  simp_rw [complexExponentialSum_progression] at hinit ⊢
  have h := norm_geometricSum_le_binomial_of_norm_le s _ _
    (Real.one_le_exp (mul_nonneg hσ hh)) hmodes hM hinit k
  rw [← Real.exp_nat_mul] at h
  convert h using 1
  congr 4
  ring

/-- A bound on the number of progression steps cancels the binomial's
factorial denominator. -/
theorem two_pow_mul_choose_le (k n : ℕ) (hn : 0 < n) {Q : ℝ}
    (hQ : (k : ℝ) + n ≤ n * Q) :
    (2 : ℝ) ^ n * ((k + n).choose n : ℝ) ≤ (2 * Real.exp 1 * Q) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ 2 ^ n * (Real.exp 1 * (k + n) / n) ^ n :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast choose_le_exp_mul_div_pow (k + n) n hn)
        (by positivity)
    _ = (2 * Real.exp 1 * ((k : ℝ) + n) / n) ^ n := by
      rw [← mul_pow]
      congr 1
      ring
    _ ≤ _ := by
      apply pow_le_pow_left₀ (by positivity)
      apply (div_le_iff₀ hnR).mpr
      nlinarith [mul_le_mul_of_nonneg_left hQ (show 0 ≤ 2 * Real.exp 1 by positivity)]

/-- Interval propagation with a universal base independent of the number of
frequencies. The exponent is the number of terms minus one. -/
theorem norm_complexExponentialSum_le_interval_universal {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ)
    {σ a l L M x : ℝ} (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, (ζ j).re ≤ σ)
    (hl : 0 < l) (hlL : l ≤ L) (hM : 0 ≤ M)
    (hinit : ∀ y ∈ Set.Icc a (a + l), ‖complexExponentialSum s c ζ y‖ ≤ M)
    (hx : x ∈ Set.Icc a (a + L)) :
    ‖complexExponentialSum s c ζ x‖ ≤
      Real.exp (σ * L) * M * (8 * Real.exp 1 * L / l) ^ (s.card - 1) := by
  by_cases hn1 : s.card = 1
  · simpa only [hn1, Nat.sub_self, pow_zero, mul_one] using
      norm_complexExponentialSum_le_initial_interval s hs c ζ hσ hζ hl hlL hM hinit hx
  let n := s.card - 1
  have hn : 0 < n := by
    have := Finset.one_le_card.mpr hs
    dsimp [n]
    omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let Q : ℝ := (n : ℝ) * L / l
  let k : ℕ := ⌈Q⌉₊ + 1
  have hQ : (n : ℝ) ≤ Q := by
    dsimp [Q]
    apply (le_div_iff₀ hl).mpr
    exact mul_le_mul_of_nonneg_left hlL (Nat.cast_nonneg _)
  have hQ1 : 1 ≤ Q := hnR.trans hQ
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
  have hscale : (n : ℝ) * L ≤ (k : ℝ) * l := (div_le_iff₀ hl).mp hklo
  let h : ℝ := (x - a) / k
  have hh : 0 ≤ h := div_nonneg (sub_nonneg.mpr hx.1) hkR.le
  have hgrid (j : ℕ) (hj : j < s.card) : a + (j : ℝ) * h ∈ Set.Icc a (a + l) := by
    constructor
    · linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hh]
    · have hjR : (j : ℝ) ≤ n := by
        exact_mod_cast (show j ≤ n by dsimp [n]; omega)
      have hmul : (j : ℝ) * (x - a) ≤ (n : ℝ) * L :=
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
  have hp := norm_complexExponentialSum_le_binomial_progression s c ζ
    (σ := σ) (M := M) hσ hζ hM a h hh hsample k
  have hstep : (k : ℝ) * h = x - a := by
    dsimp only [h]
    exact mul_div_cancel₀ _ hkR.ne'
  have hxgrid : a + (k : ℝ) * h = x := by rw [hstep]; ring
  rw [hxgrid, hstep] at hp
  have hexp : Real.exp (σ * (x - a)) ≤ Real.exp (σ * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hx.2]) hσ)
  have hbin := two_pow_mul_choose_le k n hn
    (Q := 4 * L / l) (by
      have heq : (n : ℝ) * (4 * L / l) = 4 * Q := by dsimp [Q]; ring
      rw [heq]
      linarith)
  have hbase : 2 * Real.exp 1 * (4 * L / l) = 8 * Real.exp 1 * L / l := by ring
  rw [hbase] at hbin
  calc
    _ ≤ (Real.exp (σ * (x - a)) * M) *
        (2 ^ n * ((k + n).choose n : ℝ)) := by simpa only [n, mul_assoc] using hp
    _ ≤ (Real.exp (σ * L) * M) * (8 * Real.exp 1 * L / l) ^ n :=
      mul_le_mul (mul_le_mul_of_nonneg_right hexp hM) hbin (by positivity)
        (mul_nonneg (Real.exp_pos _).le hM)
    _ = _ := rfl

end Erdos522

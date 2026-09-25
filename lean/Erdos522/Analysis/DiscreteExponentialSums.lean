/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ExponentialApproximation

/-!
# Propagation along arithmetic progressions

A finite sum of unit-modulus geometric sequences is controlled everywhere on
an arithmetic progression by its first values. The estimate depends on the
number of terms and the number of steps, but not on the frequencies or their
separation. A first-order difference removes one term, and summing that
difference gives the induction on the number of terms.
-/

noncomputable section
open scoped BigOperators
namespace Erdos522

/-- A finite sum of geometric sequences. -/
def geometricSum {ι : Type*} (s : Finset ι) (c z : ι → ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ s, c j * z j ^ k

/-- Summing a first-order difference with a unit-modulus multiplier. -/
theorem norm_le_initial_add_sum_difference (f : ℕ → ℂ) (z : ℂ)
    (hz : ‖z‖ = 1) (k : ℕ) :
    ‖f k‖ ≤ ‖f 0‖ + ∑ j ∈ Finset.range k, ‖f (j + 1) - z * f j‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h := norm_add_le (z * f k) (f (k + 1) - z * f k)
      rw [show z * f k + (f (k + 1) - z * f k) = f (k + 1) by ring,
        norm_mul, hz, one_mul] at h
      rw [Finset.sum_range_succ]
      linarith

/-- One difference removes the selected geometric mode exactly. -/
theorem geometricSum_difference_insert {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) (ha : a ∉ s) (c z : ι → ℂ) (k : ℕ) :
    geometricSum (insert a s) c z (k + 1) - z a * geometricSum (insert a s) c z k =
      geometricSum s (fun j => c j * (z j - z a)) z k := by
  simp only [geometricSum, Finset.sum_insert ha, pow_succ, mul_add,
    Finset.mul_sum]
  rw [add_sub_add_comm]
  rw [show c a * (z a ^ k * z a) - z a * (c a * z a ^ k) = 0 by ring]
  simp only [zero_add, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Initial values of a finite unit-modulus geometric sum control all later
values, with a bound independent of the locations of its modes. -/
theorem norm_geometricSum_le {ι : Type*} (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ j ∈ s, ‖z j‖ = 1) {M : ℝ} (hM : 0 ≤ M)
    (hinit : ∀ k < s.card, ‖geometricSum s c z k‖ ≤ M) (k : ℕ) :
    ‖geometricSum s c z k‖ ≤ M * (2 * ((k : ℝ) + 1)) ^ (s.card - 1) := by
  classical
  induction s using Finset.induction generalizing c M k with
  | empty => simp [geometricSum, hM]
  | @insert a s ha ih =>
      by_cases hs : s = ∅
      · subst s
        have h0 := hinit 0 (by simp)
        simpa [geometricSum, norm_mul, norm_pow, hz a (by simp)] using h0
      · have hn : 1 ≤ s.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
        have hza : ‖z a‖ = 1 := hz a (Finset.mem_insert_self _ _)
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
          rw [norm_mul, hza, one_mul] at htri
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
        have htel := norm_le_initial_add_sum_difference f (z a) hza k
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

/-- Integer multiples of the argument correspond to powers of the character. -/
theorem angularCharacter_nat_mul (k : ℕ) (x : ℝ) :
    angularCharacter ((k : ℝ) * x) = angularCharacter x ^ k := by
  induction k with
  | zero => simp [angularCharacter, fourier]
  | succ k ih =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, angularCharacter_add, ih, pow_succ]

/-- Restriction of a harmonic exponential sum to an arithmetic progression. -/
theorem finiteExponentialSum_progression {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (ν : ι → ℝ) (a h : ℝ) (k : ℕ) :
    finiteExponentialSum s c ν (a + (k : ℝ) * h) =
      geometricSum s (fun j => c j * angularCharacter (ν j * a))
        (fun j => angularCharacter (ν j * h)) k := by
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_add, angularCharacter_add,
    show ν j * ((k : ℝ) * h) = (k : ℝ) * (ν j * h) by ring,
    angularCharacter_nat_mul]
  ring

/-- The harmonic progression estimate, with no frequency separation hypothesis. -/
theorem norm_finiteExponentialSum_le_of_progression {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (ν : ι → ℝ) (a h : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hinit : ∀ j < s.card, ‖finiteExponentialSum s c ν (a + (j : ℝ) * h)‖ ≤ M)
    (k : ℕ) :
    ‖finiteExponentialSum s c ν (a + (k : ℝ) * h)‖ ≤
      M * (2 * ((k : ℝ) + 1)) ^ (s.card - 1) := by
  simp_rw [finiteExponentialSum_progression] at hinit ⊢
  exact norm_geometricSum_le s _ _ (fun j _ => norm_angularCharacter _) hM hinit k

/-- Propagation from an initial subinterval, with an explicit choice of the
number of progression steps. -/
theorem norm_finiteExponentialSum_le_on_initial_interval {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) {a l L M x : ℝ}
    (hM : 0 ≤ M) (k : ℕ) (hk : 0 < k)
    (hscale : (s.card : ℝ) * L ≤ (k : ℝ) * l)
    (hinit : ∀ y ∈ Set.Icc a (a + l), ‖finiteExponentialSum s c ν y‖ ≤ M)
    (hx : x ∈ Set.Icc a (a + L)) :
    ‖finiteExponentialSum s c ν x‖ ≤ M * (2 * ((k : ℝ) + 1)) ^ (s.card - 1) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let h := (x - a) / k
  have hnonneg : 0 ≤ h := div_nonneg (sub_nonneg.mpr hx.1) hkR.le
  have hgrid (j : ℕ) (hj : j < s.card) : a + (j : ℝ) * h ∈ Set.Icc a (a + l) := by
    constructor
    · linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hnonneg]
    · have hjR : (j : ℝ) ≤ s.card := by exact_mod_cast Nat.le_of_lt hj
      have hmul : (j : ℝ) * (x - a) ≤ (s.card : ℝ) * L :=
        mul_le_mul hjR (by linarith [hx.2]) (sub_nonneg.mpr hx.1) (Nat.cast_nonneg _)
      have hh : (j : ℝ) * h ≤ l := by
        dsimp [h]
        rw [← mul_div_assoc, div_le_iff₀ hkR]
        exact hmul.trans (by simpa only [mul_comm] using hscale)
      linarith
  have hb := norm_finiteExponentialSum_le_of_progression s c ν a h hM
    (fun j hj => hinit _ (hgrid j hj)) k
  have hxgrid : a + (k : ℝ) * h = x := by dsimp [h]; field_simp; ring
  simpa only [hxgrid] using hb

/-- An interval estimate for harmonic exponential sums with arbitrary real
frequencies. The constant depends only on the number of terms and the length
ratio. -/
theorem norm_finiteExponentialSum_le_initial_interval {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c : ι → ℂ) (ν : ι → ℝ)
    {a l L M x : ℝ} (hl : 0 < l) (hlL : l ≤ L) (hM : 0 ≤ M)
    (hinit : ∀ y ∈ Set.Icc a (a + l), ‖finiteExponentialSum s c ν y‖ ≤ M)
    (hx : x ∈ Set.Icc a (a + L)) :
    ‖finiteExponentialSum s c ν x‖ ≤
      M * (8 * (s.card : ℝ) * L / l) ^ (s.card - 1) := by
  let R : ℝ := (s.card : ℝ) * L / l
  let k : ℕ := ⌈R⌉₊ + 1
  have hn : (1 : ℝ) ≤ s.card := by exact_mod_cast Finset.one_le_card.mpr hs
  have hR : 1 ≤ R := by
    dsimp [R]
    apply (le_div_iff₀ hl).mpr
    nlinarith
  have hk : 0 < k := by dsimp [k]; omega
  have hklo : R ≤ (k : ℝ) := by
    dsimp [k]
    push_cast
    linarith [Nat.le_ceil R]
  have hkhi : (k : ℝ) < R + 2 := by
    dsimp [k]
    push_cast
    linarith [Nat.ceil_lt_add_one (show 0 ≤ R by linarith)]
  have hscale : (s.card : ℝ) * L ≤ (k : ℝ) * l := by
    exact (div_le_iff₀ hl).mp hklo
  have hb := norm_finiteExponentialSum_le_on_initial_interval s c ν hM k hk hscale hinit hx
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ hM)
  apply pow_le_pow_left₀ (by positivity)
  change 2 * ((k : ℝ) + 1) ≤ 8 * (s.card : ℝ) * L / l
  have heq : 8 * (s.card : ℝ) * L / l = 8 * R := by dsimp [R]; ring
  rw [heq]
  linarith

/-- Reflection changes the signs of all real frequencies. -/
theorem finiteExponentialSum_neg {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (ν : ι → ℝ) (x : ℝ) :
    finiteExponentialSum s c ν (-x) = finiteExponentialSum s c (fun j => -ν j) x := by
  simp only [finiteExponentialSum, mul_neg, neg_mul]

/-- The interval form of a harmonic Turán estimate. Frequencies need not be
separated or distinct; the bound counts the terms in the supplied sum. -/
theorem norm_finiteExponentialSum_le_of_subinterval {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c : ι → ℂ) (ν : ι → ℝ)
    {A B a b M x : ℝ} (ha : A ≤ a) (hab : a < b) (hb : b ≤ B) (hM : 0 ≤ M)
    (hsmall : ∀ y ∈ Set.Icc a b, ‖finiteExponentialSum s c ν y‖ ≤ M)
    (hx : x ∈ Set.Icc A B) :
    ‖finiteExponentialSum s c ν x‖ ≤
      M * (8 * (s.card : ℝ) * (B - A) / (b - a)) ^ (s.card - 1) := by
  have hl : 0 < b - a := sub_pos.mpr hab
  have hlL : b - a ≤ B - A := by linarith
  by_cases hax : a ≤ x
  · apply norm_finiteExponentialSum_le_initial_interval s hs c ν
      (a := a) (l := b - a) (L := B - A) (x := x) hl hlL hM
    · intro y hy
      apply hsmall y
      constructor <;> linarith [hy.1, hy.2]
    · constructor <;> linarith [hx.2]
  · have hr := norm_finiteExponentialSum_le_initial_interval s hs c (fun j => -ν j)
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

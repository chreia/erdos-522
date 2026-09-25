/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Multiset.Filter

/-! Root counts in subsets of the complex plane, with multiplicity. -/

noncomputable section

namespace Erdos522

/-- The number of roots of a polynomial in a set, counted with multiplicity. -/
def zeroCountIn (P : Polynomial ℂ) (s : Set ℂ) : ℕ := by
  classical
  exact (P.roots.filter (fun z ↦ z ∈ s)).card

/-- The number of roots in the closed disk centered at the origin. -/
def closedZeroCount (P : Polynomial ℂ) (r : ℝ) : ℕ :=
  zeroCountIn P {z | ‖z‖ ≤ r}

/-- The number of roots in the open disk centered at the origin. -/
def openZeroCount (P : Polynomial ℂ) (r : ℝ) : ℕ :=
  zeroCountIn P {z | ‖z‖ < r}

/-- The number of roots on the circle centered at the origin. -/
def circleZeroCount (P : Polynomial ℂ) (r : ℝ) : ℕ :=
  zeroCountIn P {z | ‖z‖ = r}

@[simp] theorem zeroCountIn_zero (s : Set ℂ) : zeroCountIn 0 s = 0 := by
  classical
  simp [zeroCountIn]

@[simp] theorem zeroCountIn_empty (P : Polynomial ℂ) : zeroCountIn P ∅ = 0 := by
  classical
  simp [zeroCountIn]

theorem zeroCountIn_mono (P : Polynomial ℂ) {s t : Set ℂ} (h : s ⊆ t) :
    zeroCountIn P s ≤ zeroCountIn P t := by
  classical
  apply Multiset.card_le_card
  apply Multiset.le_filter.mpr
  refine ⟨Multiset.filter_le _ _, ?_⟩
  intro z hz
  exact h (Multiset.mem_filter.mp hz).2

theorem zeroCountIn_le_natDegree (P : Polynomial ℂ) (s : Set ℂ) :
    zeroCountIn P s ≤ P.natDegree := by
  classical
  exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans P.card_roots'

theorem closedZeroCount_mono (P : Polynomial ℂ) : Monotone (closedZeroCount P) := by
  intro r s hrs
  exact zeroCountIn_mono P (fun _ hz ↦ hz.trans hrs)

/-- Division by a nonnegative constant preserves monotonicity of closed-disk root counts. -/
theorem normalized_closedZeroCount_mono (P : Polynomial ℂ) {a : ℝ} (ha : 0 ≤ a) :
    Monotone (fun r => (closedZeroCount P r : ℝ) / a) := by
  intro r s hrs
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (closedZeroCount_mono P hrs)) ha

/-- The normalized distribution of scaled root radii is nondecreasing, including degree zero. -/
theorem scaled_closedZeroCount_mono (P : Polynomial ℂ) (N : ℕ) :
    Monotone (fun x => (closedZeroCount P (1 + x / N) : ℝ) / N) := by
  apply (normalized_closedZeroCount_mono P (Nat.cast_nonneg N)).comp
  intro x y hxy
  exact add_le_add (le_refl (1 : ℝ)) (div_le_div_of_nonneg_right hxy (Nat.cast_nonneg N))

theorem openZeroCount_le_closedZeroCount (P : Polynomial ℂ) (r : ℝ) :
    openZeroCount P r ≤ closedZeroCount P r := by
  apply zeroCountIn_mono P
  intro z hz
  change ‖z‖ < r at hz
  exact le_of_lt hz

theorem closedZeroCount_eq_open_add_circle (P : Polynomial ℂ) (r : ℝ) :
    closedZeroCount P r = openZeroCount P r + circleZeroCount P r := by
  classical
  have h := Multiset.filter_add_filter (fun z : ℂ ↦ ‖z‖ < r)
    (fun z : ℂ ↦ ‖z‖ = r) P.roots
  have hu : (fun z : ℂ ↦ ‖z‖ < r ∨ ‖z‖ = r) = (fun z ↦ ‖z‖ ≤ r) := by
    funext z
    apply propext
    constructor
    · rintro (h | h)
      · exact h.le
      · exact h.le
    · exact lt_or_eq_of_le
  have hi : (fun z : ℂ ↦ ‖z‖ < r ∧ ‖z‖ = r) = (fun _ ↦ False) := by
    funext z
    apply propext
    constructor
    · rintro ⟨h₁, h₂⟩
      exact (ne_of_lt h₁) h₂
    · exact False.elim
  simp only [hu, hi, Multiset.filter_false, add_zero] at h
  have hc := congrArg Multiset.card h
  simpa [closedZeroCount, openZeroCount, circleZeroCount, zeroCountIn] using hc.symm

theorem closedZeroCount_eq_open_of_no_circle_roots (P : Polynomial ℂ) (r : ℝ)
    (h : ∀ z ∈ P.roots, ‖z‖ ≠ r) : closedZeroCount P r = openZeroCount P r := by
  classical
  have hc : circleZeroCount P r = 0 := by
    simp only [circleZeroCount, zeroCountIn, Multiset.card_eq_zero]
    exact Multiset.filter_eq_nil.mpr h
  rw [closedZeroCount_eq_open_add_circle, hc, add_zero]

@[simp] theorem zeroCountIn_univ (P : Polynomial ℂ) :
    zeroCountIn P Set.univ = P.natDegree := by
  classical
  simp [zeroCountIn, IsAlgClosed.card_roots_eq_natDegree]

theorem zeroCountIn_add_compl (P : Polynomial ℂ) (s : Set ℂ) :
    zeroCountIn P s + zeroCountIn P sᶜ = P.natDegree := by
  classical
  have h := Multiset.filter_add_not (fun z : ℂ ↦ z ∈ s) P.roots
  have hc := congrArg Multiset.card h
  simpa [zeroCountIn, IsAlgClosed.card_roots_eq_natDegree] using hc

theorem zeroCountIn_union_le (P : Polynomial ℂ) (s t : Set ℂ) :
    zeroCountIn P (s ∪ t) ≤ zeroCountIn P s + zeroCountIn P t := by
  classical
  have h := Multiset.filter_add_filter (fun z : ℂ ↦ z ∈ s)
    (fun z : ℂ ↦ z ∈ t) P.roots
  have hc := congrArg Multiset.card h
  have he : zeroCountIn P s + zeroCountIn P t =
      zeroCountIn P (s ∪ t) + zeroCountIn P (s ∩ t) := by
    simpa [zeroCountIn] using hc
  omega

end Erdos522

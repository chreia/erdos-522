/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.AngularSeparation

/-!
# Simultaneous angular separation at many times

A finite union of pair-collision events leaves a quantitatively large set of
times on which every phase pair is separated.
-/

noncomputable section

open MeasureTheory

namespace Erdos522

/-- Times in `[0,τ]` at which every pair of distinct indexed frequencies is phase-separated. -/
def separatedAngularTimes {ι : Type*} (a : ι → ℝ) (τ δ : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ t ≤ τ ∧ ∀ i j, i ≠ j →
    δ ≤ ‖angularCharacter (a i * t) - angularCharacter (a j * t)‖}

lemma continuous_angularCharacter : Continuous angularCharacter := by
  have heq : angularCharacter = fun x => unitCirclePoint (2 * Real.pi * x) :=
    funext angularCharacter_eq
  rw [heq]
  unfold unitCirclePoint
  fun_prop

/-- The simultaneous separation event is closed. -/
theorem isClosed_separatedAngularTimes {ι : Type*} (a : ι → ℝ) (τ δ : ℝ) :
    IsClosed (separatedAngularTimes a τ δ) := by
  have heq : separatedAngularTimes a τ δ = Set.Icc 0 τ ∩
      ⋂ i, ⋂ j, ⋂ (_h : i ≠ j),
        {t | δ ≤ ‖angularCharacter (a i * t) - angularCharacter (a j * t)‖} := by
    ext t
    simp [separatedAngularTimes, and_assoc]
  rw [heq]
  apply isClosed_Icc.inter
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  apply isClosed_le continuous_const
  exact ((continuous_angularCharacter.comp (continuous_const.mul continuous_id)).sub
    (continuous_angularCharacter.comp (continuous_const.mul continuous_id))).norm

theorem measurableSet_separatedAngularTimes {ι : Type*} (a : ι → ℝ) (τ δ : ℝ) :
    MeasurableSet (separatedAngularTimes a τ δ) :=
  (isClosed_separatedAngularTimes a τ δ).measurableSet

theorem volume_separatedAngularTimes_ne_top {ι : Type*} (a : ι → ℝ) (τ δ : ℝ) :
    volume (separatedAngularTimes a τ δ) ≠ ⊤ := by
  apply measure_ne_top_of_subset (s := Set.Icc 0 τ)
  · intro t ht
    exact ⟨ht.1, ht.2.1⟩
  · simp [Real.volume_Icc]

/-- The separation event and the strict pair-collision event partition the time interval. -/
theorem complement_separatedAngularTimes {ι : Type*} (a : ι → ℝ) (τ δ : ℝ) :
    Set.Icc 0 τ \ separatedAngularTimes a τ δ =
      {t | 0 ≤ t ∧ t ≤ τ ∧ ∃ i j, i ≠ j ∧
        ‖angularCharacter (a i * t) - angularCharacter (a j * t)‖ < δ} := by
  ext t
  simp only [Set.mem_sdiff, Set.mem_Icc, separatedAngularTimes, Set.mem_ofPred]
  aesop

/-- Removing the finite pair-collision budget leaves a large separation event. -/
theorem volume_separatedAngularTimes_lower_bound {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {τ δ gap : ℝ} (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hgap : 0 < gap)
    (hspacing : ∀ i j, i ≠ j → gap ≤ |a i - a j|) :
    τ - (Fintype.card ι : ℝ) ^ 2 * δ * (τ + 1 / gap) ≤
      volume.real (separatedAngularTimes a τ δ) := by
  have hbad := volume_strict_angular_collisions_le_card_sq a hτ hδ hgap hspacing
  rw [← complement_separatedAngularTimes] at hbad
  have hsub : separatedAngularTimes a τ δ ⊆ Set.Icc 0 τ := fun _ ht => ⟨ht.1, ht.2.1⟩
  rw [measureReal_sdiff hsub (measurableSet_separatedAngularTimes a τ δ)
      (by simp [Real.volume_Icc]),
    Real.volume_real_Icc, sub_zero, max_eq_left hτ] at hbad
  linarith

/-- The explicit collision budget used for `n+1` frequencies. -/
theorem angular_separation_budget (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ((n : ℝ) + 1) ^ 2 * (1 / (128 * ((n : ℝ) + 1) ^ 4)) *
      (τ + 1 / (1 / (8 * ((n : ℝ) + 1) ^ 2 * τ))) ≤ 9 * τ / 128 := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have heq : ((n : ℝ) + 1) ^ 2 * (1 / (128 * ((n : ℝ) + 1) ^ 4)) *
      (τ + 1 / (1 / (8 * ((n : ℝ) + 1) ^ 2 * τ))) =
        τ / 16 + τ / (128 * ((n : ℝ) + 1) ^ 2) := by
    field_simp
    ring
  rw [heq]
  have hterm : τ / (128 * ((n : ℝ) + 1) ^ 2) ≤ τ / 128 := by
    apply div_le_div_of_nonneg_left hτ.le (by norm_num)
    have hpow : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith
  linarith

/-- A fixed positive fraction of times simultaneously separates all `n+1` phases. -/
theorem volume_separatedAngularTimes_ge_half (n : ℕ) (a : Fin (n + 1) → ℝ)
    {τ : ℝ} (hτ : 0 < τ)
    (hspacing : ∀ i j, i ≠ j →
      1 / (8 * ((n : ℝ) + 1) ^ 2 * τ) ≤ |a i - a j|) :
    τ / 2 ≤ volume.real
      (separatedAngularTimes a τ (1 / (128 * ((n : ℝ) + 1) ^ 4))) := by
  have h := volume_separatedAngularTimes_lower_bound a hτ.le
    (by positivity : 0 ≤ 1 / (128 * ((n : ℝ) + 1) ^ 4))
    (by positivity : 0 < 1 / (8 * ((n : ℝ) + 1) ^ 2 * τ)) hspacing
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at h
  have hbudget := angular_separation_budget n hτ
  linarith

end Erdos522

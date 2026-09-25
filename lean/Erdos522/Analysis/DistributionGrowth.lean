/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.DistributionIteration

/-!
# Distribution bounds under measure growth

Successor constructions may increase the measure by more than the prescribed
increment. A reciprocal-power potential still bounds their accumulated loss,
and a fixed positive increment gives finite termination.
-/

noncomputable section

namespace Erdos522

/-- A successor with a fixed positive increase reaches a finite threshold, while
    preserving any real quantity that is nondecreasing at each step. -/
theorem exists_terminal_of_positive_progress {α : Type*}
    (mass value : α → ℝ) (admissible : α → Prop) (x₀ : α) (b d : ℝ)
    (hx₀ : admissible x₀) (hd : 0 < d)
    (hnext : ∀ x, admissible x → mass x₀ ≤ mass x → mass x ≤ b →
      ∃ y, admissible y ∧ mass x + d ≤ mass y ∧ value x ≤ value y) :
    ∃ y, admissible y ∧ b < mass y ∧ value x₀ ≤ value y := by
  have hrec : ∀ n : ℕ, ∃ x, admissible x ∧
      (b < mass x ∨ mass x₀ + n * d ≤ mass x) ∧ value x₀ ≤ value x := by
    intro n
    induction n with
    | zero => exact ⟨x₀, hx₀, Or.inr (by simp), le_rfl⟩
    | succ n ih =>
        obtain ⟨x, hx, hmass, hvalue⟩ := ih
        by_cases hterm : b < mass x
        · exact ⟨x, hx, Or.inl hterm, hvalue⟩
        · have hlow := hmass.resolve_left hterm
          have hn : 0 ≤ (n : ℝ) * d := by positivity
          obtain ⟨y, hy, hgrow, hval⟩ := hnext x hx (by linarith) (le_of_not_gt hterm)
          refine ⟨y, hy, Or.inr ?_, hvalue.trans hval⟩
          push_cast
          nlinarith
  let K : ℕ := ⌈(b - mass x₀) / d⌉₊ + 1
  obtain ⟨y, hy, hmass, hvalue⟩ := hrec K
  refine ⟨y, hy, ?_, hvalue⟩
  rcases hmass with hterm | hlow
  · exact hterm
  · have hceil : (b - mass x₀) / d ≤ (⌈(b - mass x₀) / d⌉₊ : ℝ) := Nat.le_ceil _
    have hmul := (div_le_iff₀ hd).mp hceil
    have hK : (K : ℝ) = (⌈(b - mass x₀) / d⌉₊ : ℝ) + 1 := by
      simp only [K, Nat.cast_add, Nat.cast_one]
    rw [hK] at hlow
    nlinarith

/-- Increasing the successor measure further only improves the potential decrease. -/
theorem reciprocal_power_drop_of_growth {p c x y : ℝ} (hp : 1 ≤ p)
    (hc : 0 < c) (hc1 : c ≤ 1) (hx : 0 < x) (hx1 : x ≤ 1)
    (hxy : x + distributionStep p c x ≤ y) :
    c / (4 * p ^ 3) * x ^ (-(1 / p)) ≤ x ^ (-(2 / p)) - y ^ (-(2 / p)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpos : 0 < x + distributionStep p c x :=
    add_pos hx (distributionStep_pos hp0 hc hx)
  have hpow := Real.rpow_le_rpow_of_nonpos hpos hxy (show -(2 / p) ≤ 0 from neg_nonpos.mpr (by positivity))
  have hdrop := reciprocal_power_drop hp hc hc1 hx hx1
  linarith

/-- Local successors with at least the prescribed measure growth satisfy the
    fifth-power distribution bound. Only the actual successor inequality is assumed. -/
theorem distribution_bound_of_successor_growth {α : Type*} {p c C B : ℝ}
    (hp : 1 ≤ p) (hc : 0 < c) (hc1 : c ≤ 1) (hC : 0 ≤ C)
    (mass value : α → ℝ) (admissible : α → Prop) (x₀ : α)
    (hx₀ : admissible x₀) (hμ₀ : 0 < mass x₀) (hμ₉ : mass x₀ ≤ 9 / 10)
    (hnext : ∀ x, admissible x → mass x₀ ≤ mass x → mass x ≤ 9 / 10 →
      ∃ y, admissible y ∧ mass x + distributionStep p c (mass x) ≤ mass y ∧
        mass y ≤ 1 ∧ value x ≤ value y +
          C * p ^ 2 * (mass x) ^ (-(1 / p)) * Real.log (p / mass x₀))
    (hterminal : ∀ x, admissible x → 9 / 10 < mass x → mass x ≤ 1 → value x ≤ B) :
    value x₀ ≤ B + (4 * C / c) * p ^ 5 *
      (mass x₀) ^ (-(2 / p)) * Real.log (p / mass x₀) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hlog : 0 ≤ Real.log (p / mass x₀) := by
    apply Real.log_nonneg
    exact (one_le_div hμ₀).mpr (by linarith)
  let coefficient : ℝ := (4 * C / c) * p ^ 5 * Real.log (p / mass x₀)
  have hcoefficient : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  let adjusted (x : α) := value x - coefficient * (mass x) ^ (-(2 / p))
  let good (x : α) : Prop := admissible x ∧ mass x ≤ 1
  have hsuccessor (x : α) (hx : good x) (hxlo : mass x₀ ≤ mass x)
      (hxhi : mass x ≤ 9 / 10) :
      ∃ y, good y ∧ mass x + distributionStep p c (mass x₀) ≤ mass y ∧
        adjusted x ≤ adjusted y := by
    obtain ⟨y, hy, hgrow, hy1, hvalue⟩ := hnext x hx.1 hxlo hxhi
    have hxpos : 0 < mass x := hμ₀.trans_le hxlo
    have hmono := distributionStep_mono hp0 hc.le hμ₀.le hxlo
    have hdrop := reciprocal_power_drop_of_growth hp hc hc1 hxpos hx.2 hgrow
    have hscaled := mul_le_mul_of_nonneg_left hdrop hcoefficient
    have hscale : coefficient * (c / (4 * p ^ 3) * (mass x) ^ (-(1 / p))) =
        C * p ^ 2 * (mass x) ^ (-(1 / p)) * Real.log (p / mass x₀) := by
      dsimp [coefficient]
      field_simp
    rw [hscale] at hscaled
    refine ⟨y, ⟨hy, hy1⟩, by linarith, ?_⟩
    dsimp [adjusted]
    nlinarith
  obtain ⟨y, hy, hymass, hval⟩ := exists_terminal_of_positive_progress mass adjusted good x₀
    (9 / 10) (distributionStep p c (mass x₀)) ⟨hx₀, by linarith⟩
    (distributionStep_pos hp0 hc hμ₀) hsuccessor
  have hB := hterminal y hy.1 hymass hy.2
  have hypos : 0 < mass y := by linarith
  have hpot : 0 ≤ coefficient * (mass y) ^ (-(2 / p)) :=
    mul_nonneg hcoefficient (Real.rpow_nonneg hypos.le _)
  dsimp [adjusted, coefficient] at hval hpot
  nlinarith

/-- The optimized logarithmic distribution estimate also holds when each
    successor increases the mass by more than the minimum required increment. -/
theorem distribution_bound_log_six_of_successor_growth {α : Type*} {c C B : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 0 ≤ C)
    (mass value : α → ℝ) (admissible : α → Prop) (x₀ : α)
    (hx₀ : admissible x₀) (hμ₀ : 0 < mass x₀) (hμ₉ : mass x₀ ≤ 9 / 10)
    (hnext : ∀ x, admissible x → mass x₀ ≤ mass x → mass x ≤ 9 / 10 →
      ∃ y, admissible y ∧ mass x +
          distributionStep (distributionMomentOrder (mass x₀) : ℝ) c (mass x) ≤ mass y ∧
        mass y ≤ 1 ∧ value x ≤ value y + C * (distributionMomentOrder (mass x₀) : ℝ) ^ 2 *
          (mass x) ^ (-(1 / (distributionMomentOrder (mass x₀) : ℝ))) *
          Real.log ((distributionMomentOrder (mass x₀) : ℝ) / mass x₀))
    (hterminal : ∀ x, admissible x → 9 / 10 < mass x → mass x ≤ 1 → value x ≤ B) :
    value x₀ ≤ B + (20480 * Real.exp 1 * C / c) * (Real.log (2 / mass x₀)) ^ 6 := by
  have hp : (1 : ℝ) ≤ distributionMomentOrder (mass x₀) := by
    exact_mod_cast (distributionMomentOrder_bounds hμ₀ (by linarith)).1
  have h := distribution_bound_of_successor_growth hp hc hc1 hC mass value admissible x₀
    hx₀ hμ₀ hμ₉ hnext hterminal
  have hcost := mul_le_mul_of_nonneg_left
    (optimized_distribution_cost_le hμ₀ (by linarith))
    (show 0 ≤ 4 * C / c by positivity)
  have hfactor : (4 * C / c) * (5120 * Real.exp 1 * Real.log (2 / mass x₀) ^ 6) =
      (20480 * Real.exp 1 * C / c) * Real.log (2 / mass x₀) ^ 6 := by ring
  rw [hfactor] at hcost
  nlinarith

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.DistributionIteration

/-!
# Distribution recurrences on spaces of states

A local successor can be a measurable set, rather than a scalar measure. Finite
induction lifts the deterministic measure orbit to such states and accumulates
the local logarithmic losses. An admissibility predicate records the conditions
preserved by each successor.
-/

noncomputable section

open scoped BigOperators

namespace Erdos522

/-- Local successors along a finite scalar sequence produce an admissible terminal
    state, with the accumulated loss bounded by the corresponding finite sum. -/
theorem exists_endpoint_of_finite_successors {α : Type*}
    (mass value : α → ℝ) (admissible : α → Prop) (x₀ : α)
    (μ loss : ℕ → ℝ) (M : ℕ) (hx₀ : admissible x₀) (hμ₀ : mass x₀ = μ 0)
    (hnext : ∀ k < M, ∀ x, admissible x → mass x = μ k →
      ∃ y, admissible y ∧ mass y = μ (k + 1) ∧ value x ≤ value y + loss k) :
    ∃ y, admissible y ∧ mass y = μ M ∧
      value x₀ ≤ value y + ∑ k ∈ Finset.range M, loss k := by
  have hrec : ∀ k, k ≤ M → ∃ y, admissible y ∧ mass y = μ k ∧
      value x₀ ≤ value y + ∑ i ∈ Finset.range k, loss i := by
    intro k
    induction k with
    | zero =>
        intro _
        exact ⟨x₀, hx₀, hμ₀, by simp⟩
    | succ k ih =>
        intro hk
        obtain ⟨x, hx, hmx, hval⟩ := ih (by omega)
        obtain ⟨y, hy, hmy, hstep⟩ := hnext k (by omega) x hx hmx
        refine ⟨y, hy, hmy, ?_⟩
        rw [Finset.sum_range_succ]
        linarith
  exact hrec M le_rfl

/-- An admissible successor at each preterminal mass, together with a terminal
    bound, gives the explicit fifth-power distribution estimate. -/
theorem distribution_successor_bound {α : Type*} {p c C B : ℝ}
    (hp : 1 ≤ p) (hc : 0 < c) (hc9 : c ≤ 1 / 9) (hC : 0 ≤ C)
    (mass value : α → ℝ) (admissible : α → Prop) (x₀ : α)
    (hx₀ : admissible x₀) (hμ₀ : 0 < mass x₀) (hμ₉ : mass x₀ ≤ 9 / 10)
    (hnext : ∀ x, admissible x → mass x₀ ≤ mass x → mass x ≤ 9 / 10 →
      ∃ y, admissible y ∧ mass y = mass x + distributionStep p c (mass x) ∧
        value x ≤ value y +
          C * p ^ 2 * (mass x) ^ (-(1 / p)) * Real.log (p / mass x₀))
    (hterminal : ∀ x, admissible x → 9 / 10 < mass x → mass x ≤ 1 → value x ≤ B) :
    value x₀ ≤ B + (4 * C / c) * p ^ 5 *
      (mass x₀) ^ (-(2 / p)) * Real.log (p / mass x₀) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  obtain ⟨M, _, _, hpre, hlast, hlast1⟩ :=
    exists_distribution_crossing_le_one hp hc hc9 hμ₀ hμ₉
  let μ : ℕ → ℝ := distributionOrbit p c (mass x₀)
  let loss (k : ℕ) : ℝ := C * p ^ 2 * (μ k) ^ (-(1 / p)) * Real.log (p / mass x₀)
  have hinit (k : ℕ) : mass x₀ ≤ μ k := distributionOrbit_ge_initial hp0 hc hμ₀ k
  have hprob (k : ℕ) (hk : k ≤ M) : 0 < μ k ∧ μ k ≤ 1 := by
    refine ⟨hμ₀.trans_le (hinit k), ?_⟩
    rcases lt_or_eq_of_le hk with hlt | rfl
    · have h := hpre k hlt
      change μ k ≤ 9 / 10 at h
      linarith
    · exact hlast1
  have hstep (k : ℕ) (_ : k < M) :
      μ (k + 1) = μ k + distributionStep p c (μ k) := rfl
  have hsucc (k : ℕ) (hk : k < M) (x : α) (hx : admissible x) (hmx : mass x = μ k) :
      ∃ y, admissible y ∧ mass y = μ (k + 1) ∧ value x ≤ value y + loss k := by
    have hxlo : mass x₀ ≤ mass x := hmx ▸ hinit k
    have hxhi : mass x ≤ 9 / 10 := hmx ▸ hpre k hk
    obtain ⟨y, hy, hmy, hval⟩ := hnext x hx hxlo hxhi
    refine ⟨y, hy, ?_, ?_⟩
    · rw [hmy, hmx, hstep k hk]
    · simpa only [loss, ← hmx] using hval
  obtain ⟨y, hy, hmy, hval⟩ :=
    exists_endpoint_of_finite_successors mass value admissible x₀ μ loss M hx₀ rfl hsucc
  have hsum := sum_distribution_losses_le hp hc (by linarith) hC μ loss M hprob hstep
    (fun _ _ => le_rfl)
  have hB := hterminal y hy (hmy ▸ hlast) (hmy ▸ hlast1)
  simp only [μ, distributionOrbit_zero] at hsum
  linarith

/-- Choosing the moment order from the initial mass gives a sixth-power
    logarithmic estimate for an arbitrary admissible successor construction. -/
theorem distribution_successor_bound_log_six {α : Type*} {c C B : ℝ}
    (hc : 0 < c) (hc9 : c ≤ 1 / 9) (hC : 0 ≤ C)
    (mass value : α → ℝ) (admissible : α → Prop) (x₀ : α)
    (hx₀ : admissible x₀) (hμ₀ : 0 < mass x₀) (hμ₉ : mass x₀ ≤ 9 / 10)
    (hnext : ∀ x, admissible x → mass x₀ ≤ mass x → mass x ≤ 9 / 10 →
      ∃ y, admissible y ∧ mass y = mass x +
          distributionStep (distributionMomentOrder (mass x₀) : ℝ) c (mass x) ∧
        value x ≤ value y + C * (distributionMomentOrder (mass x₀) : ℝ) ^ 2 *
          (mass x) ^ (-(1 / (distributionMomentOrder (mass x₀) : ℝ))) *
          Real.log ((distributionMomentOrder (mass x₀) : ℝ) / mass x₀))
    (hterminal : ∀ x, admissible x → 9 / 10 < mass x → mass x ≤ 1 → value x ≤ B) :
    value x₀ ≤ B + (20480 * Real.exp 1 * C / c) * (Real.log (2 / mass x₀)) ^ 6 := by
  have hp : (1 : ℝ) ≤ distributionMomentOrder (mass x₀) := by
    exact_mod_cast (distributionMomentOrder_bounds hμ₀ (by linarith)).1
  have h := distribution_successor_bound hp hc hc9 hC mass value admissible x₀
    hx₀ hμ₀ hμ₉ hnext hterminal
  have hcost := mul_le_mul_of_nonneg_left
    (optimized_distribution_cost_le hμ₀ (by linarith))
    (show 0 ≤ 4 * C / c by positivity)
  have hfactor : (4 * C / c) * (5120 * Real.exp 1 * Real.log (2 / mass x₀) ^ 6) =
      (20480 * Real.exp 1 * C / c) * Real.log (2 / mass x₀) ^ 6 := by ring
  rw [hfactor] at hcost
  nlinarith

end Erdos522

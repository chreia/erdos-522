/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.DistributionRecurrence

/-!
# Terminating distribution iterations

An increasing measure recurrence reaches a fixed positive threshold after an
explicit number of steps. The resulting finite chain turns local restricted
energy inequalities into a bound at the initial measure.
-/

noncomputable section

open scoped BigOperators

namespace Erdos522

/-- Successive additions of a real-valued increment. -/
def additiveStepOrbit (step : ℝ → ℝ) (x : ℝ) : ℕ → ℝ
  | 0 => x
  | k + 1 => additiveStepOrbit step x k + step (additiveStepOrbit step x k)

@[simp] theorem additiveStepOrbit_zero (step : ℝ → ℝ) (x : ℝ) :
    additiveStepOrbit step x 0 = x := rfl

@[simp] theorem additiveStepOrbit_succ (step : ℝ → ℝ) (x : ℝ) (k : ℕ) :
    additiveStepOrbit step x (k + 1) =
      additiveStepOrbit step x k + step (additiveStepOrbit step x k) := rfl

/-- An increment bounded below on the forward half-line gives linear growth. -/
theorem additiveStepOrbit_lower_bound (step : ℝ → ℝ) (x : ℝ)
    (hstep : 0 ≤ step x) (hmono : ∀ y, x ≤ y → step x ≤ step y) (k : ℕ) :
    x + k * step x ≤ additiveStepOrbit step x k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hx : x ≤ additiveStepOrbit step x k := by
        have hk : 0 ≤ (k : ℝ) * step x := by positivity
        linarith
      have hs := hmono _ hx
      rw [additiveStepOrbit_succ, Nat.cast_add, Nat.cast_one]
      nlinarith

/-- The orbit is strictly increasing when every forward increment is positive. -/
theorem strictMono_additiveStepOrbit (step : ℝ → ℝ) (x : ℝ)
    (hstep : 0 < step x) (hmono : ∀ y, x ≤ y → step x ≤ step y) :
    StrictMono (additiveStepOrbit step x) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hgrow := additiveStepOrbit_lower_bound step x hstep.le hmono k
  have hx : x ≤ additiveStepOrbit step x k := by
    have hk : 0 ≤ (k : ℝ) * step x := by positivity
    linarith
  have hs := hmono _ hx
  rw [additiveStepOrbit_succ]
  linarith

/-- The least crossing of a finite threshold occurs within the linear-growth bound. -/
theorem exists_first_crossing_additiveStepOrbit (step : ℝ → ℝ) (x b : ℝ)
    (hxb : x ≤ b) (hstep : 0 < step x)
    (hmono : ∀ y, x ≤ y → step x ≤ step y) :
    ∃ M : ℕ, 0 < M ∧ M ≤ ⌈(b - x) / step x⌉₊ + 1 ∧
      (∀ k < M, additiveStepOrbit step x k ≤ b) ∧
      b < additiveStepOrbit step x M := by
  classical
  let K : ℕ := ⌈(b - x) / step x⌉₊ + 1
  have hK : b < additiveStepOrbit step x K := by
    have hceil : (b - x) / step x ≤ (⌈(b - x) / step x⌉₊ : ℝ) := Nat.le_ceil _
    have hmul := (div_le_iff₀ hstep).mp hceil
    have hgrow := additiveStepOrbit_lower_bound step x hstep.le hmono K
    have hKcast : (K : ℝ) = (⌈(b - x) / step x⌉₊ : ℝ) + 1 := by
      simp only [K, Nat.cast_add, Nat.cast_one]
    rw [hKcast] at hgrow
    nlinarith
  have hex : ∃ k, b < additiveStepOrbit step x k := ⟨K, hK⟩
  refine ⟨Nat.find hex, ?_, Nat.find_min' hex hK, ?_, Nat.find_spec hex⟩
  · by_contra h
    have hz : Nat.find hex = 0 := by omega
    have hb := Nat.find_spec hex
    simp only [hz, additiveStepOrbit_zero] at hb
    exact not_lt_of_ge hxb hb
  · intro k hk
    exact le_of_not_gt (Nat.find_min hex hk)

/-- The distribution increment is positive at a positive measure. -/
theorem distributionStep_pos {p c μ : ℝ} (hp : 0 < p) (hc : 0 < c)
    (hμ : 0 < μ) : 0 < distributionStep p c μ := by
  unfold distributionStep
  positivity

/-- For a fixed moment parameter, the distribution increment increases with the measure. -/
theorem distributionStep_mono {p c x y : ℝ} (hp : 0 < p) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    distributionStep p c x ≤ distributionStep p c y := by
  unfold distributionStep
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy (by positivity)) (by positivity)

/-- The deterministic measure sequence used in the distribution iteration. -/
def distributionOrbit (p c μ : ℝ) : ℕ → ℝ :=
  additiveStepOrbit (distributionStep p c) μ

@[simp] theorem distributionOrbit_zero (p c μ : ℝ) : distributionOrbit p c μ 0 = μ := rfl

@[simp] theorem distributionOrbit_succ (p c μ : ℝ) (k : ℕ) :
    distributionOrbit p c μ (k + 1) = distributionOrbit p c μ k +
      distributionStep p c (distributionOrbit p c μ k) := rfl

/-- Every measure in the orbit is at least its initial positive measure. -/
theorem distributionOrbit_ge_initial {p c μ : ℝ} (hp : 0 < p) (hc : 0 < c)
    (hμ : 0 < μ) (k : ℕ) : μ ≤ distributionOrbit p c μ k := by
  have hs := distributionStep_pos hp hc hμ
  have hgrow := additiveStepOrbit_lower_bound (distributionStep p c) μ hs.le
    (fun _ hy => distributionStep_mono hp hc.le hμ.le hy) k
  have hk : 0 ≤ (k : ℝ) * distributionStep p c μ := by positivity
  exact le_trans (by linarith) hgrow

/-- The distribution orbit is strictly increasing. -/
theorem strictMono_distributionOrbit {p c μ : ℝ} (hp : 0 < p) (hc : 0 < c)
    (hμ : 0 < μ) : StrictMono (distributionOrbit p c μ) :=
  strictMono_additiveStepOrbit (distributionStep p c) μ (distributionStep_pos hp hc hμ)
    (fun _ hy => distributionStep_mono hp hc.le hμ.le hy)

/-- The measure orbit crosses `9/10` in at most the explicitly specified number
    of steps. Its final measure is at most `9/5`. -/
theorem exists_distribution_crossing {p c μ : ℝ} (hp : 1 ≤ p)
    (hc : 0 < c) (hc1 : c ≤ 1) (hμ : 0 < μ) (hμ9 : μ ≤ 9 / 10) :
    ∃ M : ℕ, 0 < M ∧
      M ≤ ⌈(9 / 10 - μ) / distributionStep p c μ⌉₊ + 1 ∧
      (∀ k < M, distributionOrbit p c μ k ≤ 9 / 10) ∧
      9 / 10 < distributionOrbit p c μ M ∧ distributionOrbit p c μ M ≤ 9 / 5 := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  obtain ⟨M, hM0, hMK, hpre, hlast⟩ :=
    exists_first_crossing_additiveStepOrbit (distributionStep p c) μ (9 / 10) hμ9
      (distributionStep_pos hp0 hc hμ)
      (fun _ hy => distributionStep_mono hp0 hc.le hμ.le hy)
  refine ⟨M, hM0, hMK, hpre, hlast, ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hM0)
  have hk9 : distributionOrbit p c μ k ≤ 9 / 10 := hpre k (by omega)
  have hk0 : 0 < distributionOrbit p c μ k :=
    hμ.trans_le (distributionOrbit_ge_initial hp0 hc hμ k)
  have hs := distributionStep_le hp hc1 hk0 (by linarith)
  rw [distributionOrbit_succ]
  linarith

/-- On the probability interval the increment is at most `c` times the measure. -/
theorem distributionStep_le_mul {p c μ : ℝ} (hp : 1 ≤ p) (hc : 0 ≤ c)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) : distributionStep p c μ ≤ c * μ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  have hdiv : c / p ^ 2 ≤ c := by
    apply (div_le_iff₀ (sq_pos_of_pos hp0)).mpr
    nlinarith
  have hpow : μ ^ (1 / p) ≤ 1 := Real.rpow_le_one hμ.le hμ1 (by positivity)
  unfold distributionStep
  rw [Real.rpow_add hμ, Real.rpow_one]
  calc
    _ ≤ c * (μ * 1) := by gcongr
    _ = c * μ := by ring

/-- With `c ≤ 1/9`, the first measure above `9/10` is still a probability. -/
theorem exists_distribution_crossing_le_one {p c μ : ℝ} (hp : 1 ≤ p)
    (hc : 0 < c) (hc9 : c ≤ 1 / 9) (hμ : 0 < μ) (hμ9 : μ ≤ 9 / 10) :
    ∃ M : ℕ, 0 < M ∧
      M ≤ ⌈(9 / 10 - μ) / distributionStep p c μ⌉₊ + 1 ∧
      (∀ k < M, distributionOrbit p c μ k ≤ 9 / 10) ∧
      9 / 10 < distributionOrbit p c μ M ∧ distributionOrbit p c μ M ≤ 1 := by
  obtain ⟨M, hM0, hMK, hpre, hlast, _⟩ :=
    exists_distribution_crossing hp hc (by linarith) hμ hμ9
  refine ⟨M, hM0, hMK, hpre, hlast, ?_⟩
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hM0)
  have hk9 : distributionOrbit p c μ k ≤ 9 / 10 := hpre k (by omega)
  have hk0 : 0 < distributionOrbit p c μ k :=
    hμ.trans_le (distributionOrbit_ge_initial hp0 hc hμ k)
  have hs := distributionStep_le_mul hp hc.le hk0 (by linarith)
  have hprod : c * distributionOrbit p c μ k ≤ (1 / 9 : ℝ) * (9 / 10) := by
    gcongr
  rw [distributionOrbit_succ]
  linarith

/-- Local logarithmic-loss inequalities and a terminal bound imply the global
    sixth-power bound, using an explicit finite crossing of the threshold. -/
theorem distribution_recurrence_bound {c C μ B : ℝ}
    (hc : 0 < c) (hc9 : c ≤ 1 / 9) (hC : 0 ≤ C)
    (hμ : 0 < μ) (hμ9 : μ ≤ 9 / 10) (value : ℝ → ℝ)
    (hlocal : ∀ x, μ ≤ x → x ≤ 9 / 10 →
      value x ≤ value (x + distributionStep (distributionMomentOrder μ : ℝ) c x) +
        C * (distributionMomentOrder μ : ℝ) ^ 2 *
          x ^ (-(1 / (distributionMomentOrder μ : ℝ))) *
          Real.log ((distributionMomentOrder μ : ℝ) / μ))
    (hterminal : ∀ x, 9 / 10 < x → x ≤ 1 → value x ≤ B) :
    value μ ≤ B + (20480 * Real.exp 1 * C / c) * (Real.log (2 / μ)) ^ 6 := by
  let p : ℝ := distributionMomentOrder μ
  have hp : 1 ≤ p := by
    dsimp [p]
    exact_mod_cast (distributionMomentOrder_bounds hμ (by linarith)).1
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  obtain ⟨M, hM0, _, hpre, hlast, hlast1⟩ :=
    exists_distribution_crossing_le_one hp hc hc9 hμ hμ9
  let orbit := distributionOrbit p c μ
  have hinit (k : ℕ) : μ ≤ orbit k := distributionOrbit_ge_initial hp0 hc hμ k
  have hprob (k : ℕ) (hk : k ≤ M) : 0 < orbit k ∧ orbit k ≤ 1 := by
    refine ⟨hμ.trans_le (hinit k), ?_⟩
    rcases lt_or_eq_of_le hk with hlt | rfl
    · have h := hpre k hlt
      change orbit k ≤ 9 / 10 at h
      linarith
    · exact hlast1
  have hstep (k : ℕ) (_ : k < M) : orbit (k + 1) = orbit k +
      distributionStep (distributionMomentOrder (orbit 0) : ℝ) c (orbit k) := by
    simp only [orbit, distributionOrbit_zero]
    rfl
  have hval (k : ℕ) (hk : k < M) : value (orbit k) ≤ value (orbit (k + 1)) +
      C * (distributionMomentOrder (orbit 0) : ℝ) ^ 2 *
        (orbit k) ^ (-(1 / (distributionMomentOrder (orbit 0) : ℝ))) *
        Real.log ((distributionMomentOrder (orbit 0) : ℝ) / orbit 0) := by
    simpa only [orbit, distributionOrbit_zero, distributionOrbit_succ, p] using
      hlocal (orbit k) (hinit k) (hpre k hk)
  have hbound := finite_distribution_recurrence_bound hc (by linarith) hC orbit
    (fun k => value (orbit k)) M hprob hstep hval
  have hterm := hterminal (orbit M) hlast hlast1
  simp only [orbit, distributionOrbit_zero] at hbound
  linarith

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Limits.RealPowerLocalization

/-!
# Admissible scales for sparse degree schedules

The logarithmic cutoff, derivative threshold, exceptional-root count, and
matching window can be chosen for every real degree exponent greater than
two. The strict margins control the actual localization inequalities and
make each displayed second-moment failure envelope summable.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- The strict power inequalities for logarithmic concentration, annular
derivative nondegeneracy, and Taylor localization. -/
structure AdmissibleSparseDegreeScales (q t ℓ d κ : ℝ) : Prop where
  logarithmic_pos : 0 < t
  derivative_pos : 0 < ℓ
  count_pos : 0 < d
  window_pos : 0 < κ
  mean_density : d < 4 * ℓ
  mean_gaussian_error : d < 1 / 2 - 2 * ℓ
  excluded_sectors : d < 1 / 2
  mesh_summability : 1 < q * (1 / 2 - 4 * ℓ - 2 * d)
  occupation_summability : 1 < q * (1 / 2 - 4 * t)
  clipped_log_summability : 1 < q * (1 / 2 - 2 * t)
  isolation : 2 * ℓ < 1 / (2 * q)
  logarithmic_window : κ < t
  displacement_window : ℓ + κ < 1 / (2 * q)

/-- Explicit admissible scales for every real `q > 2`. -/
theorem admissible_sparse_degree_scales {q : ℝ} (hq : 2 < q) :
    let Δ := 1 / 2 - 1 / q
    let t := Δ / 16
    let ℓ := min (Δ / 32) (1 / (16 * q))
    let d := ℓ
    let κ := min (t / 2) (1 / (8 * q))
    AdmissibleSparseDegreeScales q t ℓ d κ := by
  have hq0 : 0 < q := by linarith
  have hi : 0 < 1 / q := by positivity
  have hi2 : 1 / q < 1 / 2 := by
    apply (div_lt_div_iff₀ hq0 (by norm_num : (0 : ℝ) < 2)).mpr
    linarith
  let Δ := 1 / 2 - 1 / q
  let t := Δ / 16
  let ℓ := min (Δ / 32) (1 / (16 * q))
  let κ := min (t / 2) (1 / (8 * q))
  have hΔ : 0 < Δ := by dsimp [Δ]; linarith
  have hΔhalf : Δ < 1 / 2 := by dsimp [Δ]; linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have hℓ : 0 < ℓ := lt_min (by dsimp [Δ]; linarith) (by positivity)
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  have hℓΔ : ℓ ≤ Δ / 32 := min_le_left _ _
  have hℓq : ℓ ≤ 1 / (16 * q) := min_le_right _ _
  have hκt : κ ≤ t / 2 := min_le_left _ _
  have hκq : κ ≤ 1 / (8 * q) := min_le_right _ _
  have hsummable {a : ℝ} (ha : a < Δ) : 1 < q * (1 / 2 - a) := by
    have hgap : 1 / q < 1 / 2 - a := by dsimp [Δ] at ha; linarith
    have hm := mul_lt_mul_of_pos_left hgap hq0
    simpa only [mul_one_div_cancel hq0.ne'] using hm
  have hdiv16 : 1 / (16 * q) = (1 / q) / 16 := by ring
  have hdiv8 : 1 / (8 * q) = (1 / q) / 8 := by ring
  have hdiv2 : 1 / (2 * q) = (1 / q) / 2 := by ring
  change AdmissibleSparseDegreeScales q t ℓ ℓ κ
  refine ⟨ht, hℓ, hℓ, hκ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · have h := hsummable (a := 6 * ℓ) (by linarith)
    nlinarith
  · apply hsummable
    dsimp [t]
    linarith
  · apply hsummable
    dsimp [t]
    linarith
  · rw [hdiv2]
    rw [hdiv16] at hℓq
    linarith
  · linarith
  · rw [hdiv2]
    rw [hdiv16] at hℓq
    rw [hdiv8] at hκq
    linarith

/-- The original fixed powers are admissible throughout the stated open range. -/
theorem admissible_fixed_sparse_degree_scales {q : ℝ}
    (hq : 8 / 3 < q) (hq16 : q < 16) :
    AdmissibleSparseDegreeScales q (1 / 32) (1 / 64) (1 / 32) (1 / 64) := by
  have hq0 : 0 < q := by linarith
  have hmargin : (1 / 32 : ℝ) < 1 / (2 * q) := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * q)).mpr
    linarith
  norm_num at hmargin
  constructor <;> norm_num <;> linarith

/-- A positive logarithmic cutoff with summable occupation failures forces `q > 2`. -/
theorem two_lt_of_occupation_summability {q t : ℝ} (hq : 0 < q) (ht : 0 < t)
    (hs : 1 < q * (1 / 2 - 4 * t)) : 2 < q := by
  nlinarith [mul_pos hq ht]

/-- Every admissible tuple gives the actual Taylor-isolation and displacement
inequalities for the maximal appended tail. -/
theorem AdmissibleSparseDegreeScales.eventually_root_localization
    {q t ℓ d κ : ℝ} (h : AdmissibleSparseDegreeScales q t ℓ d κ)
    (hq : 0 < q) (K K' : ℝ) :
    ∀ᶠ j : ℕ in atTop,
      let N := realPowerDegree q j
      let a := TailSupremum.tailAmplitude N (realPowerBlockLength q j) K'
      let threshold := (N : ℝ) ^ (3 / 2 - ℓ)
      0 < a ∧ 0 < threshold ∧
        4 * DerivativeSupremum.secondDerivativeEnvelope N K * a ≤ threshold ^ 2 ∧
        2 * a / threshold ≤ 1 / N ∧ 2 * a / threshold < (N : ℝ) ^ (-1 - κ) :=
  eventually_real_power_root_localization
    (by linarith [two_lt_of_occupation_summability hq h.logarithmic_pos h.occupation_summability])
    h.window_pos.le h.isolation h.displacement_window K K'

/-- All three second-moment failure envelopes are summable, including arbitrary
fixed logarithmic factors. -/
theorem AdmissibleSparseDegreeScales.summable_second_moment_envelopes
    {q t ℓ d κ : ℝ} (h : AdmissibleSparseDegreeScales q t ℓ d κ)
    (hq : 0 < q) (k : ℕ) :
    Summable (fun j : ℕ => (realPowerDegree q j : ℝ) ^ (-1 / 2 + 4 * t) *
      (Real.log (realPowerDegree q j)) ^ k) ∧
    Summable (fun j : ℕ => (realPowerDegree q j : ℝ) ^ (-1 / 2 + 2 * t) *
      (Real.log (realPowerDegree q j)) ^ k) ∧
    Summable (fun j : ℕ => (realPowerDegree q j : ℝ) ^ (-1 / 2 + 4 * ℓ + 2 * d) *
      (Real.log (realPowerDegree q j)) ^ k) := by
  refine ⟨summable_realPowerDegree_rpow_mul_log_pow hq ?_ k,
    summable_realPowerDegree_rpow_mul_log_pow hq ?_ k,
    summable_realPowerDegree_rpow_mul_log_pow hq ?_ k⟩
  · nlinarith [h.occupation_summability]
  · nlinarith [h.clipped_log_summability]
  · nlinarith [h.mesh_summability]

end Erdos522

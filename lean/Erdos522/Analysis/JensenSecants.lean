/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Basic.ZeroCount
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Radial logarithmic potentials and multiplicity-counted Jensen secants. -/

noncomputable section

namespace Erdos522

open Polynomial Real

/-- The normalized angular average of the logarithm of a polynomial's modulus. -/
def logCircleAverage (P : Polynomial ℂ) (r : ℝ) : ℝ :=
  Real.circleAverage (fun z ↦ Real.log ‖P.eval z‖) 0 r

/-- The contribution of one root to the logarithmic potential at radius `r`. -/
def rootLogPotential (z : ℂ) (r : ℝ) : ℝ := Real.log (max r ‖z‖)

theorem rootLogPotential_mono (z : ℂ) {r R : ℝ} (hr : 0 < r) (h : r ≤ R) :
    rootLogPotential z r ≤ rootLogPotential z R := by
  apply Real.log_le_log
  · exact lt_of_lt_of_le hr (le_max_left _ _)
  · exact max_le_max h le_rfl

theorem rootLogPotential_increment_lower (z : ℂ) {r R : ℝ}
    (hr : 0 < r) (h : r < R) :
    (if ‖z‖ ≤ r then Real.log (R / r) else 0) ≤
      rootLogPotential z R - rootLogPotential z r := by
  by_cases hz : ‖z‖ ≤ r
  · simp only [hz, ite_true, rootLogPotential, max_eq_left hz,
      max_eq_left (hz.trans h.le)]
    rw [Real.log_div (ne_of_gt (hr.trans h)) (ne_of_gt hr)]
  · simp only [hz, ite_false]
    exact sub_nonneg.mpr (rootLogPotential_mono z hr h.le)

theorem rootLogPotential_increment_upper (z : ℂ) {r R : ℝ}
    (hr : 0 < r) (h : r < R) :
    rootLogPotential z R - rootLogPotential z r ≤
      (if ‖z‖ ≤ R then Real.log (R / r) else 0) := by
  by_cases hz : ‖z‖ ≤ R
  · simp only [hz, ite_true, rootLogPotential, max_eq_left hz]
    rw [Real.log_div (ne_of_gt (hr.trans h)) (ne_of_gt hr)]
    exact sub_le_sub_left (Real.log_le_log hr (le_max_left _ _)) _
  · have hzR : R ≤ ‖z‖ := (lt_of_not_ge hz).le
    simp only [hz, ite_false, rootLogPotential, max_eq_right hzR,
      max_eq_right (h.le.trans hzR), sub_self, le_refl]

/-- The sum of the radial logarithmic contributions of a root multiset. -/
def rootLogSum (s : Multiset ℂ) (r : ℝ) : ℝ :=
  (s.map (fun z ↦ rootLogPotential z r)).sum

theorem rootLogSum_secant_lower (s : Multiset ℂ) {r R : ℝ}
    (hr : 0 < r) (h : r < R) :
    (s.countP (fun z ↦ ‖z‖ ≤ r) : ℝ) * Real.log (R / r) ≤
      rootLogSum s R - rootLogSum s r := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp [rootLogSum]
  | cons z s ih =>
    have hz := rootLogPotential_increment_lower z hr h
    by_cases hm : ‖z‖ ≤ r <;>
      simp [rootLogSum, hm] at * <;> linarith

theorem rootLogSum_secant_upper (s : Multiset ℂ) {r R : ℝ}
    (hr : 0 < r) (h : r < R) :
    rootLogSum s R - rootLogSum s r ≤
      (s.countP (fun z ↦ ‖z‖ ≤ R) : ℝ) * Real.log (R / r) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp [rootLogSum]
  | cons z s ih =>
    have hz := rootLogPotential_increment_upper z hr h
    by_cases hm : ‖z‖ ≤ R <;>
      simp [rootLogSum, hm] at * <;> linarith

theorem logCircleAverage_eq_logMahlerMeasure (P : Polynomial ℂ) (r : ℝ) :
    logCircleAverage P r = (P.comp (C (r : ℂ) * X)).logMahlerMeasure := by
  rw [logCircleAverage, Real.circleAverage_eq_circleAverage_zero_one]
  simp [Polynomial.logMahlerMeasure_def, Polynomial.eval_comp]

theorem rootLogPotential_eq_log_add_posLog (z : ℂ) {r : ℝ} (hr : 0 < r) :
    rootLogPotential z r = Real.log r + Real.posLog (‖z‖ / r) := by
  rw [rootLogPotential, Real.posLog_eq_log_max_one (div_nonneg (norm_nonneg _) hr.le)]
  by_cases hz : ‖z‖ ≤ r
  · rw [max_eq_left hz, max_eq_left ((div_le_one hr).mpr hz), Real.log_one, add_zero]
  · have hzr : r < ‖z‖ := lt_of_not_ge hz
    rw [max_eq_right hzr.le, max_eq_right ((one_le_div hr).mpr hzr.le),
      Real.log_div (ne_of_gt (hr.trans hzr)) (ne_of_gt hr)]
    ring

theorem rootLogSum_eq_log_add_posLog (s : Multiset ℂ) {r : ℝ} (hr : 0 < r) :
    rootLogSum s r = (s.card : ℝ) * Real.log r +
      (s.map (fun z ↦ Real.posLog (‖z‖ / r))).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [rootLogSum]
  | cons z s ih =>
    simp only [rootLogSum, Multiset.map_cons, Multiset.sum_cons] at ih ⊢
    rw [rootLogPotential_eq_log_add_posLog z hr, ih]
    simp only [Multiset.card_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- Jensen's formula for a polynomial, with roots counted with multiplicity. -/
theorem logCircleAverage_eq_rootLogSum (P : Polynomial ℂ) {r : ℝ} (hr : 0 < r) :
    logCircleAverage P r = Real.log ‖P.leadingCoeff‖ + rootLogSum P.roots r := by
  by_cases hp : P = 0
  · simp [hp, logCircleAverage, rootLogSum, Real.circleAverage_const]
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hd : (C (r : ℂ) * X).natDegree ≠ 0 := by
    rw [natDegree_C_mul_X _ hrc]
    decide
  have hroots : (P.comp (C (r : ℂ) * X)).roots =
      P.roots.map (fun z ↦ (r : ℂ)⁻¹ * z) := by
    simpa only [map_zero, add_zero, sub_zero, Ring.inverse_eq_inv] using
      roots_comp_C_mul_X_add_C P (r : ℂ) 0 (isUnit_iff_ne_zero.mpr hrc)
  rw [logCircleAverage_eq_logMahlerMeasure,
    logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots, leadingCoeff_comp hd,
    leadingCoeff_C_mul_X, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    Real.log_mul (norm_ne_zero_iff.mpr (leadingCoeff_ne_zero.mpr hp))
      (pow_ne_zero _ (ne_of_gt hr)), Real.log_pow, hroots, Multiset.map_map]
  rw [rootLogSum_eq_log_add_posLog _ hr, IsAlgClosed.card_roots_eq_natDegree]
  simp only [Function.comp_def, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    div_eq_mul_inv, mul_comm]
  ring

/-- The logarithmic secant lies between the two closed-disk root counts. -/
theorem radial_zero_count_bound (P : Polynomial ℂ) {r R : ℝ}
    (hr : 0 < r) (h : r < R) :
    (closedZeroCount P r : ℝ) ≤
      (logCircleAverage P R - logCircleAverage P r) / Real.log (R / r) ∧
    (logCircleAverage P R - logCircleAverage P r) / Real.log (R / r) ≤
      (closedZeroCount P R : ℝ) := by
  classical
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr h)
  have hlow := rootLogSum_secant_lower P.roots hr h
  have hupp := rootLogSum_secant_upper P.roots hr h
  rw [logCircleAverage_eq_rootLogSum P hr,
    logCircleAverage_eq_rootLogSum P (hr.trans h)]
  have hcount : ∀ t, P.roots.countP (fun z ↦ ‖z‖ ≤ t) = closedZeroCount P t := by
    intro t
    simp only [Multiset.countP_eq_card_filter, closedZeroCount, zeroCountIn,
      Set.mem_ofPred_eq]
  rw [hcount] at hlow hupp
  constructor
  · apply (le_div_iff₀ hlog).mpr
    linarith
  · apply (div_le_iff₀ hlog).mpr
    linarith

/-- Four radii bound the mass outside the closed annulus between the extreme radii. -/
theorem radial_mass_four_radii (P : Polynomial ℂ) {r₁ r₂ r₃ r₄ : ℝ}
    (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) (h₃ : 0 < r₃) (h₃₄ : r₃ < r₄) :
    (zeroCountIn P {z | ‖z‖ < r₁ ∨ r₄ < ‖z‖} : ℝ) ≤
      P.natDegree + (logCircleAverage P r₂ - logCircleAverage P r₁) /
        Real.log (r₂ / r₁) -
        (logCircleAverage P r₄ - logCircleAverage P r₃) / Real.log (r₄ / r₃) := by
  have hunion := zeroCountIn_union_le P {z | ‖z‖ < r₁} {z | r₄ < ‖z‖}
  have hcompl := zeroCountIn_add_compl P {z | ‖z‖ ≤ r₄}
  have hc : {z : ℂ | ‖z‖ ≤ r₄}ᶜ = {z | r₄ < ‖z‖} := by
    ext z
    simp
  rw [hc] at hcompl
  have hopen := openZeroCount_le_closedZeroCount P r₁
  have hl := (radial_zero_count_bound P h₁ h₁₂).1
  have hu := (radial_zero_count_bound P h₃ h₃₄).2
  have hunion' : (zeroCountIn P {z | ‖z‖ < r₁ ∨ r₄ < ‖z‖} : ℝ) ≤
      openZeroCount P r₁ + zeroCountIn P {z | r₄ < ‖z‖} := by exact_mod_cast hunion
  have hcompl' : (closedZeroCount P r₄ : ℝ) + zeroCountIn P {z | r₄ < ‖z‖} =
      P.natDegree := by exact_mod_cast hcompl
  have hopen' : (openZeroCount P r₁ : ℝ) ≤ closedZeroCount P r₁ := by
    exact_mod_cast hopen
  linarith

/-- Four logarithmic integral errors transfer to a deterministic radial-mass bound.
The common centering constant cancels in each secant. -/
theorem radial_mass_of_log_integral_errors (P : Polynomial ℂ)
    {r₁ r₂ r₃ r₄ F₁ F₂ F₃ F₄ e₁ e₂ e₃ e₄ c : ℝ}
    (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) (h₃ : 0 < r₃) (h₃₄ : r₃ < r₄)
    (he₁ : |logCircleAverage P r₁ - (F₁ + c)| ≤ e₁)
    (he₂ : |logCircleAverage P r₂ - (F₂ + c)| ≤ e₂)
    (he₃ : |logCircleAverage P r₃ - (F₃ + c)| ≤ e₃)
    (he₄ : |logCircleAverage P r₄ - (F₄ + c)| ≤ e₄) :
    (zeroCountIn P {z | ‖z‖ < r₁ ∨ r₄ < ‖z‖} : ℝ) ≤
      P.natDegree + (F₂ - F₁ + e₁ + e₂) / Real.log (r₂ / r₁) -
        (F₄ - F₃ - e₃ - e₄) / Real.log (r₄ / r₃) := by
  have hlog₁ : 0 < Real.log (r₂ / r₁) := Real.log_pos ((one_lt_div h₁).mpr h₁₂)
  have hlog₂ : 0 < Real.log (r₄ / r₃) := Real.log_pos ((one_lt_div h₃).mpr h₃₄)
  have ha : logCircleAverage P r₂ - logCircleAverage P r₁ ≤ F₂ - F₁ + e₁ + e₂ := by
    rcases abs_le.mp he₁ with ⟨he₁l, he₁u⟩
    rcases abs_le.mp he₂ with ⟨he₂l, he₂u⟩
    linarith
  have hb : F₄ - F₃ - e₃ - e₄ ≤ logCircleAverage P r₄ - logCircleAverage P r₃ := by
    rcases abs_le.mp he₃ with ⟨he₃l, he₃u⟩
    rcases abs_le.mp he₄ with ⟨he₄l, he₄u⟩
    linarith
  exact (radial_mass_four_radii P h₁ h₁₂ h₃ h₃₄).trans
    (sub_le_sub (add_le_add_right (div_le_div_of_nonneg_right ha hlog₁.le) _)
      (div_le_div_of_nonneg_right hb hlog₂.le))

end Erdos522

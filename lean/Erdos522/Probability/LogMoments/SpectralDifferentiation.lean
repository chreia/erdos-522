/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.SpectralWeights
import Erdos522.Probability.RademacherLogMoments
import Erdos522.Analysis.ExponentialIntegration

/-!
# Local spectra and differential multipliers

The frequencies within `2 / τ` of a center form a local spectral cluster.
For Fourier coefficients supported within `1 / τ` of that center, the
corresponding constant-coefficient differential operator has multiplier bounded
by the clipped spectral weight, with the exact angular factor `6π / τ`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Erdos522.LogMoments

/-- The spectral frequencies within the open interval of radius `2 / τ`, with
    the original multiplicities retained. -/
def spectralCluster (τ center : ℝ) (Λ : Multiset ℝ) : Multiset ℝ :=
  Λ.filter fun ξ => |ξ - center| < 2 / τ

/-- At a point within `1 / τ` of the center, a frequency outside the cluster
    contributes the factor one to the clipped spectral weight. -/
theorem clipped_distance_eq_one_of_outside_cluster {τ center x ξ : ℝ}
    (hτ : 0 < τ) (hx : |x - center| ≤ 1 / τ)
    (hξ : ¬ |ξ - center| < 2 / τ) : min 1 (τ * |x - ξ|) = 1 := by
  apply min_eq_left
  have hfar : 2 / τ ≤ |ξ - center| := le_of_not_gt hξ
  have htriangle := abs_sub_le ξ x center
  rw [abs_sub_comm ξ x] at htriangle
  have hgap : 1 / τ ≤ |x - ξ| := by
    calc
      1 / τ = 2 / τ - 1 / τ := by ring
      _ ≤ |x - ξ| := by linarith
  have := (div_le_iff₀ hτ).mp hgap
  nlinarith

/-- Removing the distant spectral frequencies does not change the local weight. -/
theorem spectralWeight_cluster_eq {τ center x : ℝ} (hτ : 0 < τ)
    (hx : |x - center| ≤ 1 / τ) (Λ : Multiset ℝ) :
    spectralWeight τ (spectralCluster τ center Λ) x = spectralWeight τ Λ x := by
  induction Λ using Multiset.induction_on with
  | empty => simp [spectralCluster]
  | cons ξ Λ ih =>
      by_cases hξ : |ξ - center| < 2 / τ
      · simpa only [spectralCluster, Multiset.filter_cons_of_pos
          (p := fun z : ℝ => |z - center| < 2 / τ) Λ hξ,
          spectralWeight_cons] using congrArg (min 1 (τ * |x - ξ|) * ·) ih
      · simpa only [spectralCluster, Multiset.filter_cons_of_neg
          (p := fun z : ℝ => |z - center| < 2 / τ) Λ hξ,
          spectralWeight_cons, clipped_distance_eq_one_of_outside_cluster hτ hx hξ,
          one_mul] using ih

/-- A nearby frequency has distance at most three times its clipped distance,
    divided by the spectral scale. -/
theorem distance_le_three_div_mul_clipped {τ center x ξ : ℝ} (hτ : 0 < τ)
    (hx : |x - center| ≤ 1 / τ) (hξ : |ξ - center| ≤ 2 / τ) :
    |x - ξ| ≤ (3 / τ) * min 1 (τ * |x - ξ|) := by
  have htriangle := abs_sub_le x center ξ
  rw [abs_sub_comm center ξ] at htriangle
  have hdist : |x - ξ| ≤ 3 / τ := by
    calc
      |x - ξ| ≤ 1 / τ + 2 / τ := by linarith
      _ = 3 / τ := by ring
  by_cases hclip : 1 ≤ τ * |x - ξ|
  · simpa only [min_eq_left hclip, mul_one] using hdist
  · rw [min_eq_right (le_of_not_ge hclip)]
    have heq : (3 / τ) * (τ * |x - ξ|) = 3 * |x - ξ| := by field_simp
    rw [heq]
    linarith [abs_nonneg (x - ξ)]

/-- The Fourier multiplier of the product of the first-order operators with
    frequencies in a multiset. -/
def spectralDerivativeMultiplier (Λ : Multiset ℝ) (x : ℝ) : ℂ :=
  (Λ.map fun ξ => frequencyMultiplier (x - ξ)).prod

@[simp] theorem spectralDerivativeMultiplier_zero (x : ℝ) :
    spectralDerivativeMultiplier 0 x = 1 := by simp [spectralDerivativeMultiplier]

@[simp] theorem spectralDerivativeMultiplier_cons (ξ x : ℝ) (Λ : Multiset ℝ) :
    spectralDerivativeMultiplier (ξ ::ₘ Λ) x =
      frequencyMultiplier (x - ξ) * spectralDerivativeMultiplier Λ x := by
  simp [spectralDerivativeMultiplier]

/-- Differentiation of a character has modulus exactly `2π` times its frequency. -/
theorem norm_frequencyMultiplier (ξ : ℝ) :
    ‖frequencyMultiplier ξ‖ = 2 * Real.pi * |ξ| := by
  simp [frequencyMultiplier, Complex.norm_real,
    abs_of_pos Real.pi_pos]

/-- Multiplicities in the spectrum give the corresponding powers in the
    differential multiplier. -/
theorem norm_spectralDerivativeMultiplier (Λ : Multiset ℝ) (x : ℝ) :
    ‖spectralDerivativeMultiplier Λ x‖ =
      (2 * Real.pi) ^ Λ.card * (Λ.map fun ξ => |x - ξ|).prod := by
  induction Λ using Multiset.induction_on with
  | empty => simp
  | cons ξ Λ ih =>
      simp only [spectralDerivativeMultiplier_cons, norm_mul, norm_frequencyMultiplier,
        ih, Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ]
      ring

/-- On a local Fourier band, the cluster differential multiplier is controlled
    by the full clipped spectral weight. -/
theorem norm_cluster_derivativeMultiplier_le {τ center x : ℝ} (hτ : 0 < τ)
    (hx : |x - center| ≤ 1 / τ) (Λ : Multiset ℝ) :
    ‖spectralDerivativeMultiplier (spectralCluster τ center Λ) x‖ ≤
      (6 * Real.pi / τ) ^ (spectralCluster τ center Λ).card * spectralWeight τ Λ x := by
  have hlocal (Γ : Multiset ℝ) (hΓ : ∀ ξ ∈ Γ, |ξ - center| ≤ 2 / τ) :
      ‖spectralDerivativeMultiplier Γ x‖ ≤
        (6 * Real.pi / τ) ^ Γ.card * spectralWeight τ Γ x := by
    induction Γ using Multiset.induction_on with
    | empty => simp
    | cons ξ Γ ih =>
        have hξ := hΓ ξ (Multiset.mem_cons_self _ _)
        have hΓ' : ∀ ξ ∈ Γ, |ξ - center| ≤ 2 / τ :=
          fun ξ hξ => hΓ ξ (Multiset.mem_cons_of_mem hξ)
        have hfactor : ‖frequencyMultiplier (x - ξ)‖ ≤
            (6 * Real.pi / τ) * min 1 (τ * |x - ξ|) := by
          rw [norm_frequencyMultiplier]
          have h := mul_le_mul_of_nonneg_left
            (distance_le_three_div_mul_clipped hτ hx hξ) (by positivity : 0 ≤ 2 * Real.pi)
          convert h using 1; ring
        rw [spectralDerivativeMultiplier_cons, norm_mul, Multiset.card_cons,
          spectralWeight_cons, pow_succ]
        have hfactor0 : 0 ≤ (6 * Real.pi / τ) * min 1 (τ * |x - ξ|) :=
          mul_nonneg (by positivity) (le_min (by norm_num) (by positivity))
        have h := mul_le_mul hfactor (ih hΓ') (norm_nonneg _) hfactor0
        convert h using 1; ring
  have h := hlocal (spectralCluster τ center Λ) fun ξ hξ =>
    ((Multiset.mem_filter.mp hξ).2).le
  rwa [spectralWeight_cluster_eq hτ hx Λ] at h

/-- Differentiation after removing a real frequency. -/
def frequencyDerivative (ξ : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv f x - frequencyMultiplier ξ * f x

/-- Successive constant-coefficient first-order differential operators. -/
def spectralDerivative (Λ : List ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  Λ.foldr frequencyDerivative f

/-- The derivative of the real lift of a Fourier polynomial multiplies its
    coefficient of order `k` by `2π i k`. -/
theorem hasDerivAt_fourierPolynomial_real {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) (x : ℝ) :
    HasDerivAt (fun y : ℝ => fourierPolynomial a ω (y : AddCircle (1 : ℝ)))
      (fourierPolynomial (fun k => a k * frequencyMultiplier (k.val : ℝ))
        ω (x : AddCircle (1 : ℝ))) x := by
  simp only [fourierPolynomial_eq_sum]
  convert HasDerivAt.fun_sum (u := Finset.univ)
    (fun k _ => (hasDerivAt_fourier (1 : ℝ) (k.val : ℤ) x).const_mul (sign (ω k) * a k))
    using 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [frequencyMultiplier, Complex.ofReal_natCast, Int.cast_natCast,
    Complex.ofReal_one, div_one]
  ring

/-- A first-order frequency derivative has the exact coefficient multiplier
    `2π i (k − ξ)`. -/
theorem frequencyDerivative_fourierPolynomial {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) (ξ x : ℝ) :
    frequencyDerivative ξ (fun y : ℝ => fourierPolynomial a ω (y : AddCircle (1 : ℝ))) x =
      fourierPolynomial (fun k => a k * frequencyMultiplier ((k.val : ℝ) - ξ))
        ω (x : AddCircle (1 : ℝ)) := by
  rw [frequencyDerivative, (hasDerivAt_fourierPolynomial_real a ω x).deriv]
  simp only [fourierPolynomial_eq_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [frequencyMultiplier, Complex.ofReal_sub]
  ring

/-- Iterating the first-order operators gives the product of their Fourier
    multipliers, with every repeated spectral frequency retained. -/
theorem spectralDerivative_fourierPolynomial {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) (Λ : List ℝ) :
    spectralDerivative Λ (fun y : ℝ => fourierPolynomial a ω (y : AddCircle (1 : ℝ))) =
      fun x : ℝ => fourierPolynomial
        (fun k => a k * spectralDerivativeMultiplier (Λ : Multiset ℝ) (k.val : ℝ))
        ω (x : AddCircle (1 : ℝ)) := by
  induction Λ with
  | nil => simp [spectralDerivative]
  | cons ξ Λ ih =>
      change frequencyDerivative ξ (spectralDerivative Λ _) = _
      rw [ih]
      funext x
      rw [frequencyDerivative_fourierPolynomial]
      congr 1
      funext k
      change a k * spectralDerivativeMultiplier (Λ : Multiset ℝ) (k.val : ℝ) *
        frequencyMultiplier ((k.val : ℝ) - ξ) =
        a k * spectralDerivativeMultiplier (ξ ::ₘ (Λ : Multiset ℝ)) (k.val : ℝ)
      rw [spectralDerivativeMultiplier_cons]
      ring

/-- Parseval's exact energy identity for a differential multiplier. -/
theorem integral_spectralDerivativeMultiplier_energy {N : ℕ}
    (a : Fin (N + 1) → ℂ) (Λ : Multiset ℝ) :
    (∫ q, ‖randomFourier
      (fun k => a k * spectralDerivativeMultiplier Λ (k.val : ℝ)) q‖ ^ 2
      ∂fourierMeasure N) =
      ∑ k, ‖a k‖ ^ 2 * ‖spectralDerivativeMultiplier Λ (k.val : ℝ)‖ ^ 2 := by
  rw [integral_norm_sq_randomFourier]
  simp only [norm_mul, mul_pow]

/-- The energy of a local differential operator is bounded by the weighted
    spectral energy, uniformly in the number and values of the coefficients. -/
theorem integral_cluster_derivative_energy_le {N : ℕ}
    (a : Fin (N + 1) → ℂ) {τ center : ℝ} (hτ : 0 < τ) (Λ : Multiset ℝ)
    (hsupport : ∀ k, a k ≠ 0 → |(k.val : ℝ) - center| ≤ 1 / τ) :
    (∫ q, ‖randomFourier (fun k =>
      a k * spectralDerivativeMultiplier (spectralCluster τ center Λ) (k.val : ℝ)) q‖ ^ 2
      ∂fourierMeasure N) ≤
      (6 * Real.pi / τ) ^ (2 * (spectralCluster τ center Λ).card) *
        ∑ k, ‖a k‖ ^ 2 * (spectralWeight τ Λ (k.val : ℝ)) ^ 2 := by
  rw [integral_spectralDerivativeMultiplier_energy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : a k = 0
  · simp [hk]
  · have h := norm_cluster_derivativeMultiplier_le hτ (hsupport k hk) Λ
    have hright : 0 ≤ (6 * Real.pi / τ) ^ (spectralCluster τ center Λ).card *
        spectralWeight τ Λ (k.val : ℝ) :=
      mul_nonneg (by positivity) (spectralWeight_nonneg hτ.le _ _)
    have hsq := (sq_le_sq₀ (norm_nonneg _) hright).mpr h
    have hterm := mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖a k‖)
    convert hterm using 1
    rw [mul_pow, ← pow_mul, Nat.mul_comm (spectralCluster τ center Λ).card 2]
    ring

end Erdos522.LogMoments

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.Covariance.NormalizedValues
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Algebra.Field.GeomSum

/-!
# The Kac variance profile

The finite geometric series gives the limiting variance on the scale `1/N`.
Its logarithm supplies the deterministic profile in the radial Jensen bounds.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Erdos522

/-- The limiting normalized Kac variance, with its continuous value at zero. -/
def kacVarianceProfile (x : ℝ) : ℝ :=
  if x = 0 then 1 else (Real.exp (2 * x) - 1) / (2 * x)

/-- The limiting centered logarithmic standard deviation. -/
def kacLogVarianceProfile (x : ℝ) : ℝ := (1 / 2 : ℝ) * Real.log (kacVarianceProfile x)

theorem kacVarianceProfile_pos (x : ℝ) : 0 < kacVarianceProfile x := by
  by_cases hx : x = 0
  · simp [kacVarianceProfile, hx]
  · rw [kacVarianceProfile, ite_eq_right_iff.mpr (fun h => (hx h).elim)]
    rcases lt_or_gt_of_ne hx with hx | hx
    · apply div_pos_of_neg_of_neg
      · have := Real.exp_lt_one_iff.mpr (show 2 * x < 0 by linarith)
        linarith
      · linarith
    · apply div_pos
      · have := Real.one_lt_exp_iff.mpr (show 0 < 2 * x by linarith)
        linarith
      · linarith

/-- The Kac geometric identity in a normalization with a nonsingular large-degree denominator. -/
theorem radialVariance_scaled_geometric_identity {N : ℕ} (hN : 0 < N) (x : ℝ) :
    (radialVariance N (1 + x / N) / N) * (2 * x + x ^ 2 / N) =
      (1 + x / N) ^ (2 * (N + 1)) - 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  have hgeom := geom_sum_mul ((1 + x / (N : ℝ)) ^ 2) (N + 1)
  have hsum : (∑ k ∈ Finset.range (N + 1), ((1 + x / (N : ℝ)) ^ 2) ^ k) =
      radialVariance N (1 + x / N) := by
    simp only [radialVariance, ← pow_mul]
  rw [hsum, ← pow_mul] at hgeom
  calc
    _ = radialVariance N (1 + x / N) * ((1 + x / N) ^ 2 - 1) := by field_simp; ring
    _ = _ := hgeom

theorem tendsto_kac_radius (x : ℝ) :
    Tendsto (fun N : ℕ => 1 + x / N) atTop (𝓝 1) := by
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul x
  simpa only [mul_zero, add_zero, div_eq_mul_inv, Pi.inv_apply] using tendsto_const_nhds.add ht

/-- The exact normalized radial variance converges to its geometric-series profile. -/
theorem tendsto_radialVariance_profile (x : ℝ) :
    Tendsto (fun N : ℕ => radialVariance N (1 + x / N) / N) atTop (𝓝 (kacVarianceProfile x)) := by
  by_cases hx : x = 0
  · subst x
    rw [show kacVarianceProfile 0 = 1 by simp [kacVarianceProfile]]
    have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
    have ht' : Tendsto (fun N : ℕ => 1 + (N : ℝ)⁻¹) atTop (𝓝 1) := by
      simpa only [add_zero, Pi.inv_apply] using tendsto_const_nhds.add ht
    apply ht'.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    simp only [radialVariance, zero_div, add_zero, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    field_simp
  · have hnum : Tendsto (fun N : ℕ => (1 + x / N) ^ (2 * (N + 1)) - 1)
        atTop (𝓝 (Real.exp (2 * x) - 1)) := by
      have ht := ((Real.tendsto_one_add_div_pow_exp x).pow 2).mul ((tendsto_kac_radius x).pow 2)
      have he : Real.exp x ^ 2 = Real.exp (2 * x) := by rw [sq, ← Real.exp_add]; congr 1; ring
      simp only [one_pow, mul_one, he] at ht
      convert ht.sub_const 1 using 1
      funext N
      rw [Nat.mul_add, Nat.mul_one, pow_add, mul_comm 2 N, pow_mul]
    have hden : Tendsto (fun N : ℕ => 2 * x + x ^ 2 / N) atTop (𝓝 (2 * x)) := by
      have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul (x ^ 2)
      simpa only [mul_zero, add_zero, div_eq_mul_inv, Pi.inv_apply] using tendsto_const_nhds.add ht
    have hx2 : 2 * x ≠ 0 := mul_ne_zero (by norm_num) hx
    have hne : ∀ᶠ N : ℕ in atTop, 2 * x + x ^ 2 / N ≠ 0 :=
      hden.eventually (eventually_ne_nhds hx2)
    have ht := hnum.div hden hx2
    rw [kacVarianceProfile, ite_eq_right_iff.mpr (fun h => (hx h).elim)]
    apply ht.congr'
    filter_upwards [hne, eventually_ge_atTop 1] with N hd hN
    exact (eq_div_iff hd).mpr (radialVariance_scaled_geometric_identity (by omega) x) |>.symm

/-- The logarithmic normalization converges to half the logarithm of the variance profile. -/
theorem tendsto_log_radialSigma_profile (x : ℝ) :
    Tendsto (fun N : ℕ => Real.log (radialSigma N (1 + x / N)) - (1 / 2 : ℝ) * Real.log N)
      atTop (𝓝 (kacLogVarianceProfile x)) := by
  have ht := ((tendsto_radialVariance_profile x).log (kacVarianceProfile_pos x).ne').const_mul (1 / 2 : ℝ)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [Real.log_div (radialVariance_pos N _).ne' hn, radialSigma,
    Real.log_sqrt (radialVariance_pos N _).le]
  ring

/-- The denominator of a radial logarithmic secant has its first-order scale. -/
theorem tendsto_degree_mul_log_kac_radius (x : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.log (1 + x / N)) atTop (𝓝 x) := by
  simpa only [Real.log_pow, Real.log_exp] using
    (Real.tendsto_one_add_div_pow_exp x).log (Real.exp_pos x).ne'

/-- Logarithmic radial secants converge to ordinary secants in the scaled coordinate. -/
theorem tendsto_degree_mul_log_radius_ratio (x y : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.log ((1 + y / N) / (1 + x / N)))
      atTop (𝓝 (y - x)) := by
  have ht := (tendsto_degree_mul_log_kac_radius y).sub (tendsto_degree_mul_log_kac_radius x)
  apply ht.congr'
  filter_upwards [(tendsto_kac_radius x).eventually (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)),
    (tendsto_kac_radius y).eventually (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))] with N hx hy
  rw [Real.log_div hy hx]
  ring

/-- The logarithmic standard-deviation differences have the limiting profile differences. -/
theorem tendsto_log_radialSigma_sub (x y : ℝ) :
    Tendsto (fun N : ℕ => Real.log (radialSigma N (1 + y / N)) -
      Real.log (radialSigma N (1 + x / N))) atTop (𝓝 (kacLogVarianceProfile y - kacLogVarianceProfile x)) := by
  convert (tendsto_log_radialSigma_profile y).sub (tendsto_log_radialSigma_profile x) using 1
  funext N
  ring

/-- Reflection of the deterministic variance profile. -/
theorem kacVarianceProfile_reflection (x : ℝ) :
    kacVarianceProfile x = Real.exp (2 * x) * kacVarianceProfile (-x) := by
  by_cases hx : x = 0
  · simp [hx, kacVarianceProfile]
  · simp only [kacVarianceProfile, hx, neg_eq_zero, ↓reduceIte]
    rw [show 2 * -x = -(2 * x) by ring, Real.exp_neg]
    have he := (Real.exp_pos (2 * x)).ne'
    field_simp
    ring

/-- The reflected logarithmic profile differs by the radial coordinate. -/
theorem kacLogVarianceProfile_reflection (x : ℝ) :
    kacLogVarianceProfile x = x + kacLogVarianceProfile (-x) := by
  unfold kacLogVarianceProfile
  rw [kacVarianceProfile_reflection x,
    Real.log_mul (Real.exp_pos _).ne' (kacVarianceProfile_pos _).ne', Real.log_exp]
  ring

/-- Halving a negative radial coordinate gives an exact two-scale geometric identity. -/
theorem kacVarianceProfile_negative_half_identity {K : ℝ} (hK : 0 < K) :
    kacVarianceProfile (-K / 2) * (1 + Real.exp (-K)) = 2 * kacVarianceProfile (-K) := by
  have h₁ : -K / 2 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hK.ne') (by norm_num)
  have h₂ : -K ≠ 0 := neg_ne_zero.mpr hK.ne'
  simp only [kacVarianceProfile, h₁, h₂, ↓reduceIte]
  have he : Real.exp (2 * -K) = Real.exp (-K) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [show 2 * (-K / 2) = -K by ring, he]
  field_simp
  ring

/-- The negative-coordinate logarithmic profile increment is at most half `log 2`. -/
theorem kacLogVarianceProfile_negative_half_bound {K : ℝ} (hK : 0 < K) :
    kacLogVarianceProfile (-K / 2) - kacLogVarianceProfile (-K) ≤ (1 / 2 : ℝ) * Real.log 2 := by
  have hmul : kacVarianceProfile (-K / 2) ≤ 2 * kacVarianceProfile (-K) := by
    rw [← kacVarianceProfile_negative_half_identity hK]
    have hp := mul_nonneg (kacVarianceProfile_pos (-K / 2)).le (Real.exp_nonneg (-K))
    nlinarith
  have hl := Real.log_le_log (kacVarianceProfile_pos (-K / 2)) hmul
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (kacVarianceProfile_pos (-K)).ne'] at hl
  unfold kacLogVarianceProfile
  linarith

/-- The limiting four-secant bound on the fraction outside a fixed scaled annulus. -/
def kacAnnularTailCoefficient (K : ℝ) : ℝ :=
  1 + (kacLogVarianceProfile (-K / 2) - kacLogVarianceProfile (-K)) / (K / 2) -
    (kacLogVarianceProfile K - kacLogVarianceProfile (K / 2)) / (K / 2)

/-- The explicit annular tail coefficient is bounded by `2 log 2 / K`. -/
theorem kacAnnularTailCoefficient_le {K : ℝ} (hK : 0 < K) :
    kacAnnularTailCoefficient K ≤ 2 * Real.log 2 / K := by
  have h₁ := kacLogVarianceProfile_reflection K
  have h₂ := kacLogVarianceProfile_reflection (K / 2)
  rw [← neg_div] at h₂
  have heq : kacAnnularTailCoefficient K =
      4 * (kacLogVarianceProfile (-K / 2) - kacLogVarianceProfile (-K)) / K := by
    unfold kacAnnularTailCoefficient
    rw [h₁, h₂]
    field_simp
    ring
  rw [heq]
  exact div_le_div_of_nonneg_right
    (by linarith [kacLogVarianceProfile_negative_half_bound hK]) hK.le

end Erdos522

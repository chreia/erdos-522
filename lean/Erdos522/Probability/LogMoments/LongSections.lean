/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.RestrictedBilinear

/-!
# Energy on sets with long angular sections

Parseval fixes the angular energy at every sign vector. Khintchine and Hölder
control the energy lost when a small part of a sign cylinder is removed.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos522.LogMoments

/-- A pointwise bound used only for integrability, with no probabilistic constants. -/
theorem norm_randomFourier_le_sum_norm {N : ℕ} (a : Fin (N + 1) → ℂ)
    (q : SignVector N × AddCircle (1 : ℝ)) :
    ‖randomFourier a q‖ ≤ ∑ k, ‖a k‖ := by
  simp only [randomFourier, fourierPolynomial_eq_sum]
  calc
    _ ≤ ∑ k, ‖sign (q.1 k) * a k * fourier k.val q.2‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_sign, one_mul, fourier_apply,
      Circle.norm_coe, mul_one]

/-- The squared norm belongs to every finite `Lᵖ` space. -/
theorem memLp_complex_energy_randomFourier {N : ℕ} (a : Fin (N + 1) → ℂ)
    (p : ENNReal) :
    MemLp (fun q => ((‖randomFourier a q‖ ^ 2 : ℝ) : ℂ)) p (fourierMeasure N) := by
  apply MemLp.of_bound (C := (∑ k, ‖a k‖) ^ 2)
    (Complex.continuous_ofReal.measurable.comp
      ((measurable_randomFourier a).norm.pow_const 2)).aestronglyMeasurable
  filter_upwards with q
  simp only [Function.comp_apply]
  rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_randomFourier_le_sum_norm a q)

/-- Restricted squared energy from an even Khintchine moment. -/
theorem integral_sq_norm_randomFourier_restrict_le {N : ℕ} (a : Fin (N + 1) → ℂ)
    {V : ℝ} (hV : 0 < V) (ha : ∑ k, ‖a k‖ ^ 2 ≤ V)
    (m : ℕ) (hm : 2 ≤ m) (E : Set (SignVector N × AddCircle (1 : ℝ))) :
    (∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N) ≤
      (2 * Real.exp 2 * (m : ℝ) * V) *
        (fourierMeasure N).real E ^ (1 - 1 / (m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hp : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have h := integral_norm_restrict_le_moment hp
    (memLp_complex_energy_randomFourier a (ENNReal.ofReal (m : ℝ))) E
  simp only [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _),
    Real.rpow_natCast, ← pow_mul] at h
  have hmoment := integral_even_norm_randomFourier_le a hV ha m (by omega)
  have hroot : ((2 * Real.exp 2 * (m : ℝ) * V) ^ m) ^ (1 / (m : ℝ)) =
      2 * Real.exp 2 * (m : ℝ) * V := by
    rw [← Real.rpow_natCast, one_div, Real.rpow_rpow_inv (by positivity) (ne_of_gt hm0)]
  calc
    _ ≤ (∫ q, ‖randomFourier a q‖ ^ (2 * m) ∂fourierMeasure N) ^ (1 / (m : ℝ)) *
        (fourierMeasure N).real E ^ (1 - 1 / (m : ℝ)) := h
    _ ≤ ((2 * Real.exp 2 * (m : ℝ) * V) ^ m) ^ (1 / (m : ℝ)) *
        (fourierMeasure N).real E ^ (1 - 1 / (m : ℝ)) := by gcongr
    _ = _ := by rw [hroot]

/-- Parseval on each sign fiber gives exact energy on a sign cylinder. -/
theorem integral_sq_norm_randomFourier_sign_cylinder {N : ℕ}
    (a : Fin (N + 1) → ℂ) (A : Set (SignVector N)) :
    (∫ q in A ×ˢ Set.univ, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N) =
      (signMeasure N).real A * ∑ k, ‖a k‖ ^ 2 := by
  rw [fourierMeasure, ← Measure.prod_restrict, Measure.restrict_univ]
  have hi : Integrable (fun q => ‖randomFourier a q‖ ^ 2)
      (((signMeasure N).restrict A).prod AddCircle.haarAddCircle) := by
    rw [← Measure.restrict_univ (μ := AddCircle.haarAddCircle), Measure.prod_restrict]
    exact (integrable_norm_sq_randomFourier a).restrict
  rw [integral_prod _ hi]
  simp only [randomFourier, integral_norm_sq_fourierPolynomial, integral_const,
    measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul]

/-- A sufficient order for the Hölder error in the long-section argument.
    The finite constant is `512 exp(4)`. -/
theorem long_section_holder_error_le {δ n : ℝ} (hδ : 0 < δ) (p : ℕ) (hp : 1 ≤ p)
    (hn : 512 * Real.exp 4 * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) ≤ n) :
    (2 * Real.exp 2 * ((p : ℝ) + 1)) *
      (2 * δ / n) ^ (1 - 1 / ((p : ℝ) + 1)) ≤ δ / 4 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  let B : ℝ := 16 * Real.exp 2 * (p : ℝ)
  let r : ℝ := 1 + 1 / (p : ℝ)
  let q : ℝ := (p : ℝ) / ((p : ℝ) + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := by
    have he := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)
    dsimp [B]
    nlinarith
  have hr : r ≤ 2 := by
    have hi : 1 / (p : ℝ) ≤ 1 := (div_le_one hp0).mpr hp1
    dsimp [r]
    linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hrq : r * q = 1 := by dsimp [r, q]; field_simp
  have hqeq : 1 - 1 / ((p : ℝ) + 1) = q := by dsimp [q]; field_simp; ring
  have hBr : B ^ r ≤ B ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hB1 hr
  have hconstant : 2 * B ^ 2 = 512 * Real.exp 4 * (p : ℝ) ^ 2 := by
    dsimp [B]
    rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add]
    ring
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hn' : 2 * B ^ r * δ ^ (-(1 / (p : ℝ))) ≤ n := by
    calc
      _ ≤ 2 * B ^ 2 * δ ^ (-(1 / (p : ℝ))) := by gcongr
      _ = 512 * Real.exp 4 * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) := by rw [hconstant]
      _ ≤ n := hn
  have hδpow : δ ^ (-(1 / (p : ℝ))) * δ ^ r = δ := by
    rw [← Real.rpow_add hδ]
    have hexp : -(1 / (p : ℝ)) + r = 1 := by dsimp [r]; ring
    rw [hexp, Real.rpow_one]
  have hcancel : (2 * B ^ r * δ ^ (-(1 / (p : ℝ)))) * (δ / B) ^ r = 2 * δ := by
    rw [Real.div_rpow hδ.le hB.le]
    have hBr0 : B ^ r ≠ 0 := (Real.rpow_pos_of_pos hB r).ne'
    calc
      _ = 2 * (δ ^ (-(1 / (p : ℝ))) * δ ^ r) := by field_simp
      _ = _ := by rw [hδpow]
  have hsmall : 2 * δ / n ≤ (δ / B) ^ r := by
    apply (div_le_iff₀ hn0).mpr
    have h := mul_le_mul_of_nonneg_right hn' (Real.rpow_nonneg (div_nonneg hδ.le hB.le) r)
    rw [hcancel] at h
    nlinarith
  have hroot : (2 * δ / n) ^ q ≤ δ / B := by
    have h := Real.rpow_le_rpow (by positivity) hsmall hq.le
    rw [← Real.rpow_mul (by positivity), hrq, Real.rpow_one] at h
    exact h
  rw [hqeq]
  calc
    _ ≤ (4 * Real.exp 2 * (p : ℝ)) * (δ / B) := by
      apply mul_le_mul _ hroot (Real.rpow_nonneg (by positivity) q) (by positivity)
      nlinarith [Real.exp_pos 2]
    _ = δ / 4 := by dsimp [B]; field_simp; ring

/-- If a sign cylinder has probability at least `δ/2` and only `2δ/n` of it
    is removed, a normalized Fourier sum retains at least `δ/4` of its energy.
    The order condition is uniform in the degree and all coefficients. -/
theorem restricted_energy_ge_of_long_sections {N : ℕ}
    (a : Fin (N + 1) → ℂ) (ha : ∑ k, ‖a k‖ ^ 2 = 1)
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (A : Set (SignVector N)) {δ n : ℝ} (hδ : 0 < δ)
    (hA : δ / 2 ≤ (signMeasure N).real A)
    (hhole : (fourierMeasure N).real ((A ×ˢ Set.univ) \ E) ≤ 2 * δ / n)
    (p : ℕ) (hp : 1 ≤ p)
    (hn : 512 * Real.exp 4 * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) ≤ n) :
    δ / 4 ≤ ∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : 0 ≤ 1 - 1 / ((p : ℝ) + 1) := by
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity : 0 < (p : ℝ) + 1)).mpr
    linarith
  have hmoment := integral_sq_norm_randomFourier_restrict_le a
    (by norm_num : (0 : ℝ) < 1) ha.le (p + 1) (by omega)
    ((A ×ˢ Set.univ) \ E)
  simp only [Nat.cast_add, Nat.cast_one, mul_one] at hmoment
  have hlost : (∫ q in (A ×ˢ Set.univ) \ E,
      ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N) ≤ δ / 4 := by
    apply hmoment.trans
    apply le_trans _ (long_section_holder_error_le hδ p hp hn)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow measureReal_nonneg hhole hq) (by positivity)
  have hAm : MeasurableSet A := (Set.toFinite A).measurableSet
  have hCm : MeasurableSet (A ×ˢ (Set.univ : Set (AddCircle (1 : ℝ)))) :=
    hAm.prod MeasurableSet.univ
  have hsplit := setIntegral_sdiff (hCm.inter hE)
    (integrable_norm_sq_randomFourier a).integrableOn Set.inter_subset_left
  rw [Set.sdiff_self_inter, integral_sq_norm_randomFourier_sign_cylinder, ha, mul_one] at hsplit
  have hpart : (∫ q in (A ×ˢ Set.univ) ∩ E,
      ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N) ≤
      ∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N := by
    exact setIntegral_mono_set (integrable_norm_sq_randomFourier a).integrableOn
      (ae_of_all _ (fun q => sq_nonneg _)) (ae_of_all _ (fun _ h => h.2))
  linarith

end Erdos522.LogMoments

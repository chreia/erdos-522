/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.ShiftSeparation

/-!
# Averaged energy of Fourier multipliers

Normalized relation coefficients give a uniform square bound for every
multiplier. Integrating the separated-node inequality quantifies the energy
carried by a set of shifts with separated Fourier phases.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Erdos522.LogMoments

/-- Unit coefficient energy bounds the square of every shift multiplier. -/
theorem norm_shiftMultiplier_sq_le {n : ℕ} (c : Fin (n + 1) → ℂ)
    (hc : ∑ j, ‖c j‖ ^ 2 = 1) (t : AddCircle (1 : ℝ)) (k : ℕ) :
    ‖shiftMultiplier c t k‖ ^ 2 ≤ n + 1 := by
  have hnorm : ‖shiftMultiplier c t k‖ ≤ ∑ j, ‖c j‖ := by
    apply (norm_sum_le _ _).trans
    simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
    exact le_rfl
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖c j‖)
  simp only [Finset.card_univ, Fintype.card_fin, hc, mul_one, Nat.cast_add,
    Nat.cast_one] at hcs
  exact hsq.trans hcs

/-- Measurable normalized relations have integrable multiplier energies on every finite measure. -/
theorem integrable_shiftMultiplier_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n : ℕ}
    (c : Ω → Fin (n + 1) → ℂ) (hc : Measurable c)
    (hnorm : ∀ ω, ∑ j, ‖c ω j‖ ^ 2 = 1)
    (t : Ω → AddCircle (1 : ℝ)) (ht : Measurable t) (k : ℕ) :
    Integrable (fun ω => ‖shiftMultiplier (c ω) (t ω) k‖ ^ 2) μ := by
  have hcont : Continuous (fun p : (Fin (n + 1) → ℂ) × AddCircle (1 : ℝ) =>
      ‖shiftMultiplier p.1 p.2 k‖ ^ 2) := by
    unfold shiftMultiplier
    fun_prop
  apply Integrable.of_bound (hcont.measurable.comp (hc.prodMk ht)).aestronglyMeasurable (n + 1)
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_shiftMultiplier_sq_le _ (hnorm ω) _ _

/-- Separated phases on a measurable set force a lower bound for the averaged sample energy. -/
theorem integral_multiplier_energy_ge_of_separation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n : ℕ}
    (c : Ω → Fin (n + 1) → ℂ) (hc : Measurable c)
    (hnorm : ∀ ω, ∑ j, ‖c ω j‖ ^ 2 = 1)
    (t : Ω → AddCircle (1 : ℝ)) (ht : Measurable t)
    (m : Fin (n + 1) → ℕ) {δ : ℝ} (hδ : 0 < δ)
    (S : Set Ω) (hS : MeasurableSet S)
    (hsep : ∀ ω ∈ S, ∀ i j, i ≠ j → δ ≤ ‖fourier (m i) (t ω) - fourier (m j) (t ω)‖) :
    μ.real S * ((δ / 2) ^ (2 * n) / (n + 1 : ℝ)) ≤
      ∑ i, ∫ ω, ‖shiftMultiplier (c ω) (t ω) (m i)‖ ^ 2 ∂μ := by
  have hint (i : Fin (n + 1)) := integrable_shiftMultiplier_sq μ c hc hnorm t ht (m i)
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hint i)
  calc
    _ = ∫ _ in S, ((δ / 2) ^ (2 * n) / (n + 1 : ℝ)) ∂μ := by
      rw [integral_const]
      simp only [Measure.restrict_apply_univ, smul_eq_mul, Measure.real]
    _ ≤ ∫ ω in S, ∑ i, ‖shiftMultiplier (c ω) (t ω) (m i)‖ ^ 2 ∂μ := by
      apply setIntegral_mono_on (integrable_const _) hsum.integrableOn hS
      intro ω hω
      exact shift_multiplier_energy_ge_of_separation _ (hnorm ω) m _ hδ (hsep ω hω)
    _ ≤ ∫ ω, ∑ i, ‖shiftMultiplier (c ω) (t ω) (m i)‖ ^ 2 ∂μ :=
      setIntegral_le_integral hsum (ae_of_all _ fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := integral_finsetSum _ (fun i _ => hint i)

end Erdos522.LogMoments

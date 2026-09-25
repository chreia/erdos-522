/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.AveragedSpectrum
import Erdos522.Probability.LogMoments.SmallShiftSelection

/-!
# Coefficient energy outside short spectral intervals

Small shift energy forces all but a quantitative fraction of the Fourier
coefficient energy into finitely many short intervals. The number of
intervals is bounded by the order of the normalized shift relation.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Erdos522.LogMoments

/-- Averaged multiplier energies are nonnegative. -/
theorem averagedMultiplierEnergy_nonneg {n : ℕ}
    (c : ℝ → Fin (n + 1) → ℂ) {τ : ℝ} (hτ : 0 ≤ τ) (k : ℕ) :
    0 ≤ averagedMultiplierEnergy c τ k :=
  div_nonneg (integral_nonneg fun _ => sq_nonneg _) hτ

/-- A pointwise small-shift energy bound also bounds its weighted average. -/
theorem sum_weighted_averagedMultiplierEnergy_le {N n : ℕ}
    (a : Fin (N + 1) → ℂ) (c : ℝ → Fin (n + 1) → ℂ) (hc : Measurable c)
    (hnorm : ∀ t, ∑ j, ‖c t j‖ ^ 2 = 1) {τ B : ℝ} (hτ : 0 < τ)
    (henergy : ∀ᵐ t ∂volume.restrict (Set.Icc 0 τ),
      (∑ k, ‖a k‖ ^ 2 * ‖shiftMultiplier (c t) (t : AddCircle (1 : ℝ)) k.val‖ ^ 2) ≤ B) :
    (∑ k, ‖a k‖ ^ 2 * averagedMultiplierEnergy c τ k.val) ≤ B := by
  have hint (k : Fin (N + 1)) :=
    integrable_shiftMultiplier_sq (volume.restrict (Set.Icc 0 τ)) c hc hnorm
      (fun t : ℝ => (t : AddCircle (1 : ℝ))) (by fun_prop) k.val
  have hsum := integrable_finsetSum Finset.univ (fun k _ => (hint k).const_mul (‖a k‖ ^ 2))
  have hb := integral_mono_ae hsum (integrable_const B) henergy
  have heq : (∑ k, ‖a k‖ ^ 2 * averagedMultiplierEnergy c τ k.val) =
      (∫ t in Set.Icc 0 τ, ∑ k,
        ‖a k‖ ^ 2 * ‖shiftMultiplier (c t) (t : AddCircle (1 : ℝ)) k.val‖ ^ 2) / τ := by
    rw [integral_finsetSum _ (fun k _ => (hint k).const_mul (‖a k‖ ^ 2)), Finset.sum_div]
    simp only [averagedMultiplierEnergy, integral_const_mul, mul_div_assoc]
  rw [heq]
  apply (div_le_iff₀ hτ).mpr
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul,
    Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hτ.le, mul_comm] using hb

/-- The coefficient energy outside at most `n` short intervals is controlled by
small shift energy, uniformly in the number and values of the coefficients. -/
theorem exists_spectral_intervals_of_small_shifts {N n : ℕ}
    (a : Fin (N + 1) → ℂ) (c : ℝ → Fin (n + 1) → ℂ) (hc : Measurable c)
    (hnorm : ∀ t, ∑ j, ‖c t j‖ ^ 2 = 1) {τ B : ℝ} (hτ : 0 < τ)
    (henergy : ∀ᵐ t ∂volume.restrict (Set.Icc 0 τ),
      (∑ k, ‖a k‖ ^ 2 * ‖shiftMultiplier (c t) (t : AddCircle (1 : ℝ)) k.val‖ ^ 2) ≤ B) :
    ∃ T : Finset ℕ, T ⊆ Finset.range (N + 1) ∧ T.card ≤ n ∧
      (∑ k : Fin (N + 1) with
        ∀ m ∈ T, 1 / (8 * ((n : ℝ) + 1) ^ 2 * τ) < |(k.val : ℝ) - m|,
          ‖a k‖ ^ 2) ≤ B / spectralEnergyCutoff n := by
  classical
  let S := (Finset.range (N + 1)).filter fun k =>
    averagedMultiplierEnergy c τ k < spectralEnergyCutoff n
  obtain ⟨T, hT, hcard, hcover⟩ := exists_cover_of_small_averaged_multipliers c hc hnorm hτ S
    (fun k hk => (Finset.mem_filter.mp hk).2)
  refine ⟨T, fun k hk => (Finset.mem_filter.mp (hT hk)).1, hcard, ?_⟩
  let outside : Finset (Fin (N + 1)) := Finset.univ.filter fun k =>
    ∀ m ∈ T, 1 / (8 * ((n : ℝ) + 1) ^ 2 * τ) < |(k.val : ℝ) - m|
  have hlarge (k : Fin (N + 1)) (hk : k ∈ outside) :
      spectralEnergyCutoff n ≤ averagedMultiplierEnergy c τ k.val := by
    by_contra h
    have hkS : k.val ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr k.isLt, lt_of_not_ge h⟩
    obtain ⟨m, hm, hnear⟩ := hcover k.val hkS
    exact (not_le_of_gt ((Finset.mem_filter.mp hk).2 m hm)) hnear
  apply (le_div_iff₀ (spectralEnergyCutoff_pos n)).mpr
  change (∑ k ∈ outside, ‖a k‖ ^ 2) * spectralEnergyCutoff n ≤ B
  calc
    _ = ∑ k ∈ outside, ‖a k‖ ^ 2 * spectralEnergyCutoff n := Finset.sum_mul ..
    _ ≤ ∑ k ∈ outside, ‖a k‖ ^ 2 * averagedMultiplierEnergy c τ k.val :=
      Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hlarge k hk) (sq_nonneg _)
    _ ≤ ∑ k, ‖a k‖ ^ 2 * averagedMultiplierEnergy c τ k.val :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ => mul_nonneg (sq_nonneg _) (averagedMultiplierEnergy_nonneg c hτ.le k.val))
    _ ≤ B := sum_weighted_averagedMultiplierEnergy_le a c hc hnorm hτ henergy

/-- Pointwise small-shift relations concentrate coefficient energy in at most
`n` short intervals. Measurable selection and a finite minimum remove the selection margin. -/
theorem exists_spectral_intervals_of_shift_relations {N n : ℕ}
    (a : Fin (N + 1) → ℂ) {τ B : ℝ} (hτ : 0 < τ)
    (hsmall : ∀ t : Set.Ioo (0 : ℝ) τ, ∃ c : Fin (n + 1) → ℂ,
      (∑ j, ‖c j‖ ^ 2) = 1 ∧
      (∫ q, ‖∑ j, c j * randomFourier a
        (angularTranslation N (j.val • (t.val : AddCircle (1 : ℝ))) q)‖ ^ 2
          ∂fourierMeasure N) ≤ B) :
    ∃ T : Finset ℕ, T ⊆ Finset.range (N + 1) ∧ T.card ≤ n ∧
      (∑ k : Fin (N + 1) with ∀ j ∈ T,
        1 / (8 * ((n : ℝ) + 1) ^ 2 * τ) < |(k.val : ℝ) - j|, ‖a k‖ ^ 2) ≤
          B / spectralEnergyCutoff n := by
  classical
  let candidates := (Finset.range (N + 1)).powerset.filter fun T => T.card ≤ n
  let energy (T : Finset ℕ) : ℝ := ∑ k : Fin (N + 1) with ∀ j ∈ T,
    1 / (8 * ((n : ℝ) + 1) ^ 2 * τ) < |(k.val : ℝ) - j|, ‖a k‖ ^ 2
  have hne : candidates.Nonempty := ⟨∅, by simp [candidates]⟩
  obtain ⟨T, hT, hmin⟩ := candidates.exists_min_image energy hne
  refine ⟨T, Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1, (Finset.mem_filter.mp hT).2, ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨c, hc, hb⟩ := exists_measurable_small_shift_coefficients a (Set.Ioo (0 : ℝ) τ)
    (mul_pos hε (spectralEnergyCutoff_pos n)) hsmall
  obtain ⟨d, hd, hnorm, hext⟩ := exists_measurable_unit_extension (Set.Ioo (0 : ℝ) τ)
    measurableSet_Ioo c hc (fun t => (hb t).1)
  have henergy : ∀ᵐ t ∂volume.restrict (Set.Icc 0 τ),
      (∑ k, ‖a k‖ ^ 2 * ‖shiftMultiplier (d t) (t : AddCircle (1 : ℝ)) k.val‖ ^ 2) ≤
        B + ε * spectralEnergyCutoff n := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)))]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [hext ⟨t, ht⟩]
    exact (hb ⟨t, ht⟩).2.le
  obtain ⟨U, hU, hcard, hbound⟩ := exists_spectral_intervals_of_small_shifts a d hd hnorm hτ henergy
  have hmem : U ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hU, hcard⟩
  have h := (hmin U hmem).trans hbound
  simpa only [add_div, mul_div_cancel_right₀ ε (spectralEnergyCutoff_pos n).ne'] using h

/-- Restricted Fourier energy supplies a short-interval spectral cover. The shift
scale is uniform in the coefficient vector and in the arbitrarily small energy margin. -/
theorem exists_spectral_intervals_of_restricted_energy_with_margin {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (m : ℕ) (hm : 1 ≤ m) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ a : Fin (N + 1) → ℂ, ∀ η : ℝ, 0 < η →
      ∃ T : Finset ℕ, T ⊆ Finset.range (N + 1) ∧
        T.card ≤ shiftOrder ((fourierMeasure N).real E) m ∧
        (∑ k : Fin (N + 1) with ∀ j ∈ T,
          1 / (8 * ((shiftOrder ((fourierMeasure N).real E) m : ℝ) + 1) ^ 2 * τ) <
            |(k.val : ℝ) - j|, ‖a k‖ ^ 2) ≤
          ((4 * ((shiftOrder ((fourierMeasure N).real E) m : ℝ) + 1) /
            (fourierMeasure N).real E) *
              (∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N) + η) /
            spectralEnergyCutoff (shiftOrder ((fourierMeasure N).real E) m) := by
  obtain ⟨τ, hτ, hsmall⟩ := exists_quantitative_small_shifts E hE hpos m hm
  refine ⟨τ, hτ, fun a η hη => ?_⟩
  obtain ⟨c, hc, hb⟩ := exists_measurable_small_shift_coefficients a (Set.Ioo (0 : ℝ) τ) hη
    (fun t => hsmall t.val t.property.1 t.property.2 a)
  obtain ⟨d, hd, hnorm, hext⟩ := exists_measurable_unit_extension (Set.Ioo (0 : ℝ) τ)
    measurableSet_Ioo c hc (fun t => (hb t).1)
  apply exists_spectral_intervals_of_small_shifts a d hd hnorm hτ
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)))]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [hext ⟨t, ht⟩]
  exact (hb ⟨t, ht⟩).2.le

/-- Restricted energy controls the coefficient mass outside finitely many short
intervals with no auxiliary error term. One shift scale works for every coefficient vector. -/
theorem exists_spectral_intervals_of_restricted_energy {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (m : ℕ) (hm : 1 ≤ m) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ a : Fin (N + 1) → ℂ,
      ∃ T : Finset ℕ, T ⊆ Finset.range (N + 1) ∧
        T.card ≤ shiftOrder ((fourierMeasure N).real E) m ∧
        (∑ k : Fin (N + 1) with ∀ j ∈ T,
          1 / (8 * ((shiftOrder ((fourierMeasure N).real E) m : ℝ) + 1) ^ 2 * τ) <
            |(k.val : ℝ) - j|, ‖a k‖ ^ 2) ≤
          ((4 * ((shiftOrder ((fourierMeasure N).real E) m : ℝ) + 1) /
            (fourierMeasure N).real E) *
              (∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N)) /
            spectralEnergyCutoff (shiftOrder ((fourierMeasure N).real E) m) := by
  obtain ⟨τ, hτ, hsmall⟩ := exists_quantitative_small_shifts E hE hpos m hm
  refine ⟨τ, hτ, fun a => ?_⟩
  exact exists_spectral_intervals_of_shift_relations a hτ
    (fun t => hsmall t.val t.property.1 t.property.2 a)

end Erdos522.LogMoments

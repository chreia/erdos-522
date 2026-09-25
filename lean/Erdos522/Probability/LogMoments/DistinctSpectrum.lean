/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.WeightedSpectrum
import Erdos522.Probability.LogMoments.SpectralPerturbation

/-!
# Distinct approximate frequencies

Finite spectral perturbation removes repeated frequencies at a controlled
energy cost. Positivity of restricted energy for a normalized Fourier sum
allows the perturbation loss to remain proportional to that energy.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Erdos522.LogMoments

/-- A normalized finite Fourier sum has positive energy on every set of positive measure. -/
theorem restricted_fourier_energy_pos {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1)
    (E : Set (SignVector N × AddCircle (1 : ℝ)))
    (hE : 0 < (fourierMeasure N).real E) :
    0 < ∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N := by
  have : NeZero ((fourierMeasure N) E) := ⟨fun h => by simp [Measure.real, h] at hE⟩
  have hnonneg : 0 ≤ ∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N :=
    integral_nonneg fun _ => sq_nonneg _
  by_contra h
  have hz := (integral_eq_zero_iff_of_nonneg (fun q => sq_nonneg ‖randomFourier a q‖)
    (integrable_norm_sq_randomFourier a).integrableOn).mp (le_antisymm (le_of_not_gt h) hnonneg)
  have hne := ae_restrict_of_ae (s := E) (randomFourier_ae_ne_zero a ha)
  have hf : ∀ᵐ q ∂(fourierMeasure N).restrict E, False := by
    filter_upwards [hz, hne] with q hzero hnzero
    have hh : ‖randomFourier a q‖ ^ 2 = 0 := hzero
    exact hnzero (norm_eq_zero.mp (sq_eq_zero_iff.mp hh))
  exact hf.exists.elim (fun _ hfalse => hfalse)

/-- With positive error budget, distinct frequencies cost at most a factor two. -/
theorem exists_distinct_weighted_spectrum_of_shift_relations {N n : ℕ}
    (a : Fin (N + 1) → ℂ) {τ B : ℝ} (hτ : 0 < τ) (hB : 0 < B)
    (hsmall : ∀ t : Set.Ioo (0 : ℝ) τ, ∃ c : Fin (n + 1) → ℂ,
      (∑ j, ‖c j‖ ^ 2) = 1 ∧
      (∫ q, ‖∑ j, c j * randomFourier a
        (angularTranslation N (j.val • (t.val : AddCircle (1 : ℝ))) q)‖ ^ 2
          ∂fourierMeasure N) ≤ B) :
    ∃ Λ : Multiset ℝ, Λ.Nodup ∧ Λ.card ≤ n ∧
      (∑ k : Fin (N + 1), ‖a k‖ ^ 2 * (spectralWeight τ Λ k.val) ^ 2) ≤
        2 * B * (1 / spectralEnergyCutoff n +
          1 / (1 / (8 * ((n : ℝ) + 1) ^ 2)) ^ (2 * n)) := by
  obtain ⟨Λ, hcard, hb⟩ := exists_weighted_spectrum_of_shift_relations a hτ hsmall
  let C := 1 / spectralEnergyCutoff n + 1 / (1 / (8 * ((n : ℝ) + 1) ^ 2)) ^ (2 * n)
  have hC : 0 < C := by
    have hγ := spectralEnergyCutoff_pos n
    dsimp [C]
    positivity
  obtain ⟨Γ, hΓ, hΓcard, henergy⟩ := exists_distinct_spectrum_energy_le a
    (fun k => (k.val : ℝ)) τ Λ (mul_pos hB hC)
  refine ⟨Γ, hΓ, hΓcard.trans_le hcard, ?_⟩
  have hbound : (∑ k : Fin (N + 1), ‖a k‖ ^ 2 * (spectralWeight τ Λ k.val) ^ 2) ≤ B * C := by
    simpa only [C, mul_add, mul_one_div] using hb
  change _ ≤ 2 * B * C
  linarith

/-- A normalized finite Fourier sum has a distinct approximate spectrum with
coefficient-uniform scale and a bound proportional to its restricted energy. -/
theorem exists_distinct_weighted_spectrum_of_restricted_energy {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (m : ℕ) (hm : 1 ≤ m) :
    let n := shiftOrder ((fourierMeasure N).real E) m
    ∃ τ : ℝ, 0 < τ ∧ ∀ a : Fin (N + 1) → ℂ, (∑ k, ‖a k‖ ^ 2 = 1) →
      ∃ Λ : Multiset ℝ, Λ.Nodup ∧ Λ.card ≤ n ∧
        (∑ k : Fin (N + 1), ‖a k‖ ^ 2 * (spectralWeight τ Λ k.val) ^ 2) ≤
          2 * (4 * ((n : ℝ) + 1) / (fourierMeasure N).real E *
            (∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N)) *
            (1 / spectralEnergyCutoff n + 1 / (1 / (8 * ((n : ℝ) + 1) ^ 2)) ^ (2 * n)) := by
  dsimp only
  obtain ⟨τ, hτ, hsmall⟩ := exists_quantitative_small_shifts E hE hpos m hm
  refine ⟨τ, hτ, fun a ha => ?_⟩
  exact exists_distinct_weighted_spectrum_of_shift_relations a hτ
    (mul_pos (div_pos (by positivity) hpos) (restricted_fourier_energy_pos a ha E hpos))
    (fun t => hsmall t.val t.property.1 t.property.2 a)

end Erdos522.LogMoments

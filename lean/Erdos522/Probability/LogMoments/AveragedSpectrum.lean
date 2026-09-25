/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.AveragedMultipliers
import Erdos522.Analysis.SeparatedTimes
import Erdos522.Analysis.FiniteSeparatedCover
import Mathlib.Topology.Instances.Nat

/-!
# Finite spectral concentration of small-shift relations

Averaging the multiplier energy over a short interval detects any family of
separated frequencies. Consequently the frequencies of small averaged energy
can be covered by as many short intervals as the order of the shift relation.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Erdos522.LogMoments

/-- The normalized averaged energy of one Fourier multiplier. -/
def averagedMultiplierEnergy {n : ℕ} (c : ℝ → Fin (n + 1) → ℂ) (τ : ℝ) (k : ℕ) : ℝ :=
  (∫ t in Set.Icc 0 τ, ‖shiftMultiplier (c t) (t : AddCircle (1 : ℝ)) k‖ ^ 2) / τ

/-- The energy cutoff obtained by sampling a relation polynomial at separated phases. -/
def spectralEnergyCutoff (n : ℕ) : ℝ :=
  ((1 / (128 * ((n : ℝ) + 1) ^ 4)) / 2) ^ (2 * n) / (2 * ((n : ℝ) + 1) ^ 2)

theorem spectralEnergyCutoff_pos (n : ℕ) : 0 < spectralEnergyCutoff n := by
  unfold spectralEnergyCutoff
  positivity

/-- Evaluation of the `k`-th character at a real shift uses the frequency `k`. -/
theorem fourier_nat_eq_angularCharacter (k : ℕ) (t : ℝ) :
    fourier k (t : AddCircle (1 : ℝ)) = angularCharacter ((k : ℝ) * t) := by
  rw [angularCharacter, fourier_coe_apply, fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- Some frequency in any separated family of `n + 1` has definite averaged multiplier energy. -/
theorem exists_large_averaged_multiplier {n : ℕ}
    (c : ℝ → Fin (n + 1) → ℂ) (hc : Measurable c)
    (hnorm : ∀ t, ∑ j, ‖c t j‖ ^ 2 = 1) {τ : ℝ} (hτ : 0 < τ)
    (m : Fin (n + 1) → ℕ)
    (hspacing : ∀ i j, i ≠ j →
      1 / (8 * ((n : ℝ) + 1) ^ 2 * τ) ≤ |(m i : ℝ) - m j|) :
    ∃ i, spectralEnergyCutoff n ≤ averagedMultiplierEnergy c τ (m i) := by
  let δ : ℝ := 1 / (128 * ((n : ℝ) + 1) ^ 4)
  let S := separatedAngularTimes (fun i => (m i : ℝ)) τ δ
  let μ : Measure ℝ := volume.restrict (Set.Icc 0 τ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hS := measurableSet_separatedAngularTimes (fun i => (m i : ℝ)) τ δ
  have hSsub : S ⊆ Set.Icc 0 τ := fun _ ht => ⟨ht.1, ht.2.1⟩
  have hreal : μ.real S = volume.real S := by
    change ((volume.restrict (Set.Icc 0 τ)) S).toReal = (volume S).toReal
    rw [Measure.restrict_apply hS, Set.inter_eq_left.mpr hSsub]
  have hmeasure : τ / 2 ≤ μ.real S := by
    rw [hreal]
    exact volume_separatedAngularTimes_ge_half n _ hτ hspacing
  have hint := integral_multiplier_energy_ge_of_separation μ c hc hnorm
    (fun t : ℝ => (t : AddCircle (1 : ℝ))) (by fun_prop) m hδ S hS
    (fun t ht i j hij => by
      simpa only [fourier_nat_eq_angularCharacter] using ht.2.2 i j hij)
  have hlower : τ / 2 * ((δ / 2) ^ (2 * n) / ((n : ℝ) + 1)) ≤
      ∑ i, ∫ t in Set.Icc 0 τ,
        ‖shiftMultiplier (c t) (t : AddCircle (1 : ℝ)) (m i)‖ ^ 2 := by
    exact (mul_le_mul_of_nonneg_right hmeasure (by positivity)).trans hint
  by_contra h
  push Not at h
  have hsum : (∑ i, averagedMultiplierEnergy c τ (m i)) <
      ((n : ℝ) + 1) * spectralEnergyCutoff n := by
    calc
      _ < ∑ _i : Fin (n + 1), spectralEnergyCutoff n :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => h i)
      _ = _ := by simp
  simp only [averagedMultiplierEnergy, ← Finset.sum_div] at hsum
  have hupper := (div_lt_iff₀ hτ).mp hsum
  have heq : ((n : ℝ) + 1) * spectralEnergyCutoff n * τ =
      τ / 2 * ((δ / 2) ^ (2 * n) / ((n : ℝ) + 1)) := by
    dsimp [spectralEnergyCutoff, δ]
    field_simp
  rw [heq] at hupper
  exact (not_lt_of_ge hlower) hupper

/-- Frequencies of small averaged multiplier energy admit a finite short-interval cover. -/
theorem exists_cover_of_small_averaged_multipliers {n : ℕ}
    (c : ℝ → Fin (n + 1) → ℂ) (hc : Measurable c)
    (hnorm : ∀ t, ∑ j, ‖c t j‖ ^ 2 = 1) {τ : ℝ} (hτ : 0 < τ)
    (S : Finset ℕ)
    (hsmall : ∀ k ∈ S, averagedMultiplierEnergy c τ k < spectralEnergyCutoff n) :
    ∃ T : Finset ℕ, T ⊆ S ∧ T.card ≤ n ∧
      ∀ k ∈ S, ∃ m ∈ T, |(k : ℝ) - m| ≤ 1 / (8 * ((n : ℝ) + 1) ^ 2 * τ) := by
  apply exists_finite_cover_of_packing_bound S (by positivity) n
  intro T hT hsep
  by_contra hcard
  have hnT : n + 1 ≤ Fintype.card T := by simp only [Fintype.card_coe]; omega
  let e : Fin (n + 1) ↪ T := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa using hnT))
  have he (i j : Fin (n + 1)) (hij : i ≠ j) : (e i).val ≠ (e j).val := by
    intro h
    exact hij (e.injective (Subtype.ext h))
  obtain ⟨i, hi⟩ := exists_large_averaged_multiplier c hc hnorm hτ
    (fun i => (e i).val) (fun i j hij =>
      (hsep _ (e i).property _ (e j).property (he i j hij)).le)
  exact (not_le_of_gt (hsmall _ (hT (e i).property))) hi

end Erdos522.LogMoments

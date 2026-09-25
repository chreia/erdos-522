/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.SpectralDifferentiation
import Erdos522.Probability.LogMoments.SpectralPerturbation
import Erdos522.Probability.LogMoments.SmallShifts
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Disjoint spectral bands

An ordered finite family of frequency intervals partitions the coefficient
indices by their first containing interval. The remaining indices form the
residual band. This partitions both the Fourier polynomial and its exact
coefficient energy; on the residual band every clipped spectral factor is one.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Erdos522.LogMoments

/-- A local cluster has no more frequencies than its original spectrum. -/
theorem spectralCluster_card_le (τ center : ℝ) (Λ : Multiset ℝ) :
    (spectralCluster τ center Λ).card ≤ Λ.card :=
  Multiset.card_le_card (Multiset.filter_le _ _)

/-- Distinctness of a spectrum is preserved when taking a local cluster. -/
theorem spectralCluster_nodup (τ center : ℝ) {Λ : Multiset ℝ} (hΛ : Λ.Nodup) :
    (spectralCluster τ center Λ).Nodup :=
  Multiset.Nodup.filter _ hΛ

/-- Every chosen center belongs to its own positive-scale cluster. -/
theorem center_mem_spectralCluster {τ center : ℝ} (hτ : 0 < τ)
    {Λ : Multiset ℝ} (hcenter : center ∈ Λ) :
    center ∈ spectralCluster τ center Λ := by
  apply Multiset.mem_filter.mpr
  refine ⟨hcenter, ?_⟩
  simpa only [sub_self, abs_zero] using div_pos (by norm_num : (0 : ℝ) < 2) hτ

/-- A band center gives a nonempty cluster, whose order is at most the number
    of original frequencies. -/
theorem spectralCluster_ofFn_card_bounds {m : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (ξ : Fin m → ℝ) (j : Fin m) :
    0 < (spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)).card ∧
      (spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)).card ≤ m := by
  constructor
  · exact Multiset.card_pos_iff_exists_mem.mpr
      ⟨ξ j, center_mem_spectralCluster hτ (by simp)⟩
  · simpa using spectralCluster_card_le τ (ξ j) (List.ofFn ξ : Multiset ℝ)

/-- The first spectral interval containing a frequency, or `none` if no interval
    contains it. Every interval is open and has radius `1 / τ`. -/
def spectralBandIndex {m : ℕ} (τ : ℝ) (ξ : Fin m → ℝ) (x : ℝ) : Option (Fin m) :=
  if h : ∃ j, |x - ξ j| < 1 / τ then
    some (Fin.find (fun j => |x - ξ j| < 1 / τ) h)
  else none

/-- A non-residual band consists of the points in its interval that do not lie
    in any earlier interval. -/
theorem spectralBandIndex_eq_some_iff {m : ℕ} (τ : ℝ) (ξ : Fin m → ℝ)
    (x : ℝ) (j : Fin m) :
    spectralBandIndex τ ξ x = some j ↔
      |x - ξ j| < 1 / τ ∧ ∀ i < j, 1 / τ ≤ |x - ξ i| := by
  unfold spectralBandIndex
  split_ifs with h
  · simp only [Option.some.injEq, Fin.find_eq_iff, not_lt]
  · constructor
    · simp
    · intro hj
      exact False.elim (h ⟨j, hj.1⟩)

/-- A point lies in the residual band precisely when it is outside every open
    spectral interval, including its boundary points. -/
theorem spectralBandIndex_eq_none_iff {m : ℕ} (τ : ℝ) (ξ : Fin m → ℝ) (x : ℝ) :
    spectralBandIndex τ ξ x = none ↔ ∀ j, 1 / τ ≤ |x - ξ j| := by
  unfold spectralBandIndex
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    simp only [false_iff, not_forall, not_le]
    exact ⟨j, hj⟩
  · simpa only [not_exists, not_lt, true_iff] using h

/-- The coefficients assigned to one spectral band. The index `none` is the
    residual band, while `some j` refers to the interval centered at `ξ j`. -/
def spectralBandCoefficients {N m : ℕ} (a : Fin (N + 1) → ℂ)
    (τ : ℝ) (ξ : Fin m → ℝ) (j : Option (Fin m)) (k : Fin (N + 1)) : ℂ :=
  if spectralBandIndex τ ξ (k.val : ℝ) = j then a k else 0

/-- A nonzero projected coefficient retains its unique spectral-band index. -/
theorem spectralBandIndex_eq_of_coefficient_ne_zero {N m : ℕ}
    (a : Fin (N + 1) → ℂ) (τ : ℝ) (ξ : Fin m → ℝ)
    (j : Option (Fin m)) (k : Fin (N + 1))
    (hk : spectralBandCoefficients a τ ξ j k ≠ 0) :
    spectralBandIndex τ ξ (k.val : ℝ) = j := by
  by_contra h
  simp [spectralBandCoefficients, h] at hk

/-- Each non-residual projected coefficient is supported in its open spectral
    interval. -/
theorem spectralBandCoefficients_support {N m : ℕ}
    (a : Fin (N + 1) → ℂ) (τ : ℝ) (ξ : Fin m → ℝ)
    (j : Fin m) (k : Fin (N + 1))
    (hk : spectralBandCoefficients a τ ξ (some j) k ≠ 0) :
    |(k.val : ℝ) - ξ j| < 1 / τ :=
  ((spectralBandIndex_eq_some_iff τ ξ (k.val : ℝ) j).mp
    (spectralBandIndex_eq_of_coefficient_ne_zero a τ ξ (some j) k hk)).1

/-- Summing all the bands recovers each coefficient exactly. -/
theorem sum_spectralBandCoefficients {N m : ℕ} (a : Fin (N + 1) → ℂ)
    (τ : ℝ) (ξ : Fin m → ℝ) (k : Fin (N + 1)) :
    (∑ j : Option (Fin m), spectralBandCoefficients a τ ξ j k) = a k := by
  simp [spectralBandCoefficients]

/-- Distinct bands have disjoint coefficient supports. -/
theorem spectralBandCoefficients_disjoint {N m : ℕ} (a : Fin (N + 1) → ℂ)
    (τ : ℝ) (ξ : Fin m → ℝ) {i j : Option (Fin m)} (hij : i ≠ j)
    (k : Fin (N + 1)) :
    spectralBandCoefficients a τ ξ i k *
      spectralBandCoefficients a τ ξ j k = 0 := by
  by_cases hi : spectralBandIndex τ ξ (k.val : ℝ) = i
  · simp [spectralBandCoefficients, hi, hij]
  · simp [spectralBandCoefficients, hi]

/-- The actual Rademacher Fourier polynomial is the sum of its disjoint bands,
    for every sign vector and every point of the additive circle. -/
theorem sum_randomFourier_spectralBands {N m : ℕ} (a : Fin (N + 1) → ℂ)
    (τ : ℝ) (ξ : Fin m → ℝ) (q : SignVector N × AddCircle (1 : ℝ)) :
    (∑ j : Option (Fin m), randomFourier (spectralBandCoefficients a τ ξ j) q) =
      randomFourier a q := by
  have h := randomFourier_sum_mul (fun _ : Option (Fin m) => (1 : ℂ))
    (spectralBandCoefficients a τ ξ) q
  simpa only [one_mul, sum_spectralBandCoefficients] using h.symm

/-- Arbitrary weighted coefficient energies partition exactly across the bands. -/
theorem sum_spectralBand_weighted_energy {N m : ℕ} (a : Fin (N + 1) → ℂ)
    (τ : ℝ) (ξ : Fin m → ℝ) (w : Fin (N + 1) → ℝ) :
    (∑ j : Option (Fin m), ∑ k, ‖spectralBandCoefficients a τ ξ j k‖ ^ 2 * w k) =
      ∑ k, ‖a k‖ ^ 2 * w k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = ∑ j : Option (Fin m),
        if spectralBandIndex τ ξ (k.val : ℝ) = j then ‖a k‖ ^ 2 * w k else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : spectralBandIndex τ ξ (k.val : ℝ) = j <;>
        simp [spectralBandCoefficients, hj]
    _ = ‖a k‖ ^ 2 * w k := by simp

/-- Projection onto a band decreases every nonnegative weighted coefficient
    energy. -/
theorem spectralBand_weighted_energy_le {N m : ℕ} (a : Fin (N + 1) → ℂ)
    (τ : ℝ) (ξ : Fin m → ℝ) (w : Fin (N + 1) → ℝ) (hw : ∀ k, 0 ≤ w k)
    (j : Option (Fin m)) :
    (∑ k, ‖spectralBandCoefficients a τ ξ j k‖ ^ 2 * w k) ≤
      ∑ k, ‖a k‖ ^ 2 * w k := by
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : spectralBandIndex τ ξ (k.val : ℝ) = j
  · simp [spectralBandCoefficients, hk]
  · simpa [spectralBandCoefficients, hk] using mul_nonneg (sq_nonneg ‖a k‖) (hw k)

/-- Parseval turns the disjoint coefficient-energy identity into an identity
    under the actual product sign and Haar measure. -/
theorem sum_integral_spectralBands_energy {N m : ℕ} (a : Fin (N + 1) → ℂ)
    (τ : ℝ) (ξ : Fin m → ℝ) :
    (∑ j : Option (Fin m), ∫ q, ‖randomFourier (spectralBandCoefficients a τ ξ j) q‖ ^ 2
      ∂fourierMeasure N) = ∫ q, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N := by
  simp only [integral_norm_sq_randomFourier]
  simpa only [mul_one] using sum_spectralBand_weighted_energy a τ ξ (fun _ => 1)

/-- Outside all spectral intervals, the clipped product is exactly one. -/
theorem spectralWeight_eq_one_of_separated {τ x : ℝ} (hτ : 0 < τ)
    (Λ : Multiset ℝ) (hsep : ∀ ξ ∈ Λ, 1 / τ ≤ |x - ξ|) :
    spectralWeight τ Λ x = 1 := by
  induction Λ using Multiset.induction_on with
  | empty => simp
  | cons ξ Λ ih =>
      have hξ := hsep ξ (Multiset.mem_cons_self _ _)
      have hclip : 1 ≤ τ * |x - ξ| := by
        have := (div_le_iff₀ hτ).mp hξ
        nlinarith
      rw [spectralWeight_cons, min_eq_left hclip,
        ih (fun ξ hξ => hsep ξ (Multiset.mem_cons_of_mem hξ)), one_mul]

/-- The residual band's unweighted energy equals its spectral-weighted energy. -/
theorem residualBand_energy_eq_weighted {N m : ℕ} (a : Fin (N + 1) → ℂ)
    {τ : ℝ} (hτ : 0 < τ) (ξ : Fin m → ℝ) :
    (∑ k, ‖spectralBandCoefficients a τ ξ none k‖ ^ 2) =
      ∑ k, ‖spectralBandCoefficients a τ ξ none k‖ ^ 2 *
        (spectralWeight τ (List.ofFn ξ : Multiset ℝ) (k.val : ℝ)) ^ 2 := by
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : spectralBandCoefficients a τ ξ none k = 0
  · simp [hk]
  · have hsep := (spectralBandIndex_eq_none_iff τ ξ (k.val : ℝ)).mp
      (spectralBandIndex_eq_of_coefficient_ne_zero a τ ξ none k hk)
    have hweight : spectralWeight τ (List.ofFn ξ : Multiset ℝ) (k.val : ℝ) = 1 := by
      rw [spectralWeight_ofFn]
      apply Finset.prod_eq_one
      intro j _
      apply min_eq_left
      have := (div_le_iff₀ hτ).mp (hsep j)
      nlinarith
    simp only [hweight, one_pow, mul_one]

/-- The residual Fourier energy is bounded by the full weighted coefficient
    energy. -/
theorem integral_residualBand_energy_le {N m : ℕ} (a : Fin (N + 1) → ℂ)
    {τ : ℝ} (hτ : 0 < τ) (ξ : Fin m → ℝ) :
    (∫ q, ‖randomFourier (spectralBandCoefficients a τ ξ none) q‖ ^ 2
      ∂fourierMeasure N) ≤
      ∑ k, ‖a k‖ ^ 2 * (spectralWeight τ (List.ofFn ξ : Multiset ℝ) (k.val : ℝ)) ^ 2 := by
  rw [integral_norm_sq_randomFourier, residualBand_energy_eq_weighted a hτ ξ]
  exact spectralBand_weighted_energy_le a τ ξ _ (fun _ => sq_nonneg _) none

/-- A non-residual band's local differential energy is controlled by the full
    original weighted energy, with the exact angular normalization. -/
theorem integral_spectralBand_derivative_energy_le {N m : ℕ}
    (a : Fin (N + 1) → ℂ) {τ : ℝ} (hτ : 0 < τ) (ξ : Fin m → ℝ) (j : Fin m) :
    (∫ q, ‖randomFourier (fun k => spectralBandCoefficients a τ ξ (some j) k *
      spectralDerivativeMultiplier
        (spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)) (k.val : ℝ)) q‖ ^ 2
      ∂fourierMeasure N) ≤
      (6 * Real.pi / τ) ^ (2 * (spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)).card) *
        ∑ k, ‖a k‖ ^ 2 *
          (spectralWeight τ (List.ofFn ξ : Multiset ℝ) (k.val : ℝ)) ^ 2 := by
  apply (integral_cluster_derivative_energy_le (spectralBandCoefficients a τ ξ (some j))
    hτ (List.ofFn ξ : Multiset ℝ)
    (fun k hk => (spectralBandCoefficients_support a τ ξ j k hk).le)).trans
  exact mul_le_mul_of_nonneg_left
    (spectralBand_weighted_energy_le a τ ξ _ (fun _ => sq_nonneg _) (some j))
    (by positivity)

end Erdos522.LogMoments

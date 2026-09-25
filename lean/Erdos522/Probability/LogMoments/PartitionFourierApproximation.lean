/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.SpectralApproximationError
import Erdos522.Analysis.UnitIntervalAverages

/-!
# Fourier approximation on a fixed angular partition

Spectral band approximation on each cell is controlled by a single nonnegative
square-integrable function. The approximation factor is the cell length divided
by the shift scale, raised to the number of spectral frequencies.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Erdos522.LogMoments

theorem spectralBandIntegralError_le_partition_average {N m : ℕ}
    (a : Fin (N + 1) → ℂ) {τ M : ℝ} (hτ : 0 < τ) (hM : 1 ≤ M)
    (ξ : Fin m → ℝ) {q : ℕ} (hq : 0 < q) (hscale : 1 / (q : ℝ) = M * τ)
    (ω : SignVector N) (i : Fin q) (j : Fin m) {x : ℝ}
    (hx : x ∈ unitIntervalCell i) :
    spectralBandIntegralError a τ ξ ω ((i.val : ℝ) / q) (((i.val : ℝ) + 1) / q) j ≤
      M ^ m * (τ ^ (spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)).card *
        partitionNormAverage unitIntervalMeasure (unitIntervalCell (q := q))
          (fun t => realFourier (spectralBandForcing a τ ξ j) (ω, t)) x) := by
  have hc := spectralCluster_ofFn_card_bounds hτ ξ j
  rw [spectralBandIntegralError, unitIntervalCell_length]
  rw [cell_remainder_eq_length_pow_mul_average hq i _ hc.1]
  rw [partitionNormAverage_eq_of_mem unitIntervalMeasure _ _
    (pairwiseDisjoint_unitIntervalCell hq) hx, hscale, mul_pow]
  change (M ^ _ * τ ^ _) * normCellAverage _ _ _ ≤ _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM hc.2)
    (mul_nonneg (pow_nonneg hτ.le _) (normCellAverage_nonneg _ _ _))

/-- Every cell admits a random exponential approximant in the same spectrum,
with one common error majorant for the whole partition. -/
theorem exists_partition_fourier_approximation {N m : ℕ}
    (a : Fin (N + 1) → ℂ) {τ M : ℝ} (hτ : 0 < τ) (hM : 1 ≤ M)
    (ξ : Fin m → ℝ) (hξ : Function.Injective ξ) {q : ℕ} (hq : 0 < q)
    (hscale : 1 / (q : ℝ) = M * τ) (i : Fin q) :
    ∃ p : SignVector N → ℝ → ℂ,
      (∀ ω, p ω ∈ exponentialSpan (Set.range ξ)) ∧
      ∀ ω x, x ∈ unitIntervalCell i →
        ‖realFourier a (ω, x) - p ω x‖ ≤
          M ^ m * fourierApproximationError a τ ξ q (ω, x) := by
  classical
  have hp (ω : SignVector N) := exists_spectral_band_approximation a hτ ξ hξ ω
    (unitIntervalCell_endpoints hq i).2.1.le
  choose p hspan hbound using hp
  refine ⟨p, hspan, ?_⟩
  intro ω x hx
  have hx' : x ∈ Set.Icc ((i.val : ℝ) / q) (((i.val : ℝ) + 1) / q) :=
    ⟨hx.1, hx.2.le⟩
  apply (hbound ω x hx').trans
  change _ ≤ M ^ m * (‖realFourier (spectralBandCoefficients a τ ξ none) (ω, x)‖ + _)
  rw [mul_add, Finset.mul_sum]
  apply add_le_add
  · exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hM)
  · exact Finset.sum_le_sum fun j _ =>
      spectralBandIntegralError_le_partition_average a hτ hM ξ hq hscale ω i j hx

end Erdos522.LogMoments

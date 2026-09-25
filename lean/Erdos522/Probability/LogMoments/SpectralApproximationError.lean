/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.BandApproximation
import Erdos522.Probability.LogMoments.RealFourier
import Erdos522.Analysis.PartitionErrorEnergy
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The spectral approximation error in squared mean

Scaled cell averages of the band differential forcings, together with the
residual Fourier band, give a nonnegative `L²` majorant. Its energy depends
only on the weighted spectral energy and the number of frequencies.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Erdos522.LogMoments

/-- The fixed-partition majorant for spectral approximation. -/
def fourierApproximationError {N m : ℕ} (a : Fin (N + 1) → ℂ) (τ : ℝ)
    (ξ : Fin m → ℝ) (q : ℕ) : SignVector N × ℝ → ℝ :=
  partitionError unitIntervalMeasure (unitIntervalCell (q := q))
    (realFourier (spectralBandCoefficients a τ ξ none))
    (fun j => realFourier (spectralBandForcing a τ ξ j))
    (fun j => τ ^ (spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)).card)

theorem fourierApproximationError_nonneg {N m : ℕ} (a : Fin (N + 1) → ℂ)
    {τ : ℝ} (hτ : 0 ≤ τ) (ξ : Fin m → ℝ) (q : ℕ) (z : SignVector N × ℝ) :
    0 ≤ fourierApproximationError a τ ξ q z :=
  partitionError_nonneg _ _ _ _ _ (fun _ => pow_nonneg hτ _) z

/-- The spectral error majorant is square-integrable under the actual model. -/
theorem memLp_fourierApproximationError {N m : ℕ} (a : Fin (N + 1) → ℂ)
    (τ : ℝ) (ξ : Fin m → ℝ) {q : ℕ} (hq : 0 < q) :
    MemLp (fourierApproximationError a τ ξ q) 2 (realFourierMeasure N) :=
  memLp_partitionError (signMeasure N) unitIntervalMeasure _ _ _ _
    measurableSet_unitIntervalCell (pairwiseDisjoint_unitIntervalCell hq)
    (memLp_realFourier _)

/-- A band's scaled forcing has an energy bound independent of the shift scale. -/
theorem scaled_spectralBandForcing_energy_le {N m : ℕ} (a : Fin (N + 1) → ℂ)
    {τ : ℝ} (hτ : 0 < τ) (ξ : Fin m → ℝ) (j : Fin m) :
    (τ ^ (spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)).card) ^ 2 *
      (∫ z, ‖realFourier (spectralBandForcing a τ ξ j) z‖ ^ 2 ∂realFourierMeasure N) ≤
        (6 * Real.pi) ^ (2 * m) *
          ∑ k, ‖a k‖ ^ 2 * (spectralWeight τ (List.ofFn ξ : Multiset ℝ) k.val) ^ 2 := by
  rw [integral_norm_sq_realFourier_eq_circle]
  have h := mul_le_mul_of_nonneg_left (integral_spectralBand_derivative_energy_le a hτ ξ j)
    (sq_nonneg (τ ^ (spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)).card))
  have hcancel (k : ℕ) : (τ ^ k) ^ 2 * (6 * Real.pi / τ) ^ (2 * k) = (6 * Real.pi) ^ (2 * k) := by
    rw [← pow_mul, Nat.mul_comm k 2, ← mul_pow]
    rw [mul_div_cancel₀ _ hτ.ne']
  have hscale : (τ ^ (spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)).card) ^ 2 *
      ((6 * Real.pi / τ) ^ (2 * (spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)).card) *
        ∑ k, ‖a k‖ ^ 2 * (spectralWeight τ (List.ofFn ξ : Multiset ℝ) k.val) ^ 2) =
      (6 * Real.pi) ^ (2 * (spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)).card) *
        ∑ k, ‖a k‖ ^ 2 * (spectralWeight τ (List.ofFn ξ : Multiset ℝ) k.val) ^ 2 := by
    rw [← mul_assoc, hcancel]
  rw [hscale] at h
  apply h.trans
  gcongr
  · linarith [Real.pi_gt_three]
  · exact (spectralCluster_ofFn_card_bounds hτ ξ j).2

/-- The complete majorant has squared energy at most `(m+1)² (6π)^(2m)`
times the weighted spectral energy. -/
theorem integral_fourierApproximationError_sq_le {N m : ℕ} (a : Fin (N + 1) → ℂ)
    {τ : ℝ} (hτ : 0 < τ) (ξ : Fin m → ℝ) {q : ℕ} (hq : 0 < q) :
    (∫ z, fourierApproximationError a τ ξ q z ^ 2 ∂realFourierMeasure N) ≤
      ((m : ℝ) + 1) ^ 2 * ((6 * Real.pi) ^ (2 * m) *
        ∑ k, ‖a k‖ ^ 2 * (spectralWeight τ (List.ofFn ξ : Multiset ℝ) k.val) ^ 2) := by
  have h₀ := integral_residualBand_energy_le a hτ ξ
  have hπ : (1 : ℝ) ≤ (6 * Real.pi) ^ (2 * m) :=
    one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hW : 0 ≤ ∑ k, ‖a k‖ ^ 2 * (spectralWeight τ (List.ofFn ξ : Multiset ℝ) k.val) ^ 2 :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hres : (∫ z, ‖realFourier (spectralBandCoefficients a τ ξ none) z‖ ^ 2
      ∂realFourierMeasure N) ≤ (6 * Real.pi) ^ (2 * m) *
        ∑ k, ‖a k‖ ^ 2 * (spectralWeight τ (List.ofFn ξ : Multiset ℝ) k.val) ^ 2 := by
    rw [integral_norm_sq_realFourier_eq_circle]
    exact h₀.trans (le_mul_of_one_le_left hW hπ)
  simpa only [Fintype.card_fin, fourierApproximationError, realFourierMeasure] using integral_partitionError_sq_le (signMeasure N)
    unitIntervalMeasure (unitIntervalCell (q := q))
    (realFourier (spectralBandCoefficients a τ ξ none))
    (fun j => realFourier (spectralBandForcing a τ ξ j))
    (fun j => τ ^ (spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)).card)
    measurableSet_unitIntervalCell (pairwiseDisjoint_unitIntervalCell hq)
    (unitIntervalMeasure_real_cell_pos hq) (memLp_realFourier _)
    (fun j ω => memLp_realFourier_section _ ω) (fun j => integrable_norm_sq_realFourier _)
    hres (scaled_spectralBandForcing_energy_le a hτ ξ)

end Erdos522.LogMoments

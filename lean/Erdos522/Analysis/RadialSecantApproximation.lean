/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.ScaledRadialProbes

/-!
# Radial secants with a vanishing logarithmic error

The deterministic Jensen sandwich depends only on the error in the four
logarithmic averages. Any error tending to zero gives the same limiting
secants of the Kac variance profile.
-/

noncomputable section
open MeasureTheory Filter Polynomial
open scoped Topology
namespace Erdos522
open LogMoments

def approximateLowerRadialSecant (e : ℕ → ℝ) (x h : ℝ) (N : ℕ) : ℝ :=
  (Real.log (radialSigma N (1 + (x - h) / N)) -
      Real.log (radialSigma N (1 + (x - 2 * h) / N)) - 2 * e N) /
    ((N : ℝ) * Real.log ((1 + (x - h) / N) / (1 + (x - 2 * h) / N)))

def approximateUpperRadialSecant (e : ℕ → ℝ) (x h : ℝ) (N : ℕ) : ℝ :=
  (Real.log (radialSigma N (1 + (x + 2 * h) / N)) -
      Real.log (radialSigma N (1 + (x + h) / N)) + 2 * e N) /
    ((N : ℝ) * Real.log ((1 + (x + 2 * h) / N) / (1 + (x + h) / N)))

/-- Logarithmic control at shifted probes gives the actual radial-count sandwich. -/
theorem radial_fraction_between_approximate_secants (P : Polynomial ℂ) (N : ℕ) (e : ℕ → ℝ)
    (x : ℝ) {h r : ℝ} (hh : 0 < h) (hN : |x| + 2 * h < N)
    (hrl : 1 + (x - h) / N ≤ r) (hru : r ≤ 1 + (x + h) / N)
    (hlog : ∀ i : Fin 4,
      |logCircleAverage P (scaledRadialProbes x h N i) -
        Real.log (radialSigma N (scaledRadialProbes x h N i)) - circularLogMean| ≤ e N) :
    approximateLowerRadialSecant e x h N ≤ (closedZeroCount P r : ℝ) / N ∧
      (closedZeroCount P r : ℝ) / N ≤ approximateUpperRadialSecant e x h N := by
  have hn : (0 : ℝ) < N := by linarith [abs_nonneg x]
  have h₀ : 0 < 1 + (x - 2 * h) / N := by
    have h := (lt_div_iff₀ hn).mpr (show -1 * (N : ℝ) < x - 2 * h by linarith [neg_abs_le x])
    linarith
  have h₂ : 0 < 1 + (x + h) / N := by
    have h := (lt_div_iff₀ hn).mpr (show -1 * (N : ℝ) < x + h by linarith [neg_abs_le x])
    linarith
  have h₀₁ : 1 + (x - 2 * h) / N < 1 + (x - h) / N := by
    linarith [div_lt_div_of_pos_right (show x - 2 * h < x - h by linarith) hn]
  have h₂₃ : 1 + (x + h) / N < 1 + (x + 2 * h) / N := by
    linarith [div_lt_div_of_pos_right (show x + h < x + 2 * h by linarith) hn]
  exact radial_fraction_of_four_logarithmic_errors P (fun r => Real.log (radialSigma N r))
    hn h₀ h₀₁ h₂ h₂₃ hrl hru
    (by simpa [scaledRadialProbes] using hlog 0)
    (by simpa [scaledRadialProbes] using hlog 1)
    (by simpa [scaledRadialProbes] using hlog 2)
    (by simpa [scaledRadialProbes] using hlog 3)

theorem tendsto_approximateLowerRadialSecant {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) (x : ℝ) {h : ℝ} (hh : 0 < h) :
    Tendsto (approximateLowerRadialSecant e x h) atTop
      (𝓝 ((kacLogVarianceProfile (x - h) - kacLogVarianceProfile (x - 2 * h)) / h)) := by
  unfold approximateLowerRadialSecant
  have ht := ((tendsto_log_radialSigma_sub (x - 2 * h) (x - h)).sub
    (he.const_mul 2)).div
      (tendsto_degree_mul_log_radius_ratio (x - 2 * h) (x - h)) (by linarith : x - h - (x - 2 * h) ≠ 0)
  simpa only [mul_zero, sub_zero, Pi.div_def, show x - h - (x - 2 * h) = h by ring] using ht

theorem tendsto_approximateUpperRadialSecant {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) (x : ℝ) {h : ℝ} (hh : 0 < h) :
    Tendsto (approximateUpperRadialSecant e x h) atTop
      (𝓝 ((kacLogVarianceProfile (x + 2 * h) - kacLogVarianceProfile (x + h)) / h)) := by
  unfold approximateUpperRadialSecant
  have ht := ((tendsto_log_radialSigma_sub (x + h) (x + 2 * h)).add
    (he.const_mul 2)).div
      (tendsto_degree_mul_log_radius_ratio (x + h) (x + 2 * h)) (by linarith : x + 2 * h - (x + h) ≠ 0)
  simpa only [mul_zero, add_zero, Pi.div_def, show x + 2 * h - (x + h) = h by ring] using ht


end Erdos522

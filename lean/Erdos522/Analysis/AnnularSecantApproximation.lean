/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SparseAnnularTightness

/-!
# Annular secants with a vanishing logarithmic error

Four radial probes bound the multiplicity-counted mass outside a closed
annulus. Their exact finite variance envelope has the same limiting tail
coefficient for every logarithmic error tending to zero.
-/

noncomputable section
open MeasureTheory Filter Set Polynomial
open scoped Topology
namespace Erdos522
open LogMoments

/-- The normalized four-radius bound, with exact finite variance and both
logarithmic errors in each secant. -/
def approximateAnnularSecantEnvelope (e : ℕ → ℝ) (K : ℝ) (N : ℕ) : ℝ :=
  1 + (Real.log (radialSigma N (radialSecantRadii K N 1)) -
      Real.log (radialSigma N (radialSecantRadii K N 0)) + 2 * e N) /
        ((N : ℝ) * Real.log (radialSecantRadii K N 1 / radialSecantRadii K N 0)) -
    (Real.log (radialSigma N (radialSecantRadii K N 3)) -
      Real.log (radialSigma N (radialSecantRadii K N 2)) - 2 * e N) /
        ((N : ℝ) * Real.log (radialSecantRadii K N 3 / radialSecantRadii K N 2))

/-- Four finite logarithmic errors give the exact normalized annular tail bound,
with all zeros counted according to multiplicity. -/
theorem radial_mass_le_approximate_secant_envelope (P : Polynomial ℂ) (N : ℕ) (e : ℕ → ℝ)
    (hdegree : P.natDegree = N) {K : ℝ} (hK : 0 < K) (hNK : 2 * K < N)
    (hlog : ∀ i : Fin 4,
      |logCircleAverage P (radialSecantRadii K N i) -
        Real.log (radialSigma N (radialSecantRadii K N i)) - circularLogMean| ≤ e N) :
    (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) / N ≤ approximateAnnularSecantEnvelope e K N := by
  have hn : (0 : ℝ) < N := by linarith
  have ha : 0 < K / N := div_pos hK hn
  have ha' : K / N < 1 / 2 := (div_lt_iff₀ hn).mpr (by linarith)
  have hr₀ : radialSecantRadii K N 0 = 1 - K / N := by simp [radialSecantRadii]; ring
  have hr₁ : radialSecantRadii K N 1 = 1 - (K / N) / 2 := by simp [radialSecantRadii]; ring
  have hr₂ : radialSecantRadii K N 2 = 1 + (K / N) / 2 := by simp [radialSecantRadii]; ring
  have hr₃ : radialSecantRadii K N 3 = 1 + K / N := by simp [radialSecantRadii]
  have he (i : Fin 4) : |logCircleAverage P (radialSecantRadii K N i) -
      (Real.log (radialSigma N (radialSecantRadii K N i)) + circularLogMean)| ≤ e N := by
    convert hlog i using 1
    ring_nf
  have h := radial_mass_of_log_integral_errors P
    (r₁ := radialSecantRadii K N 0) (r₂ := radialSecantRadii K N 1)
    (r₃ := radialSecantRadii K N 2) (r₄ := radialSecantRadii K N 3)
    (by rw [hr₀]; linarith) (by rw [hr₀, hr₁]; linarith)
    (by rw [hr₂]; linarith) (by rw [hr₂, hr₃]; linarith)
    (he 0) (he 1) (he 2) (he 3)
  have hset : {z : ℂ | ‖z‖ < radialSecantRadii K N 0 ∨ radialSecantRadii K N 3 < ‖z‖} =
      {z : ℂ | |‖z‖ - 1| ≤ K / N}ᶜ := by
    rw [hr₀, hr₃]
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le, lt_abs]
    constructor
    · rintro (hz | hz)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    · rintro (hz | hz)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
  rw [hset, hdegree] at h
  refine (div_le_div_of_nonneg_right h hn.le).trans_eq ?_
  unfold approximateAnnularSecantEnvelope
  field_simp
  ring

/-- The exact finite variance envelope converges to the four secants of the Kac profile. -/
theorem tendsto_approximateAnnularSecantEnvelope {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) {K : ℝ} (hK : 0 < K) :
    Tendsto (approximateAnnularSecantEnvelope e K) atTop (𝓝 (kacAnnularTailCoefficient K)) := by
  unfold approximateAnnularSecantEnvelope
  have hin := ((tendsto_log_radialSigma_sub (-K) (-K / 2)).add
    (he.const_mul 2)).div
      (tendsto_degree_mul_log_radius_ratio (-K) (-K / 2)) (by linarith : -K / 2 - -K ≠ 0)
  have hout := ((tendsto_log_radialSigma_sub (K / 2) K).sub
    (he.const_mul 2)).div
      (tendsto_degree_mul_log_radius_ratio (K / 2) K) (by linarith : K - K / 2 ≠ 0)
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).add hin |>.sub hout
  simpa [kacAnnularTailCoefficient, radialSecantRadii,
    show -K / 2 - -K = K / 2 by ring, show K - K / 2 = K / 2 by ring] using ht


end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.ThinAnnularLogarithmicControl
import Erdos522.Probability.GrowingAnnularMass
import Erdos522.Analysis.FiniteRadialProfileBound
import Erdos522.Probability.RadialCountInterpolation

/-!
# Quantitative root counts in the matching window

Four shrinking Jensen probes control every target radius in the matching
window on one almost-sure event. Their error is negligible even after
multiplication by the logarithm of the degree.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522
open LogMoments

/-- The finite radial error from the shrinking probes and a fixed variance bound. -/
def thinRadialError (H : ℝ) (N : ℕ) : ℝ :=
  6 * thinAnnularWidth N + 8 *
    (logarithmicPowerTolerance (1 / 32) (fourierLogarithmicConstant harmonicRestrictionConstant) H N +
      kacVarianceApproximationError N 4) / thinAnnularWidth N

/-- The matching window lies between the two middle shrinking probes. -/
theorem radialMatchingWindow_le_thin_half_width {N : ℕ} (hN : 0 < N) :
    radialMatchingWindow N ≤ thinAnnularWidth N / (2 * N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : radialMatchingWindow N = (N : ℝ) ^ (-(1 / 64 : ℝ)) / N := by
    unfold radialMatchingWindow
    rw [← Real.rpow_sub_one hn.ne']
    congr 1
    ring
  rw [hw]
  unfold thinAnnularWidth
  have hp : 0 ≤ (N : ℝ) ^ (-(1 / 64 : ℝ)) / N := by positivity
  nlinarith [show 4 * (N : ℝ) ^ (-(1 / 64 : ℝ)) / (2 * N) =
    2 * ((N : ℝ) ^ (-(1 / 64 : ℝ)) / N) by ring]

/-- The radial error is smaller than every constant multiple of `1/log N`. -/
theorem tendsto_log_mul_thinRadialError (H : ℝ) :
    Tendsto (fun N : ℕ => Real.log N * thinRadialError H N) atTop (𝓝 0) := by
  let A := fourierLogarithmicConstant harmonicRestrictionConstant
  let V := (4 : ℝ) ^ 2 + 4 + Real.exp (2 * 4) / 2
  have h := tendsto_log_mul_thinAnnularWidth.const_mul 6 |>.add
    (((tendsto_log_mul_tolerance_div_thinAnnularWidth A H).add
      (tendsto_log_div_degree_mul_thinAnnularWidth.const_mul V)).const_mul 8)
  simp only [mul_zero, add_zero] at h
  apply h.congr
  intro N
  unfold thinRadialError kacVarianceApproximationError
  dsimp [A, V]
  ring

/-- Almost surely, every radius in the matching window has the same quantitative
half-density bound at all sufficiently large sparse degrees. -/
theorem exists_ae_thin_radial_bound :
    ∃ H : ℝ, 0 < H ∧ ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      let N := realPowerDegree 8 j
      ∀ r : ℝ, |r - 1| ≤ radialMatchingWindow N →
        |rademacherRadialFraction ω N r - 1 / 2| ≤ thinRadialError H N := by
  obtain ⟨H, hH, hlog⟩ := exists_ae_thin_annular_logarithmic_bound
  refine ⟨H, hH, ?_⟩
  filter_upwards [hlog] with ω hω
  filter_upwards [hω, (tendsto_realPowerDegree (by norm_num : (0 : ℝ) < 8)).eventually_ge_atTop 32]
    with j hj hN
  dsimp only
  let N := realPowerDegree 8 j
  let K := thinAnnularWidth N
  let P := rademacherPolynomial N (rademacherPrefix N ω)
  let E := logarithmicPowerTolerance (1 / 32)
    (fourierLogarithmicConstant harmonicRestrictionConstant) H N + kacVarianceApproximationError N 4
  have hn : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hn
  have hN32 : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have hK : 0 < K := thinAnnularWidth_pos hn
  have hK4 : K ≤ 4 := thinAnnularWidth_le_four (by omega)
  have hNK : 8 * K ≤ (N : ℝ) := by linarith
  have hE : 0 ≤ E := by
    have hl := Real.log_natCast_nonneg N
    unfold E logarithmicPowerTolerance powerLogarithmicMomentCutoff kacVarianceApproximationError
    positivity
  let x : Fin 4 → ℝ := ![-K, -K / 2, K / 2, K]
  have hx (i : Fin 4) : |x i| ≤ 4 := by
    fin_cases i <;> simp [x, abs_div, abs_neg, abs_of_pos hK] <;> linarith
  have hprofile (i : Fin 4) :
      |logCircleAverage P (radialSecantRadii K N i) -
        (kacLogVarianceProfile (x i) + ((1 / 2 : ℝ) * Real.log N + circularLogMean))| ≤ E := by
    have he := hj i
    change |logCircleAverage P (1 + x i / N) -
      Real.log (radialSigma N (1 + x i / N)) - circularLogMean| ≤
        logarithmicPowerTolerance (1 / 32) (fourierLogarithmicConstant harmonicRestrictionConstant) H N at he
    have hv := abs_log_radialSigma_profile_le hn (by norm_num : (0 : ℝ) ≤ 4)
      (by linarith) (hx i)
    change |logCircleAverage P (1 + x i / N) -
      (kacLogVarianceProfile (x i) + ((1 / 2 : ℝ) * Real.log N + circularLogMean))| ≤ E
    calc
      _ = |(logCircleAverage P (1 + x i / N) - Real.log (radialSigma N (1 + x i / N)) -
          circularLogMean) + (Real.log (radialSigma N (1 + x i / N)) -
            (1 / 2 : ℝ) * Real.log N - kacLogVarianceProfile (x i))| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add he hv)
  intro r hr
  have hwidth := radialMatchingWindow_le_thin_half_width hn
  have hrl : 1 - K / (2 * N) ≤ r := by have := (abs_le.mp hr).1; dsimp [K]; linarith
  have hru : r ≤ 1 + K / (2 * N) := by have := (abs_le.mp hr).2; dsimp [K]; linarith
  exact radial_fraction_half_error_le P N hK hE hNK hrl hru hprofile

end Erdos522

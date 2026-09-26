/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.FiniteAnnularMass
import Erdos522.Analysis.KacVarianceApproximation
import Erdos522.Probability.GrowingAnnularLogarithmicConcentration

/-!
# Radial mass in logarithmically growing annuli

Four simultaneous log-integral estimates combine with the finite variance
profile to retain the explicit annular tail coefficient at growing width.
The probes at `±(K - 1)` and `±K` give the coefficient `1 / (K - 1)`.
-/

noncomputable section
open MeasureTheory Filter Polynomial
open scoped Topology
namespace Erdos522
open LogMoments

/-- The deterministic variance approximation error over a width `K`. -/
def kacVarianceApproximationError (N : ℕ) (K : ℝ) : ℝ :=
  (K ^ 2 + K + Real.exp (2 * K) / 2) / N

/-- Four finite log-integral errors imply the quantitative annular mass bound. -/
theorem radial_mass_le_finite_variance_bound (P : ℂ[X]) (N : ℕ) (hdegree : P.natDegree = N)
    {K E : ℝ} (hK : 0 < K) (hNK : 2 * K < N)
    (hlog : ∀ i : Fin 4, |logCircleAverage P (radialSecantRadii K N i) -
      Real.log (radialSigma N (radialSecantRadii K N i)) - circularLogMean| ≤ E) :
    (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) / N ≤
      2 * Real.log 2 / K + 8 * (E + kacVarianceApproximationError N K) / K := by
  have hn : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  let x : Fin 4 → ℝ := ![-K, -K / 2, K / 2, K]
  have hx (i : Fin 4) : |x i| ≤ K := by
    fin_cases i <;> simp [x, abs_div, abs_neg, abs_of_pos hK] <;> linarith
  have hprofile (i : Fin 4) :
      |logCircleAverage P (1 + x i / N) -
        (kacLogVarianceProfile (x i) + ((1 / 2 : ℝ) * Real.log N + circularLogMean))| ≤
      E + kacVarianceApproximationError N K := by
    have he := hlog i
    change |logCircleAverage P (1 + x i / N) -
      Real.log (radialSigma N (1 + x i / N)) - circularLogMean| ≤ E at he
    have hv := abs_log_radialSigma_profile_le hn hK.le hNK.le (hx i)
    calc
      _ = |(logCircleAverage P (1 + x i / N) - Real.log (radialSigma N (1 + x i / N)) -
          circularLogMean) + (Real.log (radialSigma N (1 + x i / N)) -
            (1 / 2 : ℝ) * Real.log N - kacLogVarianceProfile (x i))| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add he hv)
  have h := radial_mass_le_kac_profile_bound P N hdegree hK hNK
    (E := E + kacVarianceApproximationError N K)
    (c := (1 / 2 : ℝ) * Real.log N + circularLogMean)
  apply h
  · simpa only [x, Matrix.cons_val_zero, neg_div, sub_eq_add_neg] using hprofile 0
  · simpa only [show x 1 = -K / 2 from rfl,
      show 1 + (-K / 2) / (N : ℝ) = 1 - K / (2 * N) by ring] using hprofile 1
  · simpa only [show x 2 = K / 2 from rfl,
      show 1 + (K / 2) / (N : ℝ) = 1 + K / (2 * N) by ring] using hprofile 2
  · simpa only [x, Matrix.cons_val] using hprofile 3

/-- Four finite log-integral errors at the probes `±(K - 1)` and `±K` imply the
annular mass bound with tail coefficient `1 / (K - 1)`. -/
theorem radial_mass_le_finite_variance_unit_gap_bound (P : ℂ[X]) (N : ℕ)
    (hdegree : P.natDegree = N) {K E : ℝ} (hK : 1 < K) (hNK : 2 * K < N)
    (hlog : ∀ i : Fin 4, |logCircleAverage P (radialUnitGapRadii K N i) -
      Real.log (radialSigma N (radialUnitGapRadii K N i)) - circularLogMean| ≤ E) :
    (zeroCountIn P {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) / N ≤
      1 / (K - 1) + 4 * (E + kacVarianceApproximationError N K) := by
  have hK0 : 0 < K := by linarith
  have hn : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  let x : Fin 4 → ℝ := ![-K, -(K - 1), K - 1, K]
  have hx (i : Fin 4) : |x i| ≤ K := by
    have h₁ : |1 - K| = K - 1 := by rw [abs_sub_comm]; exact abs_of_pos (by linarith)
    fin_cases i <;> simp [x, abs_neg, abs_of_pos hK0, abs_of_pos (show 0 < K - 1 by linarith), h₁]
  have hprofile (i : Fin 4) :
      |logCircleAverage P (1 + x i / N) -
        (kacLogVarianceProfile (x i) + ((1 / 2 : ℝ) * Real.log N + circularLogMean))| ≤
      E + kacVarianceApproximationError N K := by
    have he := hlog i
    change |logCircleAverage P (1 + x i / N) -
      Real.log (radialSigma N (1 + x i / N)) - circularLogMean| ≤ E at he
    have hv := abs_log_radialSigma_profile_le hn hK0.le hNK.le (hx i)
    calc
      _ = |(logCircleAverage P (1 + x i / N) - Real.log (radialSigma N (1 + x i / N)) -
          circularLogMean) + (Real.log (radialSigma N (1 + x i / N)) -
            (1 / 2 : ℝ) * Real.log N - kacLogVarianceProfile (x i))| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add he hv)
  have h := radial_mass_le_kac_profile_unit_gap_bound P N hdegree hK hNK
    (E := E + kacVarianceApproximationError N K)
    (c := (1 / 2 : ℝ) * Real.log N + circularLogMean)
  apply h
  · simpa only [x, Matrix.cons_val_zero, neg_div, sub_eq_add_neg] using hprofile 0
  · simpa only [show x 1 = -(K - 1) from rfl,
      show 1 + -(K - 1) / (N : ℝ) = 1 - (K - 1) / N by ring] using hprofile 1
  · simpa only [show x 2 = K - 1 from rfl] using hprofile 2
  · simpa only [x, Matrix.cons_val] using hprofile 3

/-- Widths greater than one satisfy the strict finite annular geometry eventually. -/
theorem eventually_one_lt_logarithmicAnnularWidth_lt :
    ∀ᶠ N : ℕ in atTop, 1 < logarithmicAnnularWidth N ∧ 2 * logarithmicAnnularWidth N < N := by
  have h := tendsto_logarithmicAnnularWidth_factor (a := 0) (b := 1) (by norm_num) (by norm_num) 1 0
  simp only [zero_mul, Real.exp_zero, pow_zero, pow_one, mul_one, Real.rpow_one] at h
  filter_upwards [tendsto_logarithmicAnnularWidth_atTop.eventually_gt_atTop 1,
    h.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2), eventually_ge_atTop 1] with N hK hN hn
  have hpos : (0 : ℝ) < N := by exact_mod_cast hn
  exact ⟨hK, by have := (div_lt_iff₀ hpos).mp hN; linarith⟩

/-- The growing-annulus mass bound holds eventually on the shared coefficient sequence. -/
theorem exists_ae_growing_annular_mass_bound {q : ℝ} (hq : 128 / 39 < q) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      let N := realPowerDegree q j
      let K := logarithmicAnnularWidth N
      (zeroCountIn (rademacherPolynomial N (rademacherPrefix N ω))
        {z | |‖z‖ - 1| ≤ K / N}ᶜ : ℝ) / N ≤
      1 / (K - 1) + 4 *
        (growingLogarithmicTolerance (fourierLogarithmicConstant harmonicRestrictionConstant)
          (rademacherOccupationConstant B K) N + kacVarianceApproximationError N K) := by
  obtain ⟨B, hB, hlog⟩ := exists_ae_growing_annular_logarithmic_bound hq
  refine ⟨B, hB, ?_⟩
  filter_upwards [hlog] with ω hω
  filter_upwards [hω, (tendsto_realPowerDegree (show 0 < q by linarith)).eventually
    eventually_one_lt_logarithmicAnnularWidth_lt] with j hj hN
  exact radial_mass_le_finite_variance_unit_gap_bound _ _
    (rademacherPolynomial_prefix_natDegree ω _) hN.1 hN.2 hj

end Erdos522

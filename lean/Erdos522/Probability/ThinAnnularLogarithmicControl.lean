/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogarithmicPowerConcentration

/-!
# Logarithmic control at a shrinking annular width

A single finite family of Jensen probes suffices for simultaneous radial
control throughout the matching window. Its concentration takes place in a
fixed enlarged annulus, so its constants are independent of the degree.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- The four-probe width covering the radial matching window. -/
def thinAnnularWidth (N : ℕ) : ℝ := 4 * (N : ℝ) ^ (-(1 / 64 : ℝ))

theorem thinAnnularWidth_nonneg (N : ℕ) : 0 ≤ thinAnnularWidth N := by
  unfold thinAnnularWidth
  positivity

theorem thinAnnularWidth_pos {N : ℕ} (hN : 0 < N) : 0 < thinAnnularWidth N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold thinAnnularWidth
  positivity

theorem thinAnnularWidth_le_four {N : ℕ} (hN : 1 ≤ N) : thinAnnularWidth N ≤ 4 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num : -(1 / 64 : ℝ) ≤ 0)
  unfold thinAnnularWidth
  linarith

/-- Fixed logarithmic factors do not consume a strict tolerance power margin. -/
theorem tendsto_log_pow_mul_rpow_mul_logarithmicPowerTolerance {t κ : ℝ}
    (hκ : κ < t) (A H : ℝ) (m : ℕ) :
    Tendsto (fun N : ℕ => (Real.log N) ^ m * (N : ℝ) ^ κ *
      logarithmicPowerTolerance t A H N) atTop (𝓝 0) := by
  let s := (κ + t) / 2
  have hs : κ < s ∧ s < t := by dsimp [s]; constructor <;> linarith
  have ht := (tendsto_rpow_mul_logarithmicPowerTolerance hs.2 A H).mul
    (tendsto_log_pow_div_nat_rpow m (sub_pos.mpr hs.1))
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [Real.rpow_sub hn]
  field_simp

/-- The shrinking-width probes satisfy one simultaneous almost-sure logarithmic bound. -/
theorem exists_ae_thin_annular_logarithmic_bound :
    ∃ H : ℝ, 0 < H ∧ ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop, ∀ i : Fin 4,
      let N := realPowerDegree 8 j
      |logCircleAverage (rademacherPolynomial N (rademacherPrefix N ω))
          (radialSecantRadii (thinAnnularWidth N) N i) -
        Real.log (radialSigma N (radialSecantRadii (thinAnnularWidth N) N i)) - circularLogMean| ≤
          logarithmicPowerTolerance (1 / 32)
            (LogMoments.fourierLogarithmicConstant harmonicRestrictionConstant) H N := by
  apply exists_ae_real_power_logarithmic_power_bound (q := 8) (t := 1 / 32)
    (by norm_num) (by norm_num) (by norm_num) 4 (by norm_num)
    (fun N i => radialSecantRadii (thinAnnularWidth N) N i)
  filter_upwards [eventually_ge_atTop 1] with N hN
  intro i
  have hi := radialSecantRadii_mem_annulus (thinAnnularWidth_nonneg N) N i
  have hwidth : thinAnnularWidth N / N ≤ 4 / (N : ℝ) :=
    div_le_div_of_nonneg_right (thinAnnularWidth_le_four hN) (Nat.cast_nonneg N)
  exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

/-- The shrinking width is negligible at the logarithmic rate. -/
theorem tendsto_log_mul_thinAnnularWidth :
    Tendsto (fun N : ℕ => Real.log N * thinAnnularWidth N) atTop (𝓝 0) := by
  have h := (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1 / 64)).const_mul 4
  simp only [mul_zero, pow_one] at h
  apply h.congr
  intro N
  unfold thinAnnularWidth
  rw [Real.rpow_neg (Nat.cast_nonneg _)]
  ring

/-- Dividing the logarithmic tolerance by the thin width preserves its logarithmic decay. -/
theorem tendsto_log_mul_tolerance_div_thinAnnularWidth (A H : ℝ) :
    Tendsto (fun N : ℕ => Real.log N * logarithmicPowerTolerance (1 / 32) A H N /
      thinAnnularWidth N) atTop (𝓝 0) := by
  have h := (tendsto_log_pow_mul_rpow_mul_logarithmicPowerTolerance
    (t := 1 / 32) (κ := 1 / 64) (by norm_num) A H 1).div_const 4
  simp only [pow_one, zero_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold thinAnnularWidth
  rw [Real.rpow_neg hn.le]
  field_simp

/-- The finite variance-profile error is negligible after division by the thin width. -/
theorem tendsto_log_div_degree_mul_thinAnnularWidth :
    Tendsto (fun N : ℕ => Real.log N / ((N : ℝ) * thinAnnularWidth N)) atTop (𝓝 0) := by
  have h := (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 63 / 64)).div_const 4
  simp only [pow_one, zero_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : (N : ℝ) * (N : ℝ) ^ (-(1 / 64 : ℝ)) = (N : ℝ) ^ (63 / 64 : ℝ) := by
    nth_rw 1 [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hn]
    norm_num
  unfold thinAnnularWidth
  rw [show (N : ℝ) * (4 * (N : ℝ) ^ (-(1 / 64 : ℝ))) =
    4 * ((N : ℝ) * (N : ℝ) ^ (-(1 / 64 : ℝ))) by ring, hp]
  ring

end Erdos522

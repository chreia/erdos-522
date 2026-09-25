/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.RademacherLogMoments
import Erdos522.Probability.LogMoments.RestrictedEnergy
import Erdos522.Probability.LogMoments.ExponentialTails

/-!
# Negative logarithmic tails from restricted energy

The sixth-root transformation converts a logarithmic restricted-energy loss
into an exponential tail and an integrable stretched exponential.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Erdos522
namespace LogMoments

theorem root_negativeLogNorm_ge_subset_sublevel {Ω : Type*} {f : Ω → ℂ} {A s : ℝ}
    (hA : 0 < A) (hs : 0 < s) :
    {ω | s ≤ (negativeLogNorm (f ω) / A) ^ ((6 : ℝ)⁻¹)} ⊆
      {ω | ‖f ω‖ ≤ Real.exp (-A * s ^ 6)} := by
  intro ω hω
  have hx : 0 ≤ negativeLogNorm (f ω) / A := div_nonneg (negativeLogNorm_nonneg _) hA.le
  have hpow : ((negativeLogNorm (f ω) / A) ^ ((6 : ℝ)⁻¹)) ^ 6 =
      negativeLogNorm (f ω) / A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have h6 := pow_le_pow_left₀ hs.le hω 6
  rw [hpow] at h6
  have hn : A * s ^ 6 ≤ negativeLogNorm (f ω) := by
    simpa only [mul_comm] using (le_div_iff₀ hA).mp h6
  have hp : 0 < A * s ^ 6 := mul_pos hA (pow_pos hs 6)
  have hlog : Real.log ‖f ω‖ < 0 := by
    by_contra! h
    simp only [negativeLogNorm, max_eq_right (neg_nonpos.mpr h)] at hn
    linarith
  rw [negativeLogNorm, max_eq_left (neg_nonneg.mpr hlog.le)] at hn
  by_cases hz : f ω = 0
  · simpa only [mem_ofPred_eq, hz, norm_zero] using (Real.exp_pos (-A * s ^ 6)).le
  · exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hz)).mp (by linarith)

theorem integrable_exp_root_negativeLogNorm_of_restrictedEnergy
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℂ} {A : ℝ} (hA : 0 < A) (hf : Measurable f)
    (hI : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (hE : ∀ E : Set Ω, MeasurableSet E → 0 < μ.real E →
      1 ≤ Real.exp (A * Real.log (2 / μ.real E) ^ 6) * ∫ ω in E, ‖f ω‖ ^ 2 ∂μ) :
    Integrable (fun ω => Real.exp ((1 / 2 : ℝ) *
      (negativeLogNorm (f ω) / A) ^ ((6 : ℝ)⁻¹))) μ ∧
      (∫ ω, Real.exp ((1 / 2 : ℝ) *
        (negativeLogNorm (f ω) / A) ^ ((6 : ℝ)⁻¹)) ∂μ) ≤ 3 := by
  apply integrable_exp_half_and_integral_le
  · exact (((hf.norm.log.neg.max measurable_const).div_const A).pow_const _)
  · intro ω
    exact Real.rpow_nonneg (div_nonneg (negativeLogNorm_nonneg _) hA.le) _
  · intro s hs
    have hreal := (measureReal_mono (root_negativeLogNorm_ge_subset_sublevel hA hs)).trans
      (sublevel_measure_le_of_restrictedEnergy hA hf hI hE hs)
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)] using
      ENNReal.ofReal_le_ofReal hreal

end LogMoments
end Erdos522

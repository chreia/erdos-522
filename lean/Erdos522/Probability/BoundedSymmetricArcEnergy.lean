/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SymmetricArcEnergy
import Erdos522.Probability.AmplitudeEnergy
import Erdos522.Probability.BoundedPolynomialSuprema

/-!
# Arc energy for bounded centrally symmetric coefficients

Conditioning on the coefficient amplitudes gives a weighted Hanson--Wright
bound. The total amplitude energy has a separate Hoeffding lower tail. Their
sum controls the arc energy under the original complex coefficient law.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Erdos522.ArcEnergy

/-- The cost of an exceptional amplitude event is added once when averaging
the conditional sign-energy inequality. -/
theorem measure_complexEnergy_le_of_sign_tail_except {N : ℕ}
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] (s : Set Angle) {t p : ℝ} (hp : 0 ≤ p)
    (E : Set (Fin (N + 1) → ℂ)) (hE : MeasurableSet E)
    (htail : ∀ᵐ a ∂Measure.pi μ, a ∉ E →
      (LogMoments.signMeasure N).real {ω | weightedRandomEnergy a s ω ≤ t} ≤ p) :
    (Measure.pi μ).real {a | complexEnergy a s ≤ t} ≤ p + (Measure.pi μ).real E := by
  let ν := (LogMoments.signMeasure N).prod (Measure.pi μ)
  let F := fun q : LogMoments.SignVector N × (Fin (N + 1) → ℂ) =>
    fun k => LogMoments.sign (q.1 k) * q.2 k
  let D := {a : Fin (N + 1) → ℂ | complexEnergy a s ≤ t}
  let G := (F ⁻¹' D) \ (Set.univ ×ˢ E)
  have hD : MeasurableSet D := measurableSet_le (measurable_complexEnergy N s) measurable_const
  have hF : MeasurePreserving F ν (Measure.pi μ) :=
    measurePreserving_random_coordinate_signs μ (LogMoments.signMeasure N)
  have hG : MeasurableSet G := (hF.measurable hD).diff (MeasurableSet.univ.prod hE)
  have hGbound : ν.real G ≤ p := by
    have hprob : ν G ≤ ENNReal.ofReal p := by
      rw [Measure.prod_apply_symm hG]
      calc
        _ ≤ ∫⁻ _a, ENNReal.ofReal p ∂Measure.pi μ := by
          apply lintegral_mono_ae
          filter_upwards [htail] with a ha
          by_cases hmem : a ∈ E
          · have he : (fun ω : LogMoments.SignVector N => (ω, a)) ⁻¹' G = ∅ := by
              ext ω
              simp [G, hmem]
            rw [he, measure_empty]
            exact zero_le
          · have he : (fun ω : LogMoments.SignVector N => (ω, a)) ⁻¹' G =
                {ω | weightedRandomEnergy a s ω ≤ t} := by
              ext ω
              simp [G, F, D, hmem, complexEnergy_signed]
            rw [he, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
            exact ENNReal.ofReal_le_ofReal (ha hmem)
        _ = ENNReal.ofReal p := by simp
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob).trans_eq (ENNReal.toReal_ofReal hp)
  have heq : (Measure.pi μ).real D = ν.real (F ⁻¹' D) := by
    simp only [measureReal_def]
    rw [← hF.map_eq, Measure.map_apply hF.measurable hD]
  change (Measure.pi μ).real D ≤ _
  rw [heq]
  have hsub : F ⁻¹' D ⊆ G ∪ (Set.univ ×ˢ E) := by
    intro q hq
    by_cases hmem : q.2 ∈ E
    · exact Or.inr ⟨Set.mem_univ _, hmem⟩
    · exact Or.inl ⟨hq, fun h => hmem h.2⟩
  have h := (measureReal_mono (μ := ν) hsub).trans (measureReal_union_le _ _)
  have hEprod : ν.real (Set.univ ×ˢ E) = (Measure.pi μ).real E := by
    simp [ν, measureReal_prod_prod]
  rw [hEprod] at h
  linarith

/-- The unnormalized total coefficient energy has an explicit lower tail. -/
theorem measure_sum_norm_sq_le_half {N : ℕ}
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    {B : ℝ} (hB : 0 < B) (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B)
    (hmean : ∀ k, (∫ z, ‖z‖ ^ 2 ∂μ k) = 1) :
    (Measure.pi μ).real {a | (∑ k, ‖a k‖ ^ 2) ≤ (N + 1 : ℝ) / 2} ≤
      Real.exp (-(N + 1 : ℝ) / (2 * B ^ 4)) := by
  have hn : (0 : ℝ) < N + 1 := by positivity
  let w := fun _k : Fin (N + 1) => (N + 1 : ℝ)⁻¹
  have hw : ∑ k, w k = 1 := by simp [w, hn.ne']
  have hw2 : (∑ k, w k ^ 2) ≤ (N + 1 : ℝ)⁻¹ := by
    have heq : (∑ k, w k ^ 2) = (N + 1 : ℝ)⁻¹ := by
      simp only [w, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      field_simp
    exact heq.le
  have h := measure_weighted_amplitude_energy_le_half μ w hw hB (inv_pos.mpr hn)
    hw2 hbound hmean
  have he : {a : Fin (N + 1) → ℂ | (∑ k, w k * ‖a k‖ ^ 2) ≤ 1 / 2} =
      {a | (∑ k, ‖a k‖ ^ 2) ≤ (N + 1 : ℝ) / 2} := by
    ext a
    simp only [Set.mem_ofPred_eq, w, ← Finset.mul_sum]
    rw [← div_eq_inv_mul, div_le_iff₀ hn]
    constructor <;> intro h <;> nlinarith
  rw [he] at h
  convert h using 1
  congr 1
  field_simp

/-- The actual complex arc-energy lower tail for independent bounded,
centrally symmetric coefficients with second absolute moment one. -/
theorem complexEnergy_lower_tail_of_norm_le {N : ℕ}
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] {B : ℝ} (hB : 0 < B)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B)
    (hmean : ∀ k, (∫ z, ‖z‖ ^ 2 ∂μ k) = 1)
    (s : Set Angle) (hs : 0 < angularMeasure.real s) :
    (Measure.pi μ).real {a | complexEnergy a s ≤ (N + 1 : ℝ) * angularMeasure.real s / 4} ≤
      2 * Real.exp (-((N + 1 : ℝ) * angularMeasure.real s) / (32768 * B ^ 2)) +
        Real.exp (-(N + 1 : ℝ) / (2 * B ^ 4)) := by
  let E := {a : Fin (N + 1) → ℂ | (∑ k, ‖a k‖ ^ 2) ≤ (N + 1 : ℝ) / 2}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hp := measure_complexEnergy_le_of_sign_tail_except μ s
    (by positivity : 0 ≤ 2 * Real.exp (-((N + 1 : ℝ) * angularMeasure.real s) / (32768 * B ^ 2)))
    E hE (by
      filter_upwards [BoundedPolynomialSuprema.ae_coordinate_norm_le μ hbound] with a ha
      intro hnot
      have he : (N + 1 : ℝ) / 2 < ∑ k, ‖a k‖ ^ 2 := lt_of_not_ge hnot
      have hepos : 0 < ∑ k, ‖a k‖ ^ 2 := lt_trans (by positivity) he
      have htail := weightedRandomEnergy_lower_tail_of_norm_le a hB ha s hs hepos
      have hthreshold : (N + 1 : ℝ) * angularMeasure.real s / 4 ≤
          (∑ k, ‖a k‖ ^ 2) * angularMeasure.real s / 2 := by
        nlinarith [mul_le_mul_of_nonneg_right he.le hs.le]
      apply (measureReal_mono (fun _ hω => le_trans hω hthreshold)).trans htail |>.trans
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff₀ (by positivity : 0 < 16384 * B ^ 2)
        (by positivity : 0 < 32768 * B ^ 2)).mpr
      nlinarith [mul_nonneg (sq_nonneg B)
        (sub_nonneg.mpr (mul_le_mul_of_nonneg_right he.le hs.le))])
  exact hp.trans (add_le_add le_rfl (measure_sum_norm_sq_le_half μ hB hbound hmean))

end Erdos522.ArcEnergy

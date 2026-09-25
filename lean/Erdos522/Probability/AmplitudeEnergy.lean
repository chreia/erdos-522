/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SymmetricLogarithmicMoments
import Erdos522.Probability.Covariance.NormalizedValues
import Erdos522.Probability.RademacherLogarithmicConcentration
import Mathlib.Probability.Moments.SubGaussian

/-!
# Concentration of weighted amplitude energy

Independent bounded complex amplitudes with second moment one have weighted
energy close to one. Hoeffding's lemma retains the squared-weight sum, giving
the explicit annular radial normalization used in logarithmic estimates.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace Erdos522

/-- A bounded complex amplitude has a centered sub-Gaussian squared norm. -/
theorem hasSubgaussianMGF_centered_norm_sq (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {B : ℝ} (_hB : 0 ≤ B) (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
    (hmean : (∫ z, ‖z‖ ^ 2 ∂μ) = 1) (w : ℝ) :
    HasSubgaussianMGF (fun z : ℂ => w * (‖z‖ ^ 2 - 1))
      (NNReal.mk (w ^ 2 * B ^ 4 / 4) (by positivity)) μ := by
  have hb : ∀ᵐ z ∂μ, ‖z‖ ^ 2 ∈ Set.Icc 0 (B ^ 2) := by
    filter_upwards [hbound] with z hz
    exact ⟨sq_nonneg _, pow_le_pow_left₀ (norm_nonneg _) hz _⟩
  have h := (hasSubgaussianMGF_of_mem_Icc
    (continuous_norm.pow 2).measurable.aemeasurable hb).const_mul w
  simp only [Pi.pow_apply] at h
  rw [hmean] at h
  change HasSubgaussianMGF (fun z : ℂ => w * (‖z‖ ^ 2 - 1))
    (NNReal.mk (w ^ 2) (sq_nonneg w) * (‖B ^ 2 - 0‖₊ / 2) ^ 2) μ at h
  have heq : NNReal.mk (w ^ 2) (sq_nonneg w) * (‖B ^ 2 - 0‖₊ / 2) ^ 2 =
      (NNReal.mk (w ^ 2 * B ^ 4 / 4) (by positivity)) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mk, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div,
      NNReal.coe_ofNat, coe_nnnorm, sub_zero, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg B)]
    ring
  rw [heq] at h
  exact h

/-- Independent weighted amplitude energies have the exact Hoeffding proxy
`B⁴ Σw²/4`. -/
theorem hasSubgaussianMGF_weighted_amplitude_energy {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    (w : ι → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, ‖z‖ ^ 2 ∂μ k) = 1) :
    HasSubgaussianMGF (fun a : ι → ℂ => ∑ k, w k * (‖a k‖ ^ 2 - 1))
      (NNReal.mk (B ^ 4 * (∑ k, (w k) ^ 2) / 4) (by positivity)) (Measure.pi μ) := by
  let X := fun k (a : ι → ℂ) => w k * (‖a k‖ ^ 2 - 1)
  have hi : iIndepFun X (Measure.pi μ) :=
    iIndepFun_pi (fun k => (measurable_const.mul ((measurable_id.norm.pow_const 2).sub_const 1)).aemeasurable)
  have hX (k : ι) : HasSubgaussianMGF (X k)
      (NNReal.mk ((w k) ^ 2 * B ^ 4 / 4) (by positivity)) (Measure.pi μ) := by
    have h := hasSubgaussianMGF_centered_norm_sq (μ k) hB (hbound k) (hmean k) (w k)
    rw [← (measurePreserving_eval μ k).map_eq] at h
    exact HasSubgaussianMGF.of_map (Y := Function.eval k) (X := fun z => w k * (‖z‖ ^ 2 - 1))
      (measurable_pi_apply k).aemeasurable h
  have h := HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ) (fun k _ => hX k)
  have heq : (∑ k, ((NNReal.mk ((w k) ^ 2 * B ^ 4 / 4) (by positivity)) : ℝ≥0)) =
      (NNReal.mk (B ^ 4 * (∑ k, (w k) ^ 2) / 4) (by positivity)) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mk, NNReal.coe_sum]
    rw [← Finset.sum_div, ← Finset.sum_mul]
    ring
  rw [heq] at h
  exact h

/-- A normalized weighted energy has lower-tail probability at most
`exp(-1/(2B⁴Q))` whenever the squared weights sum to at most `Q`. -/
theorem measure_weighted_amplitude_energy_le_half {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    (w : ι → ℝ) (hw : ∑ k, w k = 1) {B Q : ℝ} (hB : 0 < B) (hQ : 0 < Q)
    (hweights : ∑ k, (w k) ^ 2 ≤ Q)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, ‖z‖ ^ 2 ∂μ k) = 1) :
    (Measure.pi μ).real {a : ι → ℂ | (∑ k, w k * ‖a k‖ ^ 2) ≤ 1 / 2} ≤
      Real.exp (-1 / (2 * B ^ 4 * Q)) := by
  have h := hasSubgaussianMGF_weighted_amplitude_energy μ w hB.le hbound hmean
  have hproxy : B ^ 4 * (∑ k, (w k) ^ 2) / 4 ≤ B ^ 4 * Q / 4 := by gcongr
  have hlarge : HasSubgaussianMGF (fun a : ι → ℂ => ∑ k, w k * (‖a k‖ ^ 2 - 1))
      (NNReal.mk (B ^ 4 * Q / 4) (by positivity)) (Measure.pi μ) := by
    refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans ?_⟩
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hproxy (sq_nonneg t)) (by norm_num)
  have htail := hlarge.neg.measure_ge_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hevent : {a : ι → ℂ | (∑ k, w k * ‖a k‖ ^ 2) ≤ 1 / 2} =
      {a | 1 / 2 ≤ -(∑ k, w k * (‖a k‖ ^ 2 - 1))} := by
    ext a
    simp only [Set.mem_ofPred_eq, mul_sub, mul_one, Finset.sum_sub_distrib, hw]
    constructor <;> intro h <;> linarith
  change (Measure.pi μ).real {a : ι → ℂ | 1 / 2 ≤ -(∑ k, w k * (‖a k‖ ^ 2 - 1))} ≤
    Real.exp (-(1 / 2 : ℝ) ^ 2 / (2 * (B ^ 4 * Q / 4))) at htail
  rw [hevent]
  convert htail using 1
  congr 1
  ring

/-- The normalized radial energy weight of coefficient `k`. -/
def radialEnergyWeight (N : ℕ) (r : ℝ) (k : Fin (N + 1)) : ℝ :=
  r ^ (2 * k.val) / radialVariance N r

theorem radialEnergyWeight_nonneg (N : ℕ) (r : ℝ) (k : Fin (N + 1)) :
    0 ≤ radialEnergyWeight N r k := by
  unfold radialEnergyWeight
  apply div_nonneg _ (radialVariance_pos N r).le
  rw [pow_mul]
  positivity

theorem sum_radialEnergyWeight (N : ℕ) (r : ℝ) : ∑ k, radialEnergyWeight N r k = 1 := by
  simp only [radialEnergyWeight]
  rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun k => r ^ (2 * k))]
  exact div_self (radialVariance_pos N r).ne'

/-- Each annular radial weight is at most `exp(6K)/N`. -/
theorem radialEnergyWeight_le (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N) (k : Fin (N + 1)) :
    radialEnergyWeight N r k ≤ Real.exp (6 * K) / N := by
  have h := pow_le_pow_left₀ (norm_nonneg (realValueCoefficient N r 1 k))
    (norm_realValueCoefficient_le N hN K r hK hNK hrl hru 1 (by norm_num) k) 2
  rw [norm_sq_realValueCoefficient N r 1 (by norm_num) k] at h
  have he : (Real.exp (3 * K) / Real.sqrt N) ^ 2 = Real.exp (6 * K) / N := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg N), pow_two, ← Real.exp_add]
    congr 2
    ring
  exact h.trans_eq he

/-- Normalization converts the largest radial-weight bound to a squared-weight bound. -/
theorem sum_sq_radialEnergyWeight_le (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N) :
    (∑ k, radialEnergyWeight N r k ^ 2) ≤ Real.exp (6 * K) / N := by
  calc
    _ ≤ ∑ k, (Real.exp (6 * K) / N) * radialEnergyWeight N r k := by
      apply Finset.sum_le_sum
      intro k _
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (radialEnergyWeight_le N hN K r hK hNK hrl hru k)
        (radialEnergyWeight_nonneg N r k)
    _ = _ := by rw [← Finset.mul_sum, sum_radialEnergyWeight, mul_one]

/-- The normalized radial amplitude energy has the manuscript's explicit
annular lower-tail exponent. -/
theorem measure_radial_amplitude_energy_le_half (N : ℕ) (hN : 0 < N)
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    (K r : ℝ) (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, ‖z‖ ^ 2 ∂μ k) = 1) :
    (Measure.pi μ).real {a : Fin (N + 1) → ℂ |
      (∑ k, radialEnergyWeight N r k * ‖a k‖ ^ 2) ≤ 1 / 2} ≤
        Real.exp (-(N : ℝ) / (2 * B ^ 4 * Real.exp (6 * K))) := by
  have h := measure_weighted_amplitude_energy_le_half μ (radialEnergyWeight N r)
    (sum_radialEnergyWeight N r) hB
    (div_pos (Real.exp_pos _) (by exact_mod_cast hN))
    (sum_sq_radialEnergyWeight_le N hN K r hK hNK hrl hru) hbound hmean
  convert h using 1
  congr 1
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- Bounded amplitudes bound every normalized nonnegative weighted energy
by the square of the amplitude bound. -/
theorem ae_weighted_amplitude_energy_le {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    (w : ι → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hw : ∑ k, w k = 1) {B : ℝ}
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) :
    ∀ᵐ a ∂Measure.pi μ, (∑ k, w k * ‖a k‖ ^ 2) ≤ B ^ 2 := by
  have hb : ∀ᵐ a ∂Measure.pi μ, ∀ k, ‖a k‖ ≤ B := by
    apply ae_all_iff.mpr
    intro k
    exact (measurePreserving_eval μ k).quasiMeasurePreserving.ae (hbound k)
  filter_upwards [hb] with a ha
  calc
    _ ≤ ∑ k, w k * B ^ 2 := Finset.sum_le_sum (fun k _ =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (ha k) _) (hw0 k))
    _ = _ := by rw [← Finset.sum_mul, hw, one_mul]

/-- The radial Fourier coefficient energy is exactly the normalized radial weight. -/
theorem norm_sq_normalizedRadialCoefficients (N : ℕ) (r : ℝ) (k : Fin (N + 1)) :
    ‖normalizedRadialCoefficients N r k‖ ^ 2 = radialEnergyWeight N r k := by
  simp only [normalizedRadialCoefficients, radialEnergyWeight, norm_div, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (radialSigma_pos N r), div_pow,
    ← pow_mul, Nat.mul_comm _ 2, even_two_mul, Even.pow_abs, radialSigma_sq]

/-- The exceptional amplitude event for a normalized annular polynomial has
the exact exponentially small probability used in the symmetric model. -/
theorem measure_compl_radial_coefficientEnergyEvent_le (N : ℕ) (hN : 0 < N)
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    (K r : ℝ) (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ ≤ B) (hmean : ∀ k, (∫ z, ‖z‖ ^ 2 ∂μ k) = 1) :
    (Measure.pi μ).real (coefficientEnergyEvent (normalizedRadialCoefficients N r) B)ᶜ ≤
      Real.exp (-(N : ℝ) / (2 * B ^ 4 * Real.exp (6 * K))) := by
  have hupper := ae_weighted_amplitude_energy_le μ (radialEnergyWeight N r)
    (radialEnergyWeight_nonneg N r) (sum_radialEnergyWeight N r) hbound
  have hsub : (coefficientEnergyEvent (normalizedRadialCoefficients N r) B)ᶜ ≤ᵐ[Measure.pi μ]
      {a | (∑ k, radialEnergyWeight N r k * ‖a k‖ ^ 2) ≤ 1 / 2} := by
    filter_upwards [hupper] with a ha hbad
    have heq : (∑ k, ‖normalizedRadialCoefficients N r k * a k‖ ^ 2) =
        ∑ k, radialEnergyWeight N r k * ‖a k‖ ^ 2 := by
      simp only [norm_mul, mul_pow, norm_sq_normalizedRadialCoefficients]
    change ¬ (1 / 2 ≤ ∑ k, ‖normalizedRadialCoefficients N r k * a k‖ ^ 2 ∧
      (∑ k, ‖normalizedRadialCoefficients N r k * a k‖ ^ 2) ≤ B ^ 2) at hbad
    rw [heq] at hbad
    exact (lt_of_not_ge (fun hlo => hbad ⟨hlo, ha⟩)).le
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans
    (measure_radial_amplitude_energy_le_half N hN μ K r hK hNK hrl hru hB hbound hmean)

end Erdos522

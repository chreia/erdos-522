/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.WeightedArcEnergy
import Erdos522.Probability.SymmetricSignRepresentation
import Erdos522.Probability.SteinhausLaw

/-!
# Arc energy under centrally symmetric complex laws

Independent signs preserve each centrally symmetric coefficient law. Averaging
the complex-amplitude Hanson--Wright estimate therefore gives an arc-energy
bound under the original coefficient law. Unit-modulus coefficients have a
deterministic Gram trace, in particular for the Steinhaus model.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Erdos522.ArcEnergy

/-- The Fourier polynomial of a complex coefficient vector. -/
def complexFourierSum {N : ℕ} (a : Fin (N + 1) → ℂ) (θ : Angle) : ℂ :=
  ∑ k, a k * fourier (k : ℤ) θ

/-- Angular energy under the original complex coefficient law. -/
def complexEnergy {N : ℕ} (a : Fin (N + 1) → ℂ) (s : Set Angle) : ℝ :=
  ∫ θ in s, ‖complexFourierSum a θ‖ ^ 2 ∂angularMeasure

theorem measurable_complexEnergy (N : ℕ) (s : Set Angle) :
    Measurable (fun a : Fin (N + 1) → ℂ => complexEnergy a s) := by
  have hf : Continuous (fun q : (Fin (N + 1) → ℂ) × Angle => ‖complexFourierSum q.1 q.2‖ ^ 2) := by
    unfold complexFourierSum
    fun_prop
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

theorem complexEnergy_signed {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : LogMoments.SignVector N) (s : Set Angle) :
    complexEnergy (fun k => LogMoments.sign (ω k) * a k) s = weightedRandomEnergy a s ω := by
  unfold complexEnergy weightedRandomEnergy weightedEnergy
  congr 1
  ext θ
  congr 2
  simp only [complexFourierSum, weightedFourierSum, Complex.real_smul,
    LogMoments.ofReal_realSign, mul_assoc]

/-- Conditioning on the amplitudes transfers any uniform sign-energy bound
to the original product of centrally symmetric laws. -/
theorem measure_complexEnergy_le_of_sign_tail {N : ℕ}
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] (s : Set Angle) {t p : ℝ} (hp : 0 ≤ p)
    (htail : ∀ᵐ a ∂Measure.pi μ,
      (LogMoments.signMeasure N).real {ω | weightedRandomEnergy a s ω ≤ t} ≤ p) :
    (Measure.pi μ).real {a | complexEnergy a s ≤ t} ≤ p := by
  let E := {a : Fin (N + 1) → ℂ | complexEnergy a s ≤ t}
  have hE : MeasurableSet E := measurableSet_le (measurable_complexEnergy N s) measurable_const
  have hF := measurePreserving_random_coordinate_signs μ (LogMoments.signMeasure N)
  have hprob : Measure.pi μ E ≤ ENNReal.ofReal p := by
    rw [← hF.map_eq, Measure.map_apply hF.measurable hE,
      Measure.prod_apply_symm (hF.measurable hE)]
    calc
      _ ≤ ∫⁻ _a, ENNReal.ofReal p ∂Measure.pi μ := by
        apply lintegral_mono_ae
        filter_upwards [htail] with a ha
        have he : (fun ω : LogMoments.SignVector N => (ω, a)) ⁻¹'
            ((fun q : LogMoments.SignVector N × (Fin (N + 1) → ℂ) =>
              fun k => LogMoments.sign (q.1 k) * q.2 k) ⁻¹' E) =
            {ω | weightedRandomEnergy a s ω ≤ t} := by
          ext ω
          simp only [Set.mem_preimage, E, Set.mem_ofPred_eq, complexEnergy_signed]
        rw [he, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
        exact ENNReal.ofReal_le_ofReal ha
      _ = ENNReal.ofReal p := by simp
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob).trans_eq (ENNReal.toReal_ofReal hp)

/-- Independent centrally symmetric unit-modulus coefficients have the same
arc-energy lower tail as independent signs. -/
theorem complexEnergy_lower_tail_of_norm_eq_one {N : ℕ}
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] (hnorm : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ = 1)
    (s : Set Angle) (hs : 0 < angularMeasure.real s) :
    (Measure.pi μ).real {a | complexEnergy a s ≤ (N + 1 : ℝ) * angularMeasure.real s / 2} ≤
      2 * Real.exp (-((N + 1 : ℝ) * angularMeasure.real s) / 16384) := by
  apply measure_complexEnergy_le_of_sign_tail μ s (by positivity)
  have hall : ∀ᵐ a ∂Measure.pi μ, ∀ k, ‖a k‖ = 1 := by
    apply ae_all_iff.mpr
    intro k
    exact (measurePreserving_eval μ k).quasiMeasurePreserving.ae (hnorm k)
  filter_upwards [hall] with a ha
  have he : ∑ k, ‖a k‖ ^ 2 = (N + 1 : ℝ) := by simp [ha]
  have h := weightedRandomEnergy_lower_tail a (fun k => (ha k).le) s hs
    (by rw [he]; positivity)
  simpa only [he] using h

/-- The Steinhaus arc-energy lower tail under its actual complex product law. -/
theorem steinhaus_complexEnergy_lower_tail (N : ℕ) (s : Set Angle)
    (hs : 0 < angularMeasure.real s) :
    (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real
      {a | complexEnergy a s ≤ (N + 1 : ℝ) * angularMeasure.real s / 2} ≤
        2 * Real.exp (-((N + 1 : ℝ) * angularMeasure.real s) / 16384) :=
  complexEnergy_lower_tail_of_norm_eq_one _ (fun _ => ae_norm_steinhaus_eq_one) s hs

/-- At the logarithmic arc width, symmetric unit-modulus laws have failure
at most `2N⁻¹⁶`. -/
theorem complexEnergy_arc_lower_tail_of_norm_eq_one (N : ℕ) (hN : 2 ≤ N)
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] (hnorm : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ = 1)
    (θ : Angle) (hh : arcScale * Real.log N / N ≤ Real.pi) :
    (Measure.pi μ).real
      {a | complexEnergy a (arc θ (arcScale * Real.log N / N)) ≤
        (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2} ≤ 2 / (N : ℝ) ^ 16 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlog := Real.log_pos hN1
  have hscale : 0 < arcScale := by unfold arcScale; positivity
  have hwidth : 0 < arcScale * Real.log N / N := by positivity
  have hmass := angularMeasure_arc θ hwidth.le hh
  have hmpos : 0 < angularMeasure.real (arc θ (arcScale * Real.log N / N)) := by
    rw [hmass]
    positivity
  have htail := complexEnergy_lower_tail_of_norm_eq_one μ hnorm
    (arc θ (arcScale * Real.log N / N)) hmpos
  rw [hmass] at htail
  refine htail.trans ?_
  have htrace : (262144 : ℝ) * Real.log N ≤
      (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) := by
    unfold arcScale
    field_simp
    nlinarith [Real.pi_pos]
  calc
    2 * Real.exp (-((N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi)) / 16384)
        ≤ 2 * Real.exp (-(16 * Real.log N)) := by
          gcongr
          linarith
    _ = 2 / (N : ℝ) ^ 16 := by
      rw [Real.exp_neg, show (16 : ℝ) = (16 : ℕ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hN0, div_eq_mul_inv]

/-- A finite angular cover simultaneously supplies large complex polynomial
values under the original symmetric unit-modulus coefficient law. -/
theorem simultaneous_complex_large_values (N : ℕ) (hN : 2 ≤ N)
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] (hnorm : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ = 1)
    {ι : Type*} [Fintype ι] (θ : ι → Angle) (hcard : Fintype.card ι ≤ 8 * N)
    (hh : arcScale * Real.log N / N ≤ Real.pi) :
    (Measure.pi μ).real {a | ∃ i, ∀ t ∈ arc (θ i) (arcScale * Real.log N / N),
      ‖complexFourierSum a t‖ ^ 2 ≤ (N + 1 : ℝ) / 2} ≤ 1 / (N : ℝ) ^ 3 := by
  have hsub : {a : Fin (N + 1) → ℂ | ∃ i, ∀ t ∈ arc (θ i) (arcScale * Real.log N / N),
      ‖complexFourierSum a t‖ ^ 2 ≤ (N + 1 : ℝ) / 2} ⊆
      ⋃ i, {a | complexEnergy a (arc (θ i) (arcScale * Real.log N / N)) ≤
        (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2} := by
    intro a ⟨i, hi⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hwidth : 0 ≤ arcScale * Real.log N / N := by
      unfold arcScale
      positivity
    have hm := angularMeasure_arc (θ i) hwidth hh
    have hc : Continuous (fun θ : Angle => ‖complexFourierSum a θ‖ ^ 2) := by
      unfold complexFourierSum
      fun_prop
    have hint := setIntegral_mono_on (μ := angularMeasure)
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).integrableOn
      (integrableOn_const (by finiteness)) (measurableSet_arc _ _) hi
    rw [setIntegral_const, smul_eq_mul, hm] at hint
    change complexEnergy _ _ ≤ _
    unfold complexEnergy
    convert hint using 1
    ring
  have hp := (measureReal_mono (μ := Measure.pi μ) hsub).trans (measureReal_iUnion_fintype_le _)
  have hsum : (∑ i, (Measure.pi μ).real
      {a | complexEnergy a (arc (θ i) (arcScale * Real.log N / N)) ≤
        (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2}) ≤
      (Fintype.card ι : ℝ) * (2 / (N : ℝ) ^ 16) := by
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset ι))
      (fun i _ => complexEnergy_arc_lower_tail_of_norm_eq_one N hN μ hnorm (θ i) hh)
  exact (hp.trans hsum).trans (arc_family_failure_budget hN hcard)

end Erdos522.ArcEnergy

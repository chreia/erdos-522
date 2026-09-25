/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ExponentialLogarithmicDerivative
import Erdos522.Analysis.WeakLogarithmicQuotient
import Erdos522.Analysis.ExponentialGeometricRestriction
import Mathlib.Data.Finset.Max

/-!
# Geometric-mean restriction of harmonic exponential polynomials

Frequency elimination reduces the number of terms while preserving the same
measurable set. A bounded spectrum is controlled by its logarithmic potential;
a wide spectrum is reduced by differential pruning at a diameter endpoint.
-/

noncomputable section

open Complex MeasureTheory Metric Set
open scoped BigOperators

namespace Erdos522

/-- A universal constant accommodating bounded spectra and one pruning step. -/
def harmonicRestrictionConstant : ℝ := Real.exp 2000 + 2 * Real.exp 1 * 8192

theorem harmonicRestrictionConstant_pos : 0 < harmonicRestrictionConstant := by
  unfold harmonicRestrictionConstant
  positivity

theorem exp_le_harmonicRestrictionConstant : Real.exp 2000 ≤ harmonicRestrictionConstant := by
  unfold harmonicRestrictionConstant
  have h : 0 ≤ 2 * Real.exp 1 * 8192 := by positivity
  linarith

theorem pruning_factor_le_harmonicRestrictionConstant :
    2 * Real.exp 1 * 8192 ≤ harmonicRestrictionConstant := by
  unfold harmonicRestrictionConstant
  linarith [Real.exp_pos 2000]

/-- A finite nonempty spectrum has two points realizing its diameter. -/
theorem exists_spectral_diameter_pair {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (ζ : ι → ℂ) :
    ∃ a ∈ s, ∃ b ∈ s, ∀ i ∈ s, ∀ j ∈ s, ‖ζ j - ζ i‖ ≤ ‖ζ b - ζ a‖ := by
  obtain ⟨p, hp, hmax⟩ := (s.product s).exists_max_image
    (fun p : ι × ι ↦ ‖ζ p.2 - ζ p.1‖) (hs.product hs)
  exact ⟨p.1, (Finset.mem_product.mp hp).1, p.2, (Finset.mem_product.mp hp).2,
    fun i hi j hj ↦ hmax (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩)⟩

/-- An imaginary spectral translation preserves the geometric mean on the real line. -/
theorem geometricMean_complexExponentialSum_spectral_shift {ι : Type*}
    (μ : Measure ℝ) (s : Finset ι) (c ζ : ι → ℂ) (a : ℂ) (ha : a.re = 0) :
    geometricMean μ (fun x : ℝ ↦ complexExponentialSum s c ζ (x : ℂ)) =
      geometricMean μ (fun x : ℝ ↦ complexExponentialSum s c (fun j ↦ ζ j - a) (x : ℂ)) := by
  unfold geometricMean
  simp_rw [norm_complexExponentialSum_spectral_shift s c ζ a ha]

/-- A singleton imaginary spectrum has constant modulus on the real line. -/
theorem norm_complexExponentialSum_singleton_imaginary {ι : Type*} [DecidableEq ι]
    (a : ι) (c ζ : ι → ℂ) (ha : (ζ a).re = 0) (x : ℝ) :
    ‖complexExponentialSum {a} c ζ (x : ℂ)‖ = ‖c a‖ := by
  simp only [complexExponentialSum, Finset.sum_singleton, norm_mul, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, ha, zero_mul, mul_zero,
    sub_zero, Real.exp_zero, mul_one]

/-- The geometric mean of a singleton imaginary spectrum equals its coefficient modulus. -/
theorem geometricMean_complexExponentialSum_singleton {ι : Type*} [DecidableEq ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ] [NeZero μ]
    (a : ι) (c ζ : ι → ℂ) (ha : (ζ a).re = 0) (hc : c a ≠ 0) :
    geometricMean μ (fun x : ℝ ↦ complexExponentialSum {a} c ζ (x : ℂ)) = ‖c a‖ := by
  unfold geometricMean
  simp_rw [norm_complexExponentialSum_singleton_imaginary a c ζ ha]
  rw [average_const, Real.exp_log (norm_pos_iff.mpr hc)]

private theorem geometricMean_exponentialPruning_le_of_integrable {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ) (a : ℂ)
    (hne : complexExponentialSum s c ζ ≠ 0) {ρ : ℝ}
    (hρ : 0 < ρ) (hmρ : (s.card : ℝ) ≤ ρ) (hζ : ∀ j ∈ s, ‖ζ j - a‖ ≤ ρ)
    (E : Set ℝ) (hE : MeasurableSet E) (hsub : E ⊆ Icc (-1 / 2) (1 / 2))
    (hpos : 0 < volume.real E) [IsFiniteMeasure (volume.restrict E)]
    (hplog : Integrable (fun x : ℝ ↦ Real.log ‖complexExponentialSum s c ζ (x : ℂ)‖)
      (volume.restrict E))
    (hqlog : Integrable (fun x : ℝ ↦ Real.log ‖exponentialPruning s c ζ a ρ (x : ℂ)‖)
      (volume.restrict E))
    (hpzero : ∀ᵐ (x : ℝ) ∂volume.restrict E, complexExponentialSum s c ζ (x : ℂ) ≠ 0)
    (hqzero : ∀ᵐ (x : ℝ) ∂volume.restrict E, exponentialPruning s c ζ a ρ (x : ℂ) ≠ 0) :
    geometricMean (volume.restrict E) (fun x : ℝ ↦ exponentialPruning s c ζ a ρ (x : ℂ)) ≤
      (Real.exp 1 * 8192 / volume.real E) *
        geometricMean (volume.restrict E) (fun x : ℝ ↦ complexExponentialSum s c ζ (x : ℂ)) := by
  have hpmeas : Measurable (fun x : ℝ ↦ complexExponentialSum s c ζ (x : ℂ)) :=
    (analyticOnNhd_complexExponentialSum s c ζ).continuous.measurable.comp
      Complex.continuous_ofReal.measurable
  have hqmeas : Measurable (fun x : ℝ ↦ exponentialPruning s c ζ a ρ (x : ℂ)) := by
    simp_rw [exponentialPruning_eq_sum]
    exact (analyticOnNhd_complexExponentialSum _ _ _).continuous.measurable.comp
      Complex.continuous_ofReal.measurable
  have hα : volume.real E ≤ 1 := by
    have h := measureReal_mono (μ := volume) hsub (by simp)
    norm_num at h
    exact h
  have h := geometricMean_quotient_bound (volume.restrict E)
    (fun x : ℝ ↦ complexExponentialSum s c ζ (x : ℂ))
    (fun x : ℝ ↦ exponentialPruning s c ζ a ρ (x : ℂ))
    hpmeas hqmeas hplog hqlog hpzero hqzero (by simpa using hpos)
    (A := 8192) (by simpa using (hα.trans (by norm_num : (1 : ℝ) ≤ 8192))) (by
      intro u hu
      rw [Measure.restrict_apply' hE]
      refine (measure_mono ?_).trans
        (measure_exponentialPruning_quotient_levelset_le s hs c ζ a hne hρ hmρ hζ hu)
      intro x hx
      refine ⟨hsub hx.2, ?_, hx.1⟩
      intro hz
      have hbad := hx.1
      change u ≤ ‖exponentialPruning s c ζ a ρ (x : ℂ)‖ /
        ‖complexExponentialSum s c ζ (x : ℂ)‖ at hbad
      rw [hz, norm_zero, div_zero] at hbad
      linarith)
  simpa using h

/-- Differential pruning costs one inverse-mass factor in the geometric mean. -/
theorem geometricMean_exponentialPruning_le {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ) (a : ℂ)
    (hne : complexExponentialSum s c ζ ≠ 0) {ρ : ℝ}
    (hqne : exponentialPruning s c ζ a ρ ≠ 0)
    (hρ : 0 < ρ) (hmρ : (s.card : ℝ) ≤ ρ) (hζ : ∀ j ∈ s, ‖ζ j - a‖ ≤ ρ)
    (E : Set ℝ) (hE : MeasurableSet E) (hsub : E ⊆ Icc (-1 / 2) (1 / 2))
    (hpos : 0 < volume.real E) [IsFiniteMeasure (volume.restrict E)] :
    geometricMean (volume.restrict E) (fun x : ℝ ↦ exponentialPruning s c ζ a ρ (x : ℂ)) ≤
      (Real.exp 1 * 8192 / volume.real E) *
        geometricMean (volume.restrict E) (fun x : ℝ ↦ complexExponentialSum s c ζ (x : ℂ)) := by
  let d := fun j ↦ c j * (ζ j - a) / (ρ : ℂ)
  have hdne : complexExponentialSum s d ζ ≠ 0 := by
    intro h
    apply hqne
    funext z
    rw [exponentialPruning_eq_sum]
    exact congrFun h z
  apply geometricMean_exponentialPruning_le_of_integrable s hs c ζ a hne hρ hmρ hζ E hE hsub hpos
  · exact integrableOn_log_norm_complexExponentialSum s c ζ hne E hE (by simpa only [neg_div] using hsub)
  · simpa only [exponentialPruning_eq_sum, d, IntegrableOn] using
      integrableOn_log_norm_complexExponentialSum s d ζ hdne E hE (by simpa only [neg_div] using hsub)
  · exact ae_complexExponentialSum_ne_zero s c ζ hne E hE (by simpa only [neg_div] using hsub)
  · simpa only [exponentialPruning_eq_sum] using
      ae_complexExponentialSum_ne_zero s d ζ hdne E hE (by simpa only [neg_div] using hsub)

/-- An exponential polynomial with purely imaginary frequencies is controlled
    by its geometric mean on any positive-measure subset of the unit interval.
    The exponent is the number of terms minus one. -/
theorem norm_complexExponentialSum_le_geometricMean_of_imaginary_spectrum {ι : Type*}
    (s : Finset ι) (c ζ : ι → ℂ) (hζ : ∀ j ∈ s, (ζ j).re = 0)
    (E : Set ℝ) (hE : MeasurableSet E) (hsub : E ⊆ Icc (-1 / 2) (1 / 2))
    (hpos : 0 < volume.real E) (x : ℝ) (hx : |x| ≤ 1 / 2) :
    ‖complexExponentialSum s c ζ (x : ℂ)‖ ≤
      (harmonicRestrictionConstant / volume.real E) ^ (s.card - 1) *
        geometricMean (volume.restrict E) (fun t : ℝ ↦ complexExponentialSum s c ζ (t : ℂ)) := by
  classical
  have hEfinite : volume E ≠ ⊤ := ne_top_of_le_ne_top (by simp) (measure_mono hsub)
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hEfinite
  let : NeZero (volume.restrict E) := ⟨by
    intro h
    have hzero : volume.real E = 0 := by
      have := congrArg (fun μ : Measure ℝ ↦ μ.real univ) h
      simpa using this
    linarith⟩
  have hbase : 0 ≤ harmonicRestrictionConstant / volume.real E :=
    div_nonneg harmonicRestrictionConstant_pos.le hpos.le
  revert c ζ
  refine Finset.strongInductionOn s ?_
  intro s ih c ζ hζ
  by_cases hpx : complexExponentialSum s c ζ (x : ℂ) = 0
  · rw [hpx, norm_zero]
    exact mul_nonneg (pow_nonneg hbase _) (geometricMean_pos _ _).le
  have hne : complexExponentialSum s c ζ ≠ 0 := fun h ↦ hpx (congrFun h x)
  have hs : s.Nonempty := by
    by_contra h
    have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he, complexExponentialSum] at hpx
  by_cases hs₂ : 2 ≤ s.card
  · obtain ⟨a, ha, b, hb, hdiam⟩ := exists_spectral_diameter_pair s hs ζ
    let ρ : ℝ := ‖ζ b - ζ a‖
    by_cases hsmall : ρ ≤ (s.card : ℝ)
    · have hshift : complexExponentialSum s c (fun j ↦ ζ j - ζ a) ≠ 0 := by
        intro h
        apply hne
        funext z
        rw [complexExponentialSum_spectral_shift s c ζ (ζ a), h]
        simp
      have hbounded := norm_complexExponentialSum_le_geometricMean_of_bounded_spectrum
        s hs₂ c (fun j ↦ ζ j - ζ a) hshift (norm_nonneg _) hsmall
        (fun j hj ↦ hdiam a ha j hj) E hE (by simpa only [neg_div] using hsub) hpos x hx
      rw [← norm_complexExponentialSum_spectral_shift s c ζ (ζ a) (hζ a ha),
        ← geometricMean_complexExponentialSum_spectral_shift (volume.restrict E)
          s c ζ (ζ a) (hζ a ha)] at hbounded
      refine hbounded.trans (mul_le_mul_of_nonneg_right ?_ (geometricMean_pos _ _).le)
      exact pow_le_pow_left₀ (div_nonneg (Real.exp_pos _).le hpos.le)
        (div_le_div_of_nonneg_right exp_le_harmonicRestrictionConstant hpos.le) _
    · have hlarge : (s.card : ℝ) < ρ := lt_of_not_ge hsmall
      have hρ : 0 < ρ := (Nat.cast_nonneg _).trans_lt hlarge
      obtain ⟨j, hj, hkeep⟩ : ∃ j ∈ s,
          ‖complexExponentialSum s c ζ (x : ℂ)‖ / 2 ≤
            ‖exponentialPruning s c ζ (ζ j) ρ (x : ℂ)‖ := by
        rcases exists_pruned_norm_ge_half s c ζ hρ (show ‖ζ b - ζ a‖ = ρ from rfl) x with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      have hqne : exponentialPruning s c ζ (ζ j) ρ ≠ 0 := by
        intro h
        have hzero := congrFun h x
        simp only [Pi.zero_apply] at hzero
        rw [hzero, norm_zero] at hkeep
        have hn : 0 < ‖complexExponentialSum s c ζ (x : ℂ)‖ := norm_pos_iff.mpr hpx
        linarith
      let d := fun k ↦ c k * (ζ k - ζ j) / (ρ : ℂ)
      have hi := ih (s.erase j) (Finset.erase_ssubset hj) d ζ
        (fun k hk ↦ hζ k (Finset.mem_of_mem_erase hk))
      have hg := geometricMean_exponentialPruning_le s hs c ζ (ζ j) hne hqne
        hρ hlarge.le (fun k hk ↦ hdiam j hj k hk) E hE hsub hpos
      have hi' : ‖exponentialPruning s c ζ (ζ j) ρ (x : ℂ)‖ ≤
          (harmonicRestrictionConstant / volume.real E) ^ ((s.erase j).card - 1) *
            geometricMean (volume.restrict E)
              (fun t : ℝ ↦ exponentialPruning s c ζ (ζ j) ρ (t : ℂ)) := by
        simpa only [exponentialPruning_eq_erase] using hi
      have hexponent : s.card - 1 = ((s.erase j).card - 1) + 1 := by
        rw [Finset.card_erase_of_mem hj]
        omega
      have hfactor : 2 * (Real.exp 1 * 8192 / volume.real E) ≤
          harmonicRestrictionConstant / volume.real E := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right
          (by simpa only [mul_assoc] using pruning_factor_le_harmonicRestrictionConstant) hpos.le
      calc
        _ ≤ 2 * ‖exponentialPruning s c ζ (ζ j) ρ (x : ℂ)‖ := by linarith
        _ ≤ 2 * ((harmonicRestrictionConstant / volume.real E) ^ ((s.erase j).card - 1) *
            geometricMean (volume.restrict E)
              (fun t : ℝ ↦ exponentialPruning s c ζ (ζ j) ρ (t : ℂ))) := by gcongr
        _ ≤ 2 * ((harmonicRestrictionConstant / volume.real E) ^ ((s.erase j).card - 1) *
            ((Real.exp 1 * 8192 / volume.real E) * geometricMean (volume.restrict E)
              (fun t : ℝ ↦ complexExponentialSum s c ζ (t : ℂ)))) := by gcongr
        _ = ((harmonicRestrictionConstant / volume.real E) ^ ((s.erase j).card - 1) *
            (2 * (Real.exp 1 * 8192 / volume.real E))) * geometricMean (volume.restrict E)
              (fun t : ℝ ↦ complexExponentialSum s c ζ (t : ℂ)) := by ring
        _ ≤ ((harmonicRestrictionConstant / volume.real E) ^ ((s.erase j).card - 1) *
            (harmonicRestrictionConstant / volume.real E)) * geometricMean (volume.restrict E)
              (fun t : ℝ ↦ complexExponentialSum s c ζ (t : ℂ)) := by
            gcongr
            exact (geometricMean_pos _ _).le
        _ = _ := by rw [hexponent, pow_succ]
  · have hcard : s.card = 1 := by have := Finset.one_le_card.mpr hs; omega
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    have ha : (ζ a).re = 0 := hζ a (Finset.mem_singleton_self _)
    have hc : c a ≠ 0 := by
      intro h
      simp [complexExponentialSum, h] at hpx
    rw [norm_complexExponentialSum_singleton_imaginary a c ζ ha,
      geometricMean_complexExponentialSum_singleton (volume.restrict E) a c ζ ha hc]
    simp

end Erdos522

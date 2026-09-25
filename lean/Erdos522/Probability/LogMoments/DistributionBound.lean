/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.SpreadingConstants
import Erdos522.Probability.LogMoments.LargeSetEnergy
import Erdos522.Probability.LogMoments.LogarithmicTails

/-!
# Coefficient-uniform Fourier distribution bounds

The harmonic restriction inequality on measurable parts of real intervals
combines with the actual Rademacher spreading construction and the finite
measure-growth recurrence. The resulting restricted-energy bound has the
sixth-power logarithmic scale.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Erdos522.LogMoments

/-- A measurable-subset `L²` restriction bound for harmonic exponential
polynomials. The real frequencies are arbitrary and the constant is uniform
in the number of terms, the partition, and the measurable subset. -/
def HarmonicL2Restriction (C : ℝ) : Prop :=
  ∀ (m : ℕ) (ξ : Fin m → ℝ), Function.Injective ξ → ∀ (q : ℕ), 0 < q →
    ∀ (γ : ℝ), 0 < γ → γ ≤ 1 → ∀ (i : Fin q) (s : Set ℝ),
    MeasurableSet s → s ⊆ unitIntervalCell i →
    γ * volume.real (unitIntervalCell i) ≤ volume.real s →
    ∀ P : ℝ → ℂ, P ∈ exponentialSpan (Set.range ξ) →
      (∫ x in unitIntervalCell i, ‖P x‖ ^ 2) ≤ (C / γ) ^ (2 * m + 1) * ∫ x in s, ‖P x‖ ^ 2

/-- The harmonic restriction estimate remains valid at any larger frequency
order and uses the same normalization under the real Fourier law. -/
theorem HarmonicL2Restriction.at_order {C : ℝ} (hR : HarmonicL2Restriction C)
    (hC : 1 ≤ C) {m n : ℕ} (hmn : m ≤ n) (ξ : Fin m → ℝ) (hξ : Function.Injective ξ)
    {q : ℕ} (hq : 0 < q) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (i : Fin q) (s : Set ℝ) (hs : MeasurableSet s) (hsub : s ⊆ unitIntervalCell i)
    (hden : γ * unitIntervalMeasure.real (unitIntervalCell i) ≤ unitIntervalMeasure.real s)
    (P : ℝ → ℂ) (hP : P ∈ exponentialSpan (Set.range ξ)) :
    (∫ x in unitIntervalCell i, ‖P x‖ ^ 2 ∂unitIntervalMeasure) ≤
      (C / γ) ^ (2 * n + 1) * ∫ x in s, ‖P x‖ ^ 2 ∂unitIntervalMeasure := by
  apply unitInterval_restriction_of_volume hq i s hs hsub P _ hden
  intro hd
  refine (hR m ξ hξ q hq γ hγ hγ1 i s hs hsub hd P hP).trans ?_
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun _ => sq_nonneg _)
  exact pow_le_pow_right₀ ((le_div_iff₀ hγ).mpr (by linarith)) (by omega)

/-- A multiplicative energy inequality gives the corresponding additive
logarithmic loss. -/
theorem neg_log_le_neg_log_add_of_mul_bound {x y A : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hA : 0 < A) (h : y ≤ A * x) :
    -Real.log x ≤ -Real.log y + Real.log A := by
  have hl := Real.log_le_log hy h
  rw [Real.log_mul hA.ne' hx.ne'] at hl
  linarith

/-- Sets of mass at least `9/10` have logarithmic energy loss at most `log 2`. -/
theorem neg_log_restricted_fourier_energy_le_log_two {N : ℕ}
    (a : Fin (N + 1) → ℂ) (ha : ∑ k, ‖a k‖ ^ 2 = 1)
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hlarge : 9 / 10 ≤ (fourierMeasure N).real E) :
    -(Real.log (∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N)) ≤ Real.log 2 := by
  have h := coefficient_energy_le_twice_restricted_energy a E hE hlarge
  rw [ha] at h
  have he : (1 / 2 : ℝ) ≤ ∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N := by linarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) he
  rw [one_div, Real.log_inv] at hl
  linarith

/-- The optimized recurrence coefficient for the finite Fourier distribution. -/
def fourierDistributionConstant (C : ℝ) : ℝ :=
  20480 * Real.exp 1 * spreadingRecurrenceConstant C / spreadingIncrementConstant

theorem fourierDistributionConstant_pos {C : ℝ} (hC : 1 ≤ C) :
    0 < fourierDistributionConstant C := by
  have := spreadingRecurrenceConstant_pos hC
  have := spreadingIncrementConstant_pos
  unfold fourierDistributionConstant
  positivity

/-- The actual finite Rademacher Fourier sum has a coefficient-uniform
sixth-power logarithmic restricted-energy bound, given the one-cell harmonic
restriction theorem. -/
theorem neg_log_restricted_fourier_energy_le_of_harmonic_restriction
    {C : ℝ} (hC : 1 ≤ C) (hR : HarmonicL2Restriction C)
    {N : ℕ} (a : Fin (N + 1) → ℂ) (ha : ∑ k, ‖a k‖ ^ 2 = 1)
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) :
    -(Real.log (∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N)) ≤
      Real.log 2 + fourierDistributionConstant C *
        Real.log (2 / (fourierMeasure N).real E) ^ 6 := by
  by_cases hsmall : (fourierMeasure N).real E ≤ 9 / 10
  · let mass := (fourierMeasure N).real
    let value (s : Set (SignVector N × AddCircle (1 : ℝ))) :=
      -Real.log (∫ z in s, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N)
    let admissible (s : Set (SignVector N × AddCircle (1 : ℝ))) :=
      MeasurableSet s ∧ 0 < mass s
    let p := distributionMomentOrder (mass E)
    have hp : 1 ≤ p := (distributionMomentOrder_bounds hpos measureReal_le_one).1
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    apply distribution_bound_log_six_of_successor_growth spreadingIncrementConstant_pos
      (spreadingIncrementConstant_le_ninth.trans (by norm_num))
      (spreadingRecurrenceConstant_pos hC).le mass value admissible E ⟨hE, hpos⟩ hpos hsmall
    · intro s hs hslo hshi
      obtain hgood | ⟨t, ht, _hst, hgrow, henergy⟩ :=
        restricted_energy_or_spreading_of_harmonic_restriction s hs.1 hs.2 p hp hC
          (fun m hmn ξ hξ q hq γ hγ hγ1 i b hb hsub hden P hP =>
            hR.at_order hC hmn ξ hξ hq hγ hγ1 i b hb hsub hden P hP)
      · refine ⟨univ, ⟨MeasurableSet.univ, by simp [mass]⟩, ?_, by simp [mass], ?_⟩
        · have hstep := distributionStep_le_mul hpR spreadingIncrementConstant_pos.le hs.2
            (measureReal_le_one : mass s ≤ 1)
          have hmul : spreadingIncrementConstant * mass s ≤ (1 / 9 : ℝ) * (9 / 10) :=
            mul_le_mul spreadingIncrementConstant_le_ninth hshi hs.2.le (by norm_num)
          simp only [mass, probReal_univ]
          linarith
        · have he := hgood a ha
          have hlog := Real.log_le_log (div_pos hs.2 (by norm_num)) he
          have hcost := log_four_div_le_spreading_cost hpos hslo hshi hC p hp
          have heq : Real.log (4 / mass s) = -Real.log (mass s / 4) := by
            rw [Real.log_div (by norm_num) hs.2.ne', Real.log_div hs.2.ne' (by norm_num)]
            ring
          rw [heq] at hcost
          have huniv : value univ = 0 := by
            simp only [value, setIntegral_univ, integral_norm_sq_randomFourier, ha, Real.log_one,
              neg_zero]
          rw [huniv]
          change -Real.log _ ≤ _
          linarith
      · have htpos : 0 < mass t := hs.2.trans_le (le_trans
            (le_add_of_nonneg_right (by positivity)) hgrow)
        refine ⟨t, ⟨ht, htpos⟩, ?_, measureReal_le_one, ?_⟩
        · have hstep := distributionStep_le_critical_gain hs.2 measureReal_le_one p hp
          exact (add_le_add (le_refl _) hstep).trans hgrow
        · have hSpos : 0 < spreadingEnergyConstant (shiftOrder (mass s) p) (mass s) C :=
            zero_lt_one.trans_le (one_le_spreadingEnergyConstant _ hs.2 (by linarith))
          have hlog := neg_log_le_neg_log_add_of_mul_bound
            (restricted_fourier_energy_pos a ha s hs.2)
            (restricted_fourier_energy_pos a ha t htpos) hSpos (henergy a ha)
          exact hlog.trans (add_le_add (le_refl _)
            (log_spreadingEnergyConstant_shiftOrder_le_initial_mass hpos hslo hshi hC p hp))
    · intro s hs hslarge _
      exact neg_log_restricted_fourier_energy_le_log_two a ha s hs.1 hslarge.le
  · exact (neg_log_restricted_fourier_energy_le_log_two a ha E hE (le_of_not_ge hsmall)).trans
      (le_add_of_nonneg_right (mul_nonneg (fourierDistributionConstant_pos hC).le (by positivity)))

/-- The finite coefficient in the restricted-energy exponential. -/
def fourierEnergyExponent (C : ℝ) : ℝ := 64 + fourierDistributionConstant C

theorem one_le_fourierEnergyExponent {C : ℝ} (hC : 1 ≤ C) : 1 ≤ fourierEnergyExponent C := by
  have := fourierDistributionConstant_pos hC
  unfold fourierEnergyExponent
  linarith

/-- Every positive-measure set captures a quantitatively bounded fraction of
the normalized Fourier energy. -/
theorem restricted_fourier_energy_lower_bound_of_harmonic_restriction
    {C : ℝ} (hC : 1 ≤ C) (hR : HarmonicL2Restriction C)
    {N : ℕ} (a : Fin (N + 1) → ℂ) (ha : ∑ k, ‖a k‖ ^ 2 = 1)
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) :
    1 ≤ Real.exp (fourierEnergyExponent C * Real.log (2 / (fourierMeasure N).real E) ^ 6) *
      ∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N := by
  have h := neg_log_restricted_fourier_energy_le_of_harmonic_restriction hC hR a ha E hE hpos
  have hmass : (fourierMeasure N).real E ≤ 1 := measureReal_le_one
  have hratio : (2 : ℝ) ≤ 2 / (fourierMeasure N).real E :=
    (le_div_iff₀ hpos).mpr (by linarith)
  have hL : (1 / 2 : ℝ) ≤ Real.log (2 / (fourierMeasure N).real E) := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratio
    linarith [Real.log_two_gt_d9]
  have hpower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hL 6
  norm_num at hpower
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have he := restricted_fourier_energy_pos a ha E hpos
  have hnon : 0 ≤ fourierEnergyExponent C * Real.log (2 / (fourierMeasure N).real E) ^ 6 +
      Real.log (∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) := by
    unfold fourierEnergyExponent
    nlinarith
  have hexp := Real.one_le_exp hnon
  rwa [Real.exp_add, Real.exp_log he] at hexp

/-- The normalized negative logarithm has an integrable stretched exponential
with total integral at most three. -/
theorem negative_log_stretched_exponential_of_harmonic_restriction
    {C : ℝ} (hC : 1 ≤ C) (hR : HarmonicL2Restriction C)
    {N : ℕ} (a : Fin (N + 1) → ℂ) (ha : ∑ k, ‖a k‖ ^ 2 = 1) :
    Integrable (fun z => Real.exp ((1 / 2 : ℝ) *
      (negativeLogNorm (randomFourier a z) / fourierEnergyExponent C) ^ ((6 : ℝ)⁻¹)))
      (fourierMeasure N) ∧
    (∫ z, Real.exp ((1 / 2 : ℝ) *
      (negativeLogNorm (randomFourier a z) / fourierEnergyExponent C) ^ ((6 : ℝ)⁻¹))
      ∂fourierMeasure N) ≤ 3 := by
  apply integrable_exp_root_negativeLogNorm_of_restrictedEnergy
    (zero_lt_one.trans_le (one_le_fourierEnergyExponent hC))
    (measurable_randomFourier a) (integrable_norm_sq_randomFourier a)
  exact fun E hE hpos =>
    restricted_fourier_energy_lower_bound_of_harmonic_restriction hC hR a ha E hE hpos

/-- Every real moment of the negative logarithm obeys the sixth-power moment
scale, uniformly over normalized finite coefficient vectors. -/
theorem negative_log_moments_of_harmonic_restriction
    {C : ℝ} (hC : 1 ≤ C) (hR : HarmonicL2Restriction C)
    {N : ℕ} (a : Fin (N + 1) → ℂ) (ha : ∑ k, ‖a k‖ ^ 2 = 1)
    {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun z => negativeLogNorm (randomFourier a z) ^ p) (fourierMeasure N) ∧
      (∫ z, negativeLogNorm (randomFourier a z) ^ p ∂fourierMeasure N) ≤
        (36 * fourierEnergyExponent C * p) ^ (6 * p) := by
  let A := fourierEnergyExponent C
  have hA1 : 1 ≤ A := one_le_fourierEnergyExponent hC
  have hA : 0 < A := zero_lt_one.trans_le hA1
  let t := 1 / (2 * A ^ ((6 : ℝ)⁻¹))
  have ht : 0 < t := by dsimp only [t]; positivity
  have hX : Measurable (fun z => negativeLogNorm (randomFourier a z)) :=
    (measurable_randomFourier a).norm.log.neg.max measurable_const
  obtain ⟨hI, hbound⟩ := negative_log_stretched_exponential_of_harmonic_restriction hC hR a ha
  have heq : (fun z => Real.exp ((1 / 2 : ℝ) *
      (negativeLogNorm (randomFourier a z) / A) ^ ((6 : ℝ)⁻¹))) =
      (fun z => Real.exp (t * |negativeLogNorm (randomFourier a z)| ^ ((6 : ℝ)⁻¹))) := by
    funext z
    rw [abs_of_nonneg (negativeLogNorm_nonneg _),
      Real.div_rpow (negativeLogNorm_nonneg _) hA.le]
    congr 1
    dsimp only [t]
    ring
  change Integrable (fun z => Real.exp ((1 / 2 : ℝ) *
    (negativeLogNorm (randomFourier a z) / A) ^ ((6 : ℝ)⁻¹))) (fourierMeasure N) at hI
  change (∫ z, Real.exp ((1 / 2 : ℝ) *
    (negativeLogNorm (randomFourier a z) / A) ^ ((6 : ℝ)⁻¹)) ∂fourierMeasure N) ≤ 3 at hbound
  rw [heq] at hI hbound
  have hint := integrable_abs_rpow_of_stretchedExponential hX
    (by norm_num : (0 : ℝ) < 6) ht (by linarith : 0 ≤ p) hI
  have hm := integral_abs_rpow_le_of_stretchedExponential_bound hX
    (by norm_num : (1 : ℝ) ≤ 6) ht hp (by norm_num : (1 : ℝ) ≤ 3) hI hbound
  simp only [abs_of_nonneg (negativeLogNorm_nonneg _)] at hint hm
  refine ⟨hint, hm.trans ?_⟩
  have hroot : A ^ ((6 : ℝ)⁻¹) ≤ A := Real.rpow_le_self_of_one_le hA1 (by norm_num)
  have hconstant : 6 * 3 / t * p ≤ 36 * A * p := by
    dsimp only [t]
    have he : (6 : ℝ) * 3 / (1 / (2 * A ^ ((6 : ℝ)⁻¹))) * p =
        36 * A ^ ((6 : ℝ)⁻¹) * p := by rw [one_div, div_inv_eq_mul]; ring
    rw [he]
    gcongr
  exact Real.rpow_le_rpow (by positivity) hconstant (by linarith)

/-- The finite constant in the uniform absolute logarithmic-moment estimate. -/
def fourierLogarithmicConstant (C : ℝ) : ℝ := 72 * fourierEnergyExponent C

theorem fourierLogarithmicConstant_pos {C : ℝ} (hC : 1 ≤ C) :
    0 < fourierLogarithmicConstant C := by
  have := zero_lt_one.trans_le (one_le_fourierEnergyExponent hC)
  unfold fourierLogarithmicConstant
  positivity

/-- Coefficient-uniform logarithmic moments for normalized finite Rademacher
Fourier sums. The exponent six follows from the actual spreading recurrence;
the only conditional input is harmonic restriction on measurable subsets of
one real interval. -/
theorem uniform_logarithmic_moments_of_harmonic_restriction
    {C : ℝ} (hC : 1 ≤ C) (hR : HarmonicL2Restriction C)
    {N : ℕ} (a : Fin (N + 1) → ℂ) (ha : ∑ k, ‖a k‖ ^ 2 = 1)
    {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun z => |Real.log ‖randomFourier a z‖| ^ p) (fourierMeasure N) ∧
      (∫ z, |Real.log ‖randomFourier a z‖| ^ p ∂fourierMeasure N) ≤
        (fourierLogarithmicConstant C * p) ^ (6 * p) := by
  obtain ⟨hneg, hnegBound⟩ := negative_log_moments_of_harmonic_restriction hC hR a ha hp
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  refine ⟨(integrable_abs_log_norm_rpow_iff a hp0).mpr hneg, ?_⟩
  let u := 36 * fourierEnergyExponent C * p
  have hA := one_le_fourierEnergyExponent hC
  have hu36 : 36 ≤ u := by
    calc
      (36 : ℝ) = 36 * 1 * 1 := by norm_num
      _ ≤ _ := by dsimp only [u]; gcongr
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hpbase : p / 2 ≤ u := by
    dsimp only [u]
    nlinarith [mul_le_mul_of_nonneg_right hA hp0.le]
  have hup : u ≤ u ^ p := Real.self_le_rpow_of_one_le hu1 hp
  have hposBound : (∫ z, positiveLogNorm (randomFourier a z) ^ p ∂fourierMeasure N) ≤
      u ^ (6 * p) := by
    calc
      _ ≤ (p / 2) ^ p * 2 := integral_rpow_positiveLogNorm_le a ha hp0.le
      _ ≤ u ^ p * u ^ p := by
        exact mul_le_mul (Real.rpow_le_rpow (by positivity) hpbase hp0.le)
          (by linarith : (2 : ℝ) ≤ u ^ p) (by norm_num) (Real.rpow_nonneg hu0 _)
      _ = u ^ (2 * p) := by rw [← Real.rpow_add (by linarith : 0 < u)]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
  rw [integral_abs_log_norm_rpow_eq a hp0 hneg]
  calc
    _ ≤ 2 * u ^ (6 * p) := by linarith
    _ ≤ (2 : ℝ) ^ (6 * p) * u ^ (6 * p) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hu0 _)
      exact Real.self_le_rpow_of_one_le (by norm_num) (by linarith)
    _ = (2 * u) ^ (6 * p) := (Real.mul_rpow (by norm_num) hu0).symm
    _ = _ := by congr 1; unfold fourierLogarithmicConstant; dsimp only [u]; ring

end Erdos522.LogMoments

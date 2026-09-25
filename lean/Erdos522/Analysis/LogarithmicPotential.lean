/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.ExponentialTailIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Average

/-!
# Logarithmic potentials on real sets

The negative logarithmic potential of any complex point has a uniform integral
bound on a real set of prescribed length.  The bound follows by integrating the
length estimate for the intersection of a complex disk with the real line.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Erdos522

/-- The nonnegative part of the logarithmic potential of a complex point. -/
def negativeLogPotential (z : ℂ) (x : ℝ) : ℝ :=
  max (-Real.log ‖(x : ℂ) - z‖) 0

/-- The portion of a logarithmic potential above height `T`. -/
def negativeLogPotentialTail (z : ℂ) (T x : ℝ) : ℝ :=
  max (-Real.log ‖(x : ℂ) - z‖ - T) 0

theorem measurable_negativeLogPotential (z : ℂ) :
    Measurable (negativeLogPotential z) := by
  unfold negativeLogPotential
  fun_prop

theorem measurable_negativeLogPotentialTail (z : ℂ) (T : ℝ) :
    Measurable (negativeLogPotentialTail z T) := by
  unfold negativeLogPotentialTail
  fun_prop

/-- A disk of radius `r` cuts the real line in a set of length at most `2r`. -/
theorem volume_real_complex_distance_le (z : ℂ) (r : ℝ) :
    volume {x : ℝ | ‖(x : ℂ) - z‖ ≤ r} ≤ ENNReal.ofReal (2 * r) := by
  calc
    _ ≤ volume (Metric.closedBall z.re r) := by
      apply measure_mono
      intro x hx
      rw [Metric.mem_closedBall, Real.dist_eq]
      have h : |x - z.re| ≤ ‖(x : ℂ) - z‖ := by
        simpa using Complex.abs_re_le_norm ((x : ℂ) - z)
      exact h.trans hx
    _ = _ := Real.volume_closedBall z.re r

/-- The possible singular point of a logarithmic potential is Lebesgue null. -/
theorem ae_real_complex_sub_ne_zero (z : ℂ) :
    ∀ᵐ x : ℝ ∂volume, (x : ℂ) - z ≠ 0 := by
  apply ae_iff.mpr
  apply measure_mono_null (t := {z.re})
  · intro x hx
    simp only [mem_ofPred_eq, not_not] at hx
    have hx' := congrArg Complex.re (sub_eq_zero.mp hx)
    simpa using hx'
  · exact measure_singleton _

/-- Exponential tails hold for the excess potential on every restricted real set. -/
theorem measure_negativeLogPotentialTail_ge_le (z : ℂ) (E : Set ℝ)
    (T s : ℝ) (hs : 0 < s) :
    (volume.restrict E) {x | s ≤ negativeLogPotentialTail z T x} ≤
      ENNReal.ofReal (2 * Real.exp (-T) * Real.exp (-s)) := by
  have hsub : {x | s ≤ negativeLogPotentialTail z T x} ⊆
      {x : ℝ | ‖(x : ℂ) - z‖ ≤ Real.exp (-(T + s))} := by
    intro x hx
    change s ≤ max (-Real.log ‖(x : ℂ) - z‖ - T) 0 at hx
    have hlog : s ≤ -Real.log ‖(x : ℂ) - z‖ - T := by
      rcases le_max_iff.mp hx with h | h
      · exact h
      · linarith
    by_cases hx0 : (x : ℂ) - z = 0
    · change ‖(x : ℂ) - z‖ ≤ Real.exp (-(T + s))
      simpa only [hx0, norm_zero] using (Real.exp_pos (-(T + s))).le
    · exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hx0)).mp (by linarith)
  calc
    _ ≤ volume {x | s ≤ negativeLogPotentialTail z T x} :=
      Measure.restrict_le_self _
    _ ≤ volume {x : ℝ | ‖(x : ℂ) - z‖ ≤ Real.exp (-(T + s))} :=
      measure_mono hsub
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(T + s))) :=
      volume_real_complex_distance_le z _
    _ = _ := by rw [neg_add, Real.exp_add, mul_assoc]

/-- The integral of the excess above height `T` is at most `2 exp (-T)`. -/
theorem integrable_negativeLogPotentialTail_and_integral_le
    (z : ℂ) (E : Set ℝ) (T : ℝ) :
    IntegrableOn (negativeLogPotentialTail z T) E ∧
      (∫ x in E, negativeLogPotentialTail z T x) ≤ 2 * Real.exp (-T) := by
  simpa only [IntegrableOn, one_mul, div_one] using
    integrable_and_integral_le_of_exponential_tail (volume.restrict E)
      (negativeLogPotentialTail z T) (measurable_negativeLogPotentialTail z T)
      (fun _ => le_max_right _ _) (2 * Real.exp (-T)) 1 (by positivity) (by norm_num)
      (fun s hs => by simpa using measure_negativeLogPotentialTail_ge_le z E T s hs)

/-- Clipping a nonnegative logarithmic potential at a nonnegative height. -/
theorem negativeLogPotential_le_height_add_tail (z : ℂ) {T : ℝ}
    (hT : 0 ≤ T) (x : ℝ) :
    negativeLogPotential z x ≤ T + negativeLogPotentialTail z T x := by
  unfold negativeLogPotential negativeLogPotentialTail
  apply max_le
  · have h := le_max_left (-Real.log ‖(x : ℂ) - z‖ - T) 0
    linarith
  · exact add_nonneg hT (le_max_right _ _)

/-- A real set of finite length at most two has a uniform logarithmic-potential bound. -/
theorem integrable_negativeLogPotential_and_integral_le
    (z : ℂ) (E : Set ℝ) (hfinite : volume E ≠ ∞)
    (hpos : 0 < volume.real E) (hle : volume.real E ≤ 2) :
    IntegrableOn (negativeLogPotential z) E ∧
      (∫ x in E, negativeLogPotential z x) ≤
        volume.real E * (1 + Real.log (2 / volume.real E)) := by
  let α := volume.real E
  let T := Real.log (2 / α)
  have hα : 0 < α := hpos
  have hratio : 0 < 2 / α := div_pos (by norm_num) hα
  have hT : 0 ≤ T := Real.log_nonneg ((one_le_div hα).mpr hle)
  have htailvalue : 2 * Real.exp (-T) = α := by
    dsimp [T]
    rw [Real.exp_neg, Real.exp_log hratio]
    field_simp
  obtain ⟨htail, htailint⟩ := integrable_negativeLogPotentialTail_and_integral_le z E T
  rw [htailvalue] at htailint
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hfinite
  have hdom : Integrable (fun x => T + negativeLogPotentialTail z T x)
      (volume.restrict E) := (integrable_const T).add htail
  have hint : IntegrableOn (negativeLogPotential z) E :=
    hdom.mono' (measurable_negativeLogPotential z).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact negativeLogPotential_le_height_add_tail z hT x)
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ x in E, T + negativeLogPotentialTail z T x :=
      integral_mono hint hdom (negativeLogPotential_le_height_add_tail z hT)
    _ = α * T + ∫ x in E, negativeLogPotentialTail z T x := by
      rw [integral_add (integrable_const T) htail, setIntegral_const, smul_eq_mul]
    _ ≤ α * T + α := add_le_add_right htailint _
    _ = _ := by dsimp [α, T]; ring

/-- On the centered unit interval the bound depends only on the length of the set. -/
theorem integrable_negativeLogPotential_on_unit_interval_and_integral_le
    (z : ℂ) (E : Set ℝ) (hE : E ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hpos : 0 < volume.real E) :
    IntegrableOn (negativeLogPotential z) E ∧
      (∫ x in E, negativeLogPotential z x) ≤
        volume.real E * (1 + Real.log (2 / volume.real E)) := by
  have hmeasure : volume E ≤ ENNReal.ofReal 1 := by
    calc
      _ ≤ volume (Icc (-(1 / 2 : ℝ)) (1 / 2)) := measure_mono hE
      _ = _ := by rw [Real.volume_Icc]; norm_num
  have hfinite : volume E ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmeasure
  have hle : volume.real E ≤ 2 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
    norm_num [measureReal_def] at h ⊢
    linarith
  exact integrable_negativeLogPotential_and_integral_le z E hfinite hpos hle

/-- The sum of the negative logarithmic potentials of a multiset, with multiplicities. -/
def multisetNegativeLogPotential (s : Multiset ℂ) (x : ℝ) : ℝ :=
  (s.map (fun z => negativeLogPotential z x)).sum

/-- The product of the linear factors attached to a multiset, with multiplicities. -/
def realLinearFactorProduct (s : Multiset ℂ) (x : ℝ) : ℂ :=
  (s.map (fun z => (x : ℂ) - z)).prod

theorem multisetNegativeLogPotential_nonneg (s : Multiset ℂ) (x : ℝ) :
    0 ≤ multisetNegativeLogPotential s x := by
  apply Multiset.sum_nonneg
  intro y hy
  obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hy
  exact le_max_right _ _

theorem measurable_multisetNegativeLogPotential (s : Multiset ℂ) :
    Measurable (multisetNegativeLogPotential s) := by
  induction s using Multiset.induction_on with
  | empty =>
    change Measurable (fun _ : ℝ => (0 : ℝ))
    exact measurable_const
  | cons z s ih =>
    have heq : multisetNegativeLogPotential (z ::ₘ s) =
        negativeLogPotential z + multisetNegativeLogPotential s := by
      funext x
      simp only [multisetNegativeLogPotential, Multiset.map_cons, Multiset.sum_cons,
        Pi.add_apply]
    rw [heq]
    exact (measurable_negativeLogPotential z).add ih

theorem continuous_realLinearFactorProduct (s : Multiset ℂ) :
    Continuous (realLinearFactorProduct s) := by
  induction s using Multiset.induction_on with
  | empty =>
    change Continuous (fun _ : ℝ => (1 : ℂ))
    exact continuous_const
  | cons z s ih =>
    have heq : realLinearFactorProduct (z ::ₘ s) =
        (fun x : ℝ => (x : ℂ) - z) * realLinearFactorProduct s := by
      funext x
      simp only [realLinearFactorProduct, Multiset.map_cons, Multiset.prod_cons,
        Pi.mul_apply]
    rw [heq]
    exact (Complex.continuous_ofReal.sub (continuous_const (y := z))).mul ih

/-- A finite product of linear factors is nonzero almost everywhere on the real line. -/
theorem ae_realLinearFactorProduct_ne_zero (s : Multiset ℂ) :
    ∀ᵐ x : ℝ ∂volume, realLinearFactorProduct s x ≠ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp [realLinearFactorProduct]
  | cons z s ih =>
    filter_upwards [ae_real_complex_sub_ne_zero z, ih] with x hx hs
    simpa only [realLinearFactorProduct, Multiset.map_cons, Multiset.prod_cons] using
      mul_ne_zero hx hs

/-- Integrating a finite sum of potentials preserves every multiplicity. -/
theorem integrable_multisetNegativeLogPotential_and_integral_le
    (s : Multiset ℂ) (E : Set ℝ) (hfinite : volume E ≠ ∞)
    (hpos : 0 < volume.real E) (hle : volume.real E ≤ 2) :
    IntegrableOn (multisetNegativeLogPotential s) E ∧
      (∫ x in E, multisetNegativeLogPotential s x) ≤
        s.card * (volume.real E * (1 + Real.log (2 / volume.real E))) := by
  induction s using Multiset.induction_on with
  | empty =>
    constructor
    · change Integrable (fun _ : ℝ => (0 : ℝ)) (volume.restrict E)
      exact integrable_zero _ _ _
    · simp [multisetNegativeLogPotential]
  | cons z s ih =>
    obtain ⟨hz, hzint⟩ := integrable_negativeLogPotential_and_integral_le z E hfinite hpos hle
    obtain ⟨hs, hsint⟩ := ih
    have heq : multisetNegativeLogPotential (z ::ₘ s) =
        fun x => negativeLogPotential z x + multisetNegativeLogPotential s x := by
      funext x
      simp only [multisetNegativeLogPotential, Multiset.map_cons, Multiset.sum_cons]
    rw [heq]
    refine ⟨hz.add hs, ?_⟩
    rw [integral_add hz hs]
    calc
      _ ≤ volume.real E * (1 + Real.log (2 / volume.real E)) +
          s.card * (volume.real E * (1 + Real.log (2 / volume.real E))) :=
        add_le_add hzint hsint
      _ = _ := by rw [Multiset.card_cons, Nat.cast_add, Nat.cast_one]; ring

/-- The negative logarithm of a product is bounded by the sum of its negative logarithms. -/
theorem negative_log_norm_realLinearFactorProduct_le
    (s : Multiset ℂ) (x : ℝ) :
    max (-Real.log ‖realLinearFactorProduct s x‖) 0 ≤
      multisetNegativeLogPotential s x := by
  induction s using Multiset.induction_on with
  | empty => simp [realLinearFactorProduct, multisetNegativeLogPotential]
  | cons z s ih =>
    have heq : realLinearFactorProduct (z ::ₘ s) x =
        ((x : ℂ) - z) * realLinearFactorProduct s x := by
      simp only [realLinearFactorProduct, Multiset.map_cons, Multiset.prod_cons]
    rw [heq]
    by_cases hz : (x : ℂ) - z = 0
    · simpa only [hz, zero_mul, norm_zero, Real.log_zero, neg_zero, max_self] using
        multisetNegativeLogPotential_nonneg (z ::ₘ s) x
    by_cases hs : realLinearFactorProduct s x = 0
    · simpa only [hs, mul_zero, norm_zero, Real.log_zero, neg_zero, max_self] using
        multisetNegativeLogPotential_nonneg (z ::ₘ s) x
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hs)]
    apply max_le
    · have hzle : -Real.log ‖(x : ℂ) - z‖ ≤ negativeLogPotential z x := le_max_left _ _
      have hsle := (le_max_left (-Real.log ‖realLinearFactorProduct s x‖) 0).trans ih
      simp only [multisetNegativeLogPotential, Multiset.map_cons, Multiset.sum_cons]
      change -(Real.log ‖(x : ℂ) - z‖ + Real.log ‖realLinearFactorProduct s x‖) ≤
        negativeLogPotential z x + multisetNegativeLogPotential s x
      linarith
    · exact multisetNegativeLogPotential_nonneg (z ::ₘ s) x

/-- The negative logarithm of a finite product of linear factors has the same integral bound. -/
theorem integrable_negative_log_norm_realLinearFactorProduct_and_integral_le
    (s : Multiset ℂ) (E : Set ℝ) (hfinite : volume E ≠ ∞)
    (hpos : 0 < volume.real E) (hle : volume.real E ≤ 2) :
    IntegrableOn (fun x => max (-Real.log ‖realLinearFactorProduct s x‖) 0) E ∧
      (∫ x in E, max (-Real.log ‖realLinearFactorProduct s x‖) 0) ≤
        s.card * (volume.real E * (1 + Real.log (2 / volume.real E))) := by
  obtain ⟨hs, hsint⟩ :=
    integrable_multisetNegativeLogPotential_and_integral_le s E hfinite hpos hle
  have hmeas : Measurable (fun x => max (-Real.log ‖realLinearFactorProduct s x‖) 0) :=
    ((continuous_realLinearFactorProduct s).measurable.norm.log.neg).max measurable_const
  have hint : IntegrableOn (fun x => max (-Real.log ‖realLinearFactorProduct s x‖) 0) E :=
    hs.mono_nonneg hmeas.aestronglyMeasurable (ae_of_all _ fun _ => le_max_right _ _)
      (ae_of_all _ fun x => negative_log_norm_realLinearFactorProduct_le s x)
  exact ⟨hint, (integral_mono hint hs (negative_log_norm_realLinearFactorProduct_le s)).trans hsint⟩

/-- On a real set of positive length a product of `n` linear factors takes a value
of norm at least `(length / (2 exp 1))^n`. -/
theorem exists_realLinearFactorProduct_norm_ge
    (s : Multiset ℂ) (E : Set ℝ) (hE : MeasurableSet E) (hfinite : volume E ≠ ∞)
    (hpos : 0 < volume.real E) (hle : volume.real E ≤ 2) :
    ∃ x ∈ E, (volume.real E / (2 * Real.exp 1)) ^ s.card ≤
      ‖realLinearFactorProduct s x‖ := by
  let α := volume.real E
  let C := (s.card : ℝ) * (1 + Real.log (2 / α))
  let f := fun x => max (-Real.log ‖realLinearFactorProduct s x‖) 0
  let μ := volume.restrict E
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hfinite
  obtain ⟨hf, hfint⟩ :=
    integrable_negative_log_norm_realLinearFactorProduct_and_integral_le s E hfinite hpos hle
  have hμ : μ ≠ 0 := by
    intro hz
    have heq : α = 0 := by
      calc
        α = μ.real univ := (measureReal_restrict_apply_univ E).symm
        _ = 0 := by rw [hz]; simp
    exact hpos.ne' heq
  have hgood : ∀ᵐ x ∂μ, x ∈ E ∧ realLinearFactorProduct s x ≠ 0 :=
    (ae_restrict_mem hE).and (ae_restrict_of_ae (ae_realLinearFactorProduct_ne_zero s))
  have hnull : μ {x | ¬(x ∈ E ∧ realLinearFactorProduct s x ≠ 0)} = 0 := ae_iff.mp hgood
  obtain ⟨x, hxgood, hxmean⟩ := exists_notMem_null_le_average hμ (show Integrable f μ from hf) hnull
  have hx : x ∈ E ∧ realLinearFactorProduct s x ≠ 0 := by simpa using hxgood
  have hmean : (⨍ x, f x ∂μ) ≤ C := by
    rw [average_eq, smul_eq_mul]
    dsimp [μ]
    rw [measureReal_restrict_apply_univ]
    change α⁻¹ * (∫ x in E, f x) ≤ C
    calc
      _ ≤ α⁻¹ * (s.card * (α * (1 + Real.log (2 / α)))) :=
        mul_le_mul_of_nonneg_left hfint (inv_nonneg.mpr hpos.le)
      _ = C := by dsimp [C]; field_simp [show α ≠ 0 from hpos.ne']
  have hlog : -C ≤ Real.log ‖realLinearFactorProduct s x‖ := by
    have hfx : -Real.log ‖realLinearFactorProduct s x‖ ≤ f x := le_max_left _ _
    have hxC := hxmean.trans hmean
    linarith
  refine ⟨x, hx.1, ?_⟩
  have hexp := (Real.le_log_iff_exp_le (norm_pos_iff.mpr hx.2)).mp hlog
  have heq : Real.exp (-C) = (α / (2 * Real.exp 1)) ^ s.card := by
    dsimp [C]
    rw [← mul_neg, Real.exp_nat_mul]
    congr 1
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rw [heq] at hexp
  exact hexp

end Erdos522

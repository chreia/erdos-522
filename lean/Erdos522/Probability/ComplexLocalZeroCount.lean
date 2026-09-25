/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SymmetricArcEnergy
import Erdos522.Probability.BoundedPolynomialSuprema
import Erdos522.Probability.LocalZeroCount

/-!
# Local zero counts for symmetric unit-modulus coefficients

The complex arc-energy bound supplies a nearby large value at every angular
position. Local Jensen then controls all closed disks near the unit circle,
counting zeros with their polynomial multiplicities.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
namespace Erdos522
namespace ComplexLocalZeroCount

theorem eval_ofFn_circle {N : ℕ} (a : Fin (N + 1) → ℂ) (θ : ArcEnergy.Angle) :
    (Polynomial.ofFn (N + 1) a).eval (AddCircle.toCircle θ : ℂ) =
      ArcEnergy.complexFourierSum a θ := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [eval_finsetSum, eval_monomial, ArcEnergy.complexFourierSum]
  congr 1
  ext k
  congr 1
  rw [show (k.val : ℤ) = (k.val : ℕ) by rfl]
  simp [fourier, AddCircle.toCircle_nsmul]

/-- Unit-bounded coefficients give the same disk growth bound as signs. -/
theorem norm_eval_ofFn_le_exp {N : ℕ} (a : Fin (N + 1) → ℂ) (ha : ∀ k, ‖a k‖ ≤ 1)
    {c z : ℂ} (hc : ‖c‖ = 1) {R : ℝ} (hR : 0 ≤ R)
    (hz : z ∈ Metric.closedBall c (2 * R)) :
    ‖(Polynomial.ofFn (N + 1) a).eval z‖ ≤ (N + 1 : ℝ) * Real.exp (2 * N * R) := by
  have hnorm : ‖z‖ ≤ 1 + 2 * R := by
    have htri := norm_le_norm_sub_add z c
    have hdist : ‖z - c‖ ≤ 2 * R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    rw [hc] at htri
    linarith
  have hb := BoundedPolynomialSuprema.norm_iterate_derivative_ofFn_le N 0 a (by norm_num) ha
    (by linarith : 1 ≤ 1 + 2 * R) hnorm
  simp only [Function.iterate_zero, id_eq, pow_zero, one_mul] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + 2 * R)
    (by simpa only [add_comm] using Real.add_one_le_exp (2 * R)) N
  calc
    _ ≤ Real.exp (2 * R) ^ N := hp
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- A large unit-circle value controls the nearby closed-disk root count. -/
theorem zero_count_bound_of_large_circle_value {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∀ k, ‖a k‖ ≤ 1) {c : ℂ} (hc : ‖c‖ = 1) {R : ℝ} (hR : 0 < R)
    (hlarge : (N + 1 : ℝ) / 2 ≤ ‖(Polynomial.ofFn (N + 1) a).eval c‖ ^ 2) :
    (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall c R) : ℝ) ≤
      (Real.log (N + 1) / 2 + Real.log 2 / 2 + 2 * N * R) / Real.log 2 := by
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hnorm : 0 < ‖(Polynomial.ofFn (N + 1) a).eval c‖ := by
    by_contra! h
    have hz : ‖(Polynomial.ofFn (N + 1) a).eval c‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [hz] at hlarge
    nlinarith
  have hM : 1 ≤ (N + 1 : ℝ) * Real.exp (2 * N * R) := by
    have hexp : 1 ≤ Real.exp (2 * N * R) := Real.one_le_exp (by positivity)
    have hn : (1 : ℝ) ≤ N + 1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
    nlinarith
  have hbase := local_zero_count_bound (Polynomial.ofFn (N + 1) a) c hR (by linarith : R < 2 * R)
    hM (norm_pos_iff.mp hnorm) (fun z hz =>
      norm_eval_ofFn_le_exp a ha hc hR.le (Metric.sphere_subset_closedBall hz))
  have hloglarge : (Real.log (N + 1) - Real.log 2) / 2 ≤
      Real.log ‖(Polynomial.ofFn (N + 1) a).eval c‖ := by
    have h := Real.log_le_log (by positivity : 0 < (N + 1 : ℝ) / 2) hlarge
    rw [Real.log_div hN1.ne' (by norm_num), Real.log_pow] at h
    norm_num at h
    linarith
  rw [show (2 * R) / R = 2 by field_simp, Real.log_mul hN1.ne' (Real.exp_ne_zero _),
    Real.log_exp] at hbase
  apply hbase.trans
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  linarith

/-- Large values on a short angular cover lie close to every nearby complex center. -/
theorem exists_large_value_near_center (P : Polynomial ℂ) {ι : Type*}
    (θ : ι → ArcEnergy.Angle) {h b : ℝ}
    (hcover : ∀ φ, ∃ i, dist φ (θ i) ≤ h / (2 * Real.pi))
    (hvalues : ∀ i, ∃ t ∈ ArcEnergy.arc (θ i) h,
      b ≤ ‖P.eval (AddCircle.toCircle t : ℂ)‖ ^ 2)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ dist z₀ c ≤ |‖z₀‖ - 1| + 2 * h ∧ b ≤ ‖P.eval c‖ ^ 2 := by
  let u : Circle := ⟨NormedSpace.normalize z₀, by
    change NormedSpace.normalize z₀ ∈ Metric.sphere (0 : ℂ) 1
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hz₀⟩
  obtain ⟨φ, hφ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective u
  rw [AddCircle.homeomorphCircle_apply] at hφ
  have hφc : (AddCircle.toCircle φ : ℂ) = NormedSpace.normalize z₀ := congrArg Subtype.val hφ
  obtain ⟨i, hi⟩ := hcover φ
  obtain ⟨t, ht, hlarge⟩ := hvalues i
  refine ⟨(AddCircle.toCircle t : ℂ), Circle.norm_coe _, ?_, hlarge⟩
  have hdist : dist t (θ i) ≤ h / (2 * Real.pi) := ht
  have hangular : dist φ t ≤ h / Real.pi := by
    have htri := dist_triangle φ (θ i) t
    rw [dist_comm (θ i) t] at htri
    have heq : h / (2 * Real.pi) + h / (2 * Real.pi) = h / Real.pi := by ring
    rw [← heq]
    exact htri.trans (add_le_add hi hdist)
  have hchord := LocalZeroCount.circle_chord_le_angular_distance φ t
  rw [hφc] at hchord
  have hnormdist : dist (NormedSpace.normalize z₀) (AddCircle.toCircle t : ℂ) ≤ 2 * h := by
    rw [dist_eq_norm]
    calc
      _ ≤ 2 * Real.pi * dist φ t := hchord
      _ ≤ 2 * Real.pi * (h / Real.pi) := mul_le_mul_of_nonneg_left hangular (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ dist z₀ (NormedSpace.normalize z₀) +
      dist (NormedSpace.normalize z₀) (AddCircle.toCircle t : ℂ) := dist_triangle _ _ _
    _ ≤ |‖z₀‖ - 1| + 2 * h := by rw [LocalZeroCount.dist_normalize_eq hz₀]; gcongr

theorem local_count_of_nearby_large_value {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∀ k, ‖a k‖ ≤ 1) {K h : ℝ} (hK : 0 ≤ K) (hh : 0 ≤ h) (hN : 0 < N)
    {z₀ c : ℂ} (hc : ‖c‖ = 1) (hdist : dist z₀ c ≤ 1 / (N : ℝ) + 2 * h)
    (hlarge : (N + 1 : ℝ) / 2 ≤ ‖(Polynomial.ofFn (N + 1) a).eval c‖ ^ 2) :
    (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall z₀ (2 * K / N)) : ℝ) ≤
      (Real.log (N + 1) / 2 + Real.log 2 / 2 +
        2 * N * ((2 * K + 1) / N + 2 * h)) / Real.log 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hR : 0 < (2 * K + 1) / (N : ℝ) + 2 * h := by positivity
  have hsub : Metric.closedBall z₀ (2 * K / (N : ℝ)) ⊆
      Metric.closedBall c ((2 * K + 1) / N + 2 * h) := by
    intro z hz
    have hzdist : dist z z₀ ≤ 2 * K / N := hz
    have htri := dist_triangle z z₀ c
    change dist z c ≤ _
    have heq : (2 * K + 1) / (N : ℝ) = 2 * K / N + 1 / N := by ring
    rw [heq]
    linarith
  have hcount : (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall z₀ (2 * K / N)) : ℝ) ≤
      zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall c ((2 * K + 1) / N + 2 * h)) := by
    exact_mod_cast zeroCountIn_mono (Polynomial.ofFn (N + 1) a) hsub
  exact hcount.trans (zero_count_bound_of_large_circle_value a ha hc hR hlarge)

/-- The finite angular cover gives simultaneous closed-disk zero counts under
any symmetric unit-modulus product law. -/
theorem simultaneous_local_count_of_cover (N : ℕ) (hN : 2 ≤ N)
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] (hnorm : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ = 1)
    {ι : Type*} [Fintype ι] (θ : ι → ArcEnergy.Angle) (hcard : Fintype.card ι ≤ 8 * N)
    (hwidth : ArcEnergy.arcScale * Real.log N / N ≤ Real.pi)
    (hcover : ∀ φ, ∃ i, dist φ (θ i) ≤
      (ArcEnergy.arcScale * Real.log N / N) / (2 * Real.pi)) {K : ℝ} (hK : 0 ≤ K) :
    (Measure.pi μ).real {a | ∃ z₀ : ℂ, |‖z₀‖ - 1| ≤ 1 / (N : ℝ) ∧
      (Real.log (N + 1) / 2 + Real.log 2 / 2 +
        2 * N * ((2 * K + 1) / N + 2 * (ArcEnergy.arcScale * Real.log N / N))) / Real.log 2 <
      (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall z₀ (2 * K / N)) : ℝ)} ≤
        1 / (N : ℝ) ^ 3 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hh : 0 ≤ ArcEnergy.arcScale * Real.log N / N := by
    unfold ArcEnergy.arcScale
    positivity
  have hcoef := BoundedPolynomialSuprema.ae_coordinate_norm_le μ
    (fun k => (hnorm k).mono (fun _ hz => hz.le))
  apply le_trans _ (ArcEnergy.simultaneous_complex_large_values N hN μ hnorm θ hcard hwidth)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hcoef] with a ha
  intro ⟨z₀, hz₀, hcount⟩
  by_contra hfailure
  change ¬ ∃ i, ∀ t ∈ ArcEnergy.arc (θ i) (ArcEnergy.arcScale * Real.log N / N),
    ‖ArcEnergy.complexFourierSum a t‖ ^ 2 ≤ (N + 1 : ℝ) / 2 at hfailure
  push Not at hfailure
  have hz₀ne : z₀ ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero, zero_sub, abs_neg, abs_one] at hz₀
    have h := (one_le_div hN0).mp hz₀
    linarith
  have hvalues : ∀ i, ∃ t ∈ ArcEnergy.arc (θ i) (ArcEnergy.arcScale * Real.log N / N),
      (N + 1 : ℝ) / 2 ≤ ‖(Polynomial.ofFn (N + 1) a).eval (AddCircle.toCircle t : ℂ)‖ ^ 2 := by
    intro i
    obtain ⟨t, ht, hlarge⟩ := hfailure i
    exact ⟨t, ht, by rw [eval_ofFn_circle]; exact hlarge.le⟩
  obtain ⟨c, hc, hdist, hlarge⟩ := exists_large_value_near_center
    (Polynomial.ofFn (N + 1) a) θ hcover hvalues hz₀ne
  have hbound := local_count_of_nearby_large_value a ha hK hh (by omega) hc
    (hdist.trans (by linarith)) hlarge
  exact (not_lt_of_ge hbound) hcount

/-- Simultaneously at every center within `1/N` of the unit circle, the
closed disk of radius `2K/N` contains at most `C_K log N` zeros with multiplicity. -/
theorem simultaneous_local_zero_count (N : ℕ) (hN : 2 ≤ N)
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] (hnorm : ∀ k, ∀ᵐ z ∂μ k, ‖z‖ = 1)
    (hwidth : ArcEnergy.arcScale * Real.log N / N ≤ 1) {K : ℝ} (hK : 0 ≤ K) :
    (Measure.pi μ).real {a | ∃ z₀ : ℂ, |‖z₀‖ - 1| ≤ 1 / (N : ℝ) ∧
      LocalZeroCount.localCountConstant K * Real.log N <
        (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall z₀ (2 * K / N)) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 := by
  have hlog := LocalZeroCount.one_le_log_of_arcWidth_le_one hN hwidth
  obtain ⟨J, hJ, hcover⟩ := LocalZeroCount.exists_logarithmic_angular_cover hN hlog
  have hbase := simultaneous_local_count_of_cover N hN μ hnorm (LocalZeroCount.angularGrid J)
    (by simpa using hJ) (hwidth.trans (by linarith [Real.two_le_pi])) hcover hK
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hbase
  intro a ⟨z₀, hz₀, hcount⟩
  exact ⟨z₀, hz₀, lt_of_le_of_lt (LocalZeroCount.local_jensen_quotient_le hN hlog hK) hcount⟩

/-- The simultaneous local zero-count theorem for the actual Steinhaus law. -/
theorem steinhaus_local_zero_count (N : ℕ) (hN : 2 ≤ N)
    (hwidth : ArcEnergy.arcScale * Real.log N / N ≤ 1) {K : ℝ} (hK : 0 ≤ K) :
    (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real
      {a | ∃ z₀ : ℂ, |‖z₀‖ - 1| ≤ 1 / (N : ℝ) ∧
        LocalZeroCount.localCountConstant K * Real.log N <
          (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall z₀ (2 * K / N)) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 :=
  simultaneous_local_zero_count N hN _ (fun _ => ae_norm_steinhaus_eq_one) hwidth hK

end ComplexLocalZeroCount
end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianArcEnergy
import Erdos522.Probability.GaussianLocalZeroCount
import Erdos522.Probability.ComplexLocalZeroCount

/-!
# Simultaneous local zero counts for circular Gaussian polynomials

A logarithmic angular cover supplies nearby large values. Cauchy–Schwarz on
the coefficient-energy event controls each surrounding disk, and Jensen's
formula counts its zeros with multiplicity, including the boundary.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators
namespace Erdos522
namespace CircularGaussianLocalZeroCount
open LocalZeroCount

/-- The coefficient-energy event controls the coefficient one-norm. -/
theorem sum_norm_le_of_energy {N : ℕ} (a : Fin (N + 1) → ℂ)
    (henergy : ∑ k, ‖a k‖ ^ 2 ≤ 2 * (N + 1 : ℝ)) :
    ∑ k, ‖a k‖ ≤ Real.sqrt 2 * (N + 1 : ℝ) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun k : Fin (N + 1) => ‖a k‖) (g := fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hc
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hnonneg : 0 ≤ ∑ k, ‖a k‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hm := mul_le_mul_of_nonneg_right henergy (by positivity : (0 : ℝ) ≤ N + 1)
  have hsq : (∑ k, ‖a k‖) ^ 2 ≤ (Real.sqrt 2 * (N + 1 : ℝ)) ^ 2 := by
    rw [mul_pow, hs]
    nlinarith only [hc, hm]
  exact (sq_le_sq₀ hnonneg (by positivity)).mp hsq

/-- Cauchy–Schwarz yields the local disk supremum on the coefficient-energy event. -/
theorem norm_eval_le_exp {N : ℕ} (a : Fin (N + 1) → ℂ)
    (henergy : ∑ k, ‖a k‖ ^ 2 ≤ 2 * (N + 1 : ℝ))
    {c z : ℂ} (hc : ‖c‖ = 1) {R : ℝ} (hR : 0 ≤ R)
    (hz : z ∈ Metric.closedBall c (2 * R)) :
    ‖(Polynomial.ofFn (N + 1) a).eval z‖ ≤ Real.sqrt 2 * (N + 1 : ℝ) * Real.exp (2 * N * R) := by
  have hnorm : ‖z‖ ≤ 1 + 2 * R := by
    have htri := norm_le_norm_sub_add z c
    have hdist : ‖z - c‖ ≤ 2 * R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    rw [hc] at htri
    linarith
  have hpow (k : Fin (N + 1)) : ‖z‖ ^ k.val ≤ Real.exp (2 * N * R) := by
    calc
      _ ≤ (1 + 2 * R) ^ N := (pow_le_pow_left₀ (norm_nonneg _) hnorm _).trans
        (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + 2 * R) (Nat.le_of_lt_succ k.isLt))
      _ ≤ (Real.exp (2 * R)) ^ N := pow_le_pow_left₀ (by linarith)
        (by simpa only [add_comm] using Real.add_one_le_exp (2 * R)) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [eval_finsetSum, eval_monomial]
  calc
    _ ≤ ∑ k, ‖a k * z ^ k.val‖ := norm_sum_le _ _
    _ = ∑ k, ‖a k‖ * ‖z‖ ^ k.val := by
      simp only [norm_mul, norm_pow]
    _ ≤ ∑ k, ‖a k‖ * Real.exp (2 * N * R) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hpow k) (norm_nonneg _)
    _ = (∑ k, ‖a k‖) * Real.exp (2 * N * R) := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_norm_le_of_energy a henergy) (Real.exp_pos _).le

/-- A large Gaussian polynomial value bounds all nearby zeros by a Jensen quotient. -/
theorem zero_count_bound_of_large_circle_value {N : ℕ} (a : Fin (N + 1) → ℂ)
    (henergy : ∑ k, ‖a k‖ ^ 2 ≤ 2 * (N + 1 : ℝ))
    {c : ℂ} (hc : ‖c‖ = 1) {R : ℝ} (hR : 0 < R)
    (hlarge : (N + 1 : ℝ) / 2 ≤ ‖(Polynomial.ofFn (N + 1) a).eval c‖ ^ 2) :
    (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall c R) : ℝ) ≤
      (Real.log (N + 1) / 2 + Real.log 2 + 2 * N * R) / Real.log 2 := by
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hnorm : 0 < ‖(Polynomial.ofFn (N + 1) a).eval c‖ := by
    by_contra! h
    have hz : ‖(Polynomial.ofFn (N + 1) a).eval c‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [hz] at hlarge
    nlinarith
  have hs : 1 ≤ Real.sqrt (2 : ℝ) := by norm_num
  have hM : 1 ≤ Real.sqrt 2 * (N + 1 : ℝ) * Real.exp (2 * N * R) := by
    have hexp : 1 ≤ Real.exp (2 * N * R) := Real.one_le_exp (by positivity)
    have hn : (1 : ℝ) ≤ N + 1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hs hn) hexp
  have hbase := local_zero_count_bound (Polynomial.ofFn (N + 1) a) c hR (by linarith : R < 2 * R)
    hM (norm_pos_iff.mp hnorm) (fun z hz =>
      norm_eval_le_exp a henergy hc hR.le (Metric.sphere_subset_closedBall hz))
  have hloglarge : (Real.log (N + 1) - Real.log 2) / 2 ≤
      Real.log ‖(Polynomial.ofFn (N + 1) a).eval c‖ := by
    have h := Real.log_le_log (by positivity : 0 < (N + 1 : ℝ) / 2) hlarge
    rw [Real.log_div hN1.ne' (by norm_num), Real.log_pow] at h
    norm_num at h
    linarith
  rw [show (2 * R) / R = 2 by field_simp,
    Real.log_mul (by positivity : Real.sqrt 2 * (N + 1 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_mul (by positivity : Real.sqrt (2 : ℝ) ≠ 0) hN1.ne', Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.log_exp] at hbase
  apply hbase.trans
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  linarith

/-- Two independent real-coordinate arrays control the total complex coefficient energy. -/
theorem coefficient_energy_upper_tail (N : ℕ) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
      {a | 2 * (N + 1 : ℝ) < ∑ k, ‖a k‖ ^ 2} ≤
      2 * Real.exp (-3 * (N + 1 : ℝ) / 32) := by
  let E : Set (Fin (N + 1) → ℝ) := {g | 2 * (N + 1 : ℝ) < ∑ k, g k ^ 2}
  have hE : (gaussianCoefficientMeasure (N + 1)).real E ≤
      Real.exp (-3 * (N + 1 : ℝ) / 32) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (gaussian_coefficient_energy_gt_two_dimension_le (n := N + 1) (by omega))
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le, Nat.cast_add, Nat.cast_one,
      measureReal_def, E] using h
  have he (g : (Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) :
      (∑ k, ‖circularGaussianCoefficientVectorEquiv (N + 1) g k‖ ^ 2) =
        ((∑ k, g.1 k ^ 2) + (∑ k, g.2 k ^ 2)) / 2 := by
    have hk (k : Fin (N + 1)) :
        ‖circularGaussianCoefficientVectorEquiv (N + 1) g k‖ ^ 2 =
          (g.1 k ^ 2 + g.2 k ^ 2) / 2 := by
      rw [circularGaussianCoefficientVectorEquiv_apply, norm_div, div_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
        Real.sq_sqrt (by norm_num), Complex.sq_norm]
      simp [Complex.normSq_apply, pow_two]
    simp only [hk, ← Finset.sum_div, Finset.sum_add_distrib]
  have h := circularGaussian_coefficient_event_le (N + 1)
    {a | 2 * (N + 1 : ℝ) < ∑ k, ‖a k‖ ^ 2} E E (by
      intro g hg
      change 2 * (N + 1 : ℝ) < ∑ k, ‖circularGaussianCoefficientVectorEquiv (N + 1) g k‖ ^ 2 at hg
      rw [he] at hg
      change 2 * (N + 1 : ℝ) < ∑ k, g.1 k ^ 2 ∨ 2 * (N + 1 : ℝ) < ∑ k, g.2 k ^ 2
      by_contra! hn
      linarith [hn.1, hn.2])
  exact h.trans (by linarith)

/-- The Jensen radius contains every target disk whenever the large center value is close enough. -/
theorem local_count_of_nearby_large_value {N : ℕ} (a : Fin (N + 1) → ℂ)
    (henergy : ∑ k, ‖a k‖ ^ 2 ≤ 2 * (N + 1 : ℝ))
    {K h : ℝ} (hK : 0 ≤ K) (hh : 0 ≤ h) (hN : 0 < N)
    {z₀ c : ℂ} (hc : ‖c‖ = 1)
    (hdist : dist z₀ c ≤ 1 / (N : ℝ) + 2 * h)
    (hlarge : (N + 1 : ℝ) / 2 ≤ ‖(Polynomial.ofFn (N + 1) a).eval c‖ ^ 2) :
    (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall z₀ (2 * K / N)) : ℝ) ≤
      (Real.log (N + 1) / 2 + Real.log 2 +
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
  exact hcount.trans (zero_count_bound_of_large_circle_value a henergy hc hR hlarge)



/-- A finite logarithmic angular cover controls all nearby disks simultaneously. -/
theorem simultaneous_local_count_of_cover (N : ℕ) (hN : 2 ≤ N)
    {ι : Type*} [Fintype ι] (θ : ι → AddCircle (1 : ℝ))
    (hcard : Fintype.card ι ≤ 8 * N)
    (hwidth : ArcEnergy.arcScale * Real.log N / N ≤ Real.pi)
    (hcover : ∀ φ, ∃ i, dist φ (θ i) ≤
      (ArcEnergy.arcScale * Real.log N / N) / (2 * Real.pi))
    {K : ℝ} (hK : 0 ≤ K) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {a | ∃ z₀ : ℂ,
      |‖z₀‖ - 1| ≤ 1 / (N : ℝ) ∧
      (Real.log (N + 1) / 2 + Real.log 2 +
        2 * N * ((2 * K + 1) / N + 2 * (ArcEnergy.arcScale * Real.log N / N))) / Real.log 2 <
      (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall z₀ (2 * K / N)) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + 2 * Real.exp (-3 * (N + 1 : ℝ) / 32) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hh : 0 ≤ ArcEnergy.arcScale * Real.log N / N := by
    unfold ArcEnergy.arcScale
    positivity
  let F := {a : Fin (N + 1) → ℂ | ∃ i, ∀ t ∈ ArcEnergy.arc (θ i) (ArcEnergy.arcScale * Real.log N / N),
    ‖ArcEnergy.complexFourierSum a t‖ ^ 2 ≤ (N + 1 : ℝ) / 2}
  let E := {a : Fin (N + 1) → ℂ | 2 * (N + 1 : ℝ) < ∑ k, ‖a k‖ ^ 2}
  have hF : (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real F ≤ 1 / (N : ℝ) ^ 3 :=
    CircularGaussianArcEnergy.simultaneous_large_values N hN θ hcard hwidth
  have hE : (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real E ≤
      2 * Real.exp (-3 * (N + 1 : ℝ) / 32) := coefficient_energy_upper_tail N
  refine (measureReal_mono (s₂ := F ∪ E) ?_ (measure_ne_top _ _)).trans
    ((measureReal_union_le F E).trans (add_le_add hF hE))
  intro a hg
  by_cases he : 2 * (N + 1 : ℝ) < ∑ k, ‖a k‖ ^ 2
  · exact Or.inr he
  · left
    have henergy := le_of_not_gt he
    obtain ⟨z₀, hz₀, hcount⟩ := hg
    by_contra hfailure
    change ¬ ∃ i, ∀ t ∈ ArcEnergy.arc (θ i) (ArcEnergy.arcScale * Real.log N / N),
      ‖ArcEnergy.complexFourierSum a t‖ ^ 2 ≤ (N + 1 : ℝ) / 2 at hfailure
    push Not at hfailure
    have hz₀ne : z₀ ≠ 0 := by
      intro hz
      have hbad : (1 : ℝ) ≤ 1 / N := by simpa [hz] using hz₀
      have := (le_div_iff₀ hN0).mp hbad
      nlinarith
    obtain ⟨c, hc, hdist, hlarge⟩ := ComplexLocalZeroCount.exists_large_value_near_center
      (Polynomial.ofFn (N + 1) a) θ hcover (fun i => by
        obtain ⟨t, ht, hv⟩ := hfailure i
        exact ⟨t, ht, by rw [ComplexLocalZeroCount.eval_ofFn_circle]; exact hv.le⟩) hz₀ne
    have hdist' : dist z₀ c ≤ 1 / (N : ℝ) + 2 * (ArcEnergy.arcScale * Real.log N / N) :=
      hdist.trans (add_le_add hz₀ le_rfl)
    exact (not_lt_of_ge (local_count_of_nearby_large_value a henergy hK hh (by omega) hc hdist' hlarge)) hcount

/-- All closed disks at reciprocal-degree scale obey the Gaussian local-count bound,
with the arc and coefficient-energy exceptional probabilities displayed separately. -/
theorem simultaneous_local_zero_count (N : ℕ) (hN : 2 ≤ N)
    (hwidth : ArcEnergy.arcScale * Real.log N / N ≤ 1) {K : ℝ} (hK : 0 ≤ K) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {a | ∃ z₀ : ℂ,
      |‖z₀‖ - 1| ≤ 1 / (N : ℝ) ∧
      GaussianLocalZeroCount.localCountConstant K * Real.log N <
        (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall z₀ (2 * K / N)) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + 2 * Real.exp (-3 * (N + 1 : ℝ) / 32) := by
  have hlog := one_le_log_of_arcWidth_le_one hN hwidth
  obtain ⟨J, hJ, hcover⟩ := exists_logarithmic_angular_cover hN hlog
  have hbase := simultaneous_local_count_of_cover N hN (angularGrid J)
    (by simpa using hJ) (hwidth.trans (by linarith [Real.two_le_pi])) hcover hK
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hbase
  intro a hg
  obtain ⟨z₀, hz₀, hcount⟩ := hg
  exact ⟨z₀, hz₀, lt_of_le_of_lt (GaussianLocalZeroCount.local_jensen_quotient_le hN hlog hK) hcount⟩

end CircularGaussianLocalZeroCount
end Erdos522

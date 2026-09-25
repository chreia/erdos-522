/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianArcEnergy
import Erdos522.Probability.GaussianRadialEnergy
import Erdos522.Probability.GaussianJets
import Erdos522.Probability.LocalZeroCount

/-!
# Simultaneous local zero counts for Gaussian polynomials

Arc energy supplies nearby large values. On the coefficient-energy event,
Cauchy–Schwarz bounds the surrounding disk supremum, and Jensen's formula
counts every zero with multiplicity in each closed disk.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators
namespace Erdos522
namespace GaussianLocalZeroCount
open LocalZeroCount

/-- Gaussian polynomial values agree with the real Fourier sum used in arc energy. -/
theorem eval_circle {N : ℕ} (g : Fin (N + 1) → ℝ) (θ : AddCircle (1 : ℝ)) :
    (gaussianPolynomial N g).eval (AddCircle.toCircle θ : ℂ) = ArcEnergy.fourierSum g θ := by
  simp only [gaussianPolynomial_eval, ArcEnergy.fourierSum, Complex.real_smul]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp [fourier, AddCircle.toCircle_nsmul]

/-- The coefficient-energy event controls the coefficient one-norm. -/
theorem sum_abs_le_of_energy {N : ℕ} (g : Fin (N + 1) → ℝ)
    (henergy : ∑ k, g k ^ 2 ≤ 2 * (N + 1 : ℝ)) :
    ∑ k, |g k| ≤ Real.sqrt 2 * (N + 1 : ℝ) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun k : Fin (N + 1) => |g k|) (g := fun _ => (1 : ℝ))
  simp only [mul_one, sq_abs, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hc
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hnonneg : 0 ≤ ∑ k, |g k| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hm := mul_le_mul_of_nonneg_right henergy (by positivity : (0 : ℝ) ≤ N + 1)
  have hsq : (∑ k, |g k|) ^ 2 ≤ (Real.sqrt 2 * (N + 1 : ℝ)) ^ 2 := by
    rw [mul_pow, hs]
    nlinarith only [hc, hm]
  exact (sq_le_sq₀ hnonneg (by positivity)).mp hsq

/-- Cauchy–Schwarz yields the local disk supremum on the coefficient-energy event. -/
theorem norm_eval_le_exp {N : ℕ} (g : Fin (N + 1) → ℝ)
    (henergy : ∑ k, g k ^ 2 ≤ 2 * (N + 1 : ℝ))
    {c z : ℂ} (hc : ‖c‖ = 1) {R : ℝ} (hR : 0 ≤ R)
    (hz : z ∈ Metric.closedBall c (2 * R)) :
    ‖(gaussianPolynomial N g).eval z‖ ≤ Real.sqrt 2 * (N + 1 : ℝ) * Real.exp (2 * N * R) := by
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
  rw [gaussianPolynomial_eval]
  calc
    _ ≤ ∑ k, ‖(g k : ℂ) * z ^ k.val‖ := norm_sum_le _ _
    _ = ∑ k, |g k| * ‖z‖ ^ k.val := by
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ k, |g k| * Real.exp (2 * N * R) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hpow k) (abs_nonneg _)
    _ = (∑ k, |g k|) * Real.exp (2 * N * R) := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_abs_le_of_energy g henergy) (Real.exp_pos _).le

/-- A large Gaussian polynomial value bounds all nearby zeros by a Jensen quotient. -/
theorem zero_count_bound_of_large_circle_value {N : ℕ} (g : Fin (N + 1) → ℝ)
    (henergy : ∑ k, g k ^ 2 ≤ 2 * (N + 1 : ℝ))
    {c : ℂ} (hc : ‖c‖ = 1) {R : ℝ} (hR : 0 < R)
    (hlarge : (N + 1 : ℝ) / 2 ≤ ‖(gaussianPolynomial N g).eval c‖ ^ 2) :
    (zeroCountIn (gaussianPolynomial N g) (Metric.closedBall c R) : ℝ) ≤
      (Real.log (N + 1) / 2 + Real.log 2 + 2 * N * R) / Real.log 2 := by
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hnorm : 0 < ‖(gaussianPolynomial N g).eval c‖ := by
    by_contra! h
    have hz : ‖(gaussianPolynomial N g).eval c‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [hz] at hlarge
    nlinarith
  have hs : 1 ≤ Real.sqrt (2 : ℝ) := by norm_num
  have hM : 1 ≤ Real.sqrt 2 * (N + 1 : ℝ) * Real.exp (2 * N * R) := by
    have hexp : 1 ≤ Real.exp (2 * N * R) := Real.one_le_exp (by positivity)
    have hn : (1 : ℝ) ≤ N + 1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hs hn) hexp
  have hbase := local_zero_count_bound (gaussianPolynomial N g) c hR (by linarith : R < 2 * R)
    hM (norm_pos_iff.mp hnorm) (fun z hz =>
      norm_eval_le_exp g henergy hc hR.le (Metric.sphere_subset_closedBall hz))
  have hloglarge : (Real.log (N + 1) - Real.log 2) / 2 ≤
      Real.log ‖(gaussianPolynomial N g).eval c‖ := by
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

/-- A short angular cover and large values on its arcs control every nearby center. -/
theorem exists_large_value_near_center {N : ℕ} (g : Fin (N + 1) → ℝ)
    {ι : Type*} (θ : ι → AddCircle (1 : ℝ)) {h : ℝ} (_hh : 0 ≤ h)
    (hcover : ∀ φ, ∃ i, dist φ (θ i) ≤ h / (2 * Real.pi))
    (hvalues : ∀ i, ∃ t ∈ ArcEnergy.arc (θ i) h,
      (N + 1 : ℝ) / 2 ≤ ‖ArcEnergy.fourierSum g t‖ ^ 2)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      dist z₀ c ≤ |‖z₀‖ - 1| + 2 * h ∧
      (N + 1 : ℝ) / 2 ≤ ‖(gaussianPolynomial N g).eval c‖ ^ 2 := by
  let u : Circle := ⟨NormedSpace.normalize z₀, by
    change NormedSpace.normalize z₀ ∈ Metric.sphere (0 : ℂ) 1
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hz₀⟩
  obtain ⟨φ, hφ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective u
  rw [AddCircle.homeomorphCircle_apply] at hφ
  have hφc : (AddCircle.toCircle φ : ℂ) = NormedSpace.normalize z₀ := congrArg Subtype.val hφ
  obtain ⟨i, hi⟩ := hcover φ
  obtain ⟨t, ht, hlarge⟩ := hvalues i
  refine ⟨(AddCircle.toCircle t : ℂ), Circle.norm_coe _, ?_, ?_⟩
  · have hdist : dist t (θ i) ≤ h / (2 * Real.pi) := ht
    have hangular : dist φ t ≤ h / Real.pi := by
      have htri := dist_triangle φ (θ i) t
      rw [dist_comm (θ i) t] at htri
      have heq : h / (2 * Real.pi) + h / (2 * Real.pi) = h / Real.pi := by ring
      rw [← heq]
      exact htri.trans (add_le_add hi hdist)
    have hchord := circle_chord_le_angular_distance φ t
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
      _ ≤ |‖z₀‖ - 1| + 2 * h := by rw [dist_normalize_eq hz₀]; gcongr
  · simpa only [eval_circle] using hlarge

/-- The Jensen radius contains every target disk whenever the large center value is close enough. -/
theorem local_count_of_nearby_large_value {N : ℕ} (g : Fin (N + 1) → ℝ)
    (henergy : ∑ k, g k ^ 2 ≤ 2 * (N + 1 : ℝ))
    {K h : ℝ} (hK : 0 ≤ K) (hh : 0 ≤ h) (hN : 0 < N)
    {z₀ c : ℂ} (hc : ‖c‖ = 1)
    (hdist : dist z₀ c ≤ 1 / (N : ℝ) + 2 * h)
    (hlarge : (N + 1 : ℝ) / 2 ≤ ‖(gaussianPolynomial N g).eval c‖ ^ 2) :
    (zeroCountIn (gaussianPolynomial N g) (Metric.closedBall z₀ (2 * K / N)) : ℝ) ≤
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
  have hcount : (zeroCountIn (gaussianPolynomial N g) (Metric.closedBall z₀ (2 * K / N)) : ℝ) ≤
      zeroCountIn (gaussianPolynomial N g) (Metric.closedBall c ((2 * K + 1) / N + 2 * h)) := by
    exact_mod_cast zeroCountIn_mono (gaussianPolynomial N g) hsub
  exact hcount.trans (zero_count_bound_of_large_circle_value g henergy hc hR hlarge)



/-- A finite logarithmic angular cover controls all nearby disks simultaneously. -/
theorem simultaneous_local_count_of_cover (N : ℕ) (hN : 2 ≤ N)
    {ι : Type*} [Fintype ι] (θ : ι → AddCircle (1 : ℝ))
    (hcard : Fintype.card ι ≤ 8 * N)
    (hwidth : ArcEnergy.arcScale * Real.log N / N ≤ Real.pi)
    (hcover : ∀ φ, ∃ i, dist φ (θ i) ≤
      (ArcEnergy.arcScale * Real.log N / N) / (2 * Real.pi))
    {K : ℝ} (hK : 0 ≤ K) :
    (gaussianCoefficientMeasure (N + 1)).real {g | ∃ z₀ : ℂ,
      |‖z₀‖ - 1| ≤ 1 / (N : ℝ) ∧
      (Real.log (N + 1) / 2 + Real.log 2 +
        2 * N * ((2 * K + 1) / N + 2 * (ArcEnergy.arcScale * Real.log N / N))) / Real.log 2 <
      (zeroCountIn (gaussianPolynomial N g) (Metric.closedBall z₀ (2 * K / N)) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + Real.exp (-3 * (N + 1 : ℝ) / 32) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hh : 0 ≤ ArcEnergy.arcScale * Real.log N / N := by
    unfold ArcEnergy.arcScale
    positivity
  let F := {g : Fin (N + 1) → ℝ | ∃ i, ∀ t ∈ ArcEnergy.arc (θ i) (ArcEnergy.arcScale * Real.log N / N),
    ‖ArcEnergy.fourierSum g t‖ ^ 2 ≤ (N + 1 : ℝ) / 2}
  let E := {g : Fin (N + 1) → ℝ | 2 * (N + 1 : ℝ) < ∑ k, g k ^ 2}
  have hF : (gaussianCoefficientMeasure (N + 1)).real F ≤ 1 / (N : ℝ) ^ 3 :=
    GaussianArcEnergy.simultaneous_large_values N hN θ hcard hwidth
  have hE : (gaussianCoefficientMeasure (N + 1)).real E ≤ Real.exp (-3 * (N + 1 : ℝ) / 32) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (gaussian_coefficient_energy_gt_two_dimension_le (n := N + 1) (by omega))
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le, Nat.cast_add, Nat.cast_one, measureReal_def, E] using h
  refine (measureReal_mono (s₂ := F ∪ E) ?_ (measure_ne_top _ _)).trans
    ((measureReal_union_le F E).trans (add_le_add hF hE))
  intro g hg
  by_cases he : 2 * (N + 1 : ℝ) < ∑ k, g k ^ 2
  · exact Or.inr he
  · left
    have henergy := le_of_not_gt he
    obtain ⟨z₀, hz₀, hcount⟩ := hg
    by_contra hfailure
    change ¬ ∃ i, ∀ t ∈ ArcEnergy.arc (θ i) (ArcEnergy.arcScale * Real.log N / N),
      ‖ArcEnergy.fourierSum g t‖ ^ 2 ≤ (N + 1 : ℝ) / 2 at hfailure
    push Not at hfailure
    have hz₀ne : z₀ ≠ 0 := by
      intro hz
      have hbad : (1 : ℝ) ≤ 1 / N := by simpa [hz] using hz₀
      have := (le_div_iff₀ hN0).mp hbad
      nlinarith
    obtain ⟨c, hc, hdist, hlarge⟩ := exists_large_value_near_center g θ hh hcover
      (fun i => by
        obtain ⟨t, ht, hv⟩ := hfailure i
        exact ⟨t, ht, hv.le⟩) hz₀ne
    have hdist' : dist z₀ c ≤ 1 / (N : ℝ) + 2 * (ArcEnergy.arcScale * Real.log N / N) :=
      hdist.trans (add_le_add hz₀ le_rfl)
    exact (not_lt_of_ge (local_count_of_nearby_large_value g henergy hK hh (by omega) hc hdist' hlarge)) hcount

/-- The Gaussian local-count constant includes the coefficient-energy allowance. -/
def localCountConstant (K : ℝ) : ℝ := LocalZeroCount.localCountConstant K + 2 / Real.log 2

/-- The exact Gaussian Jensen quotient fits the stated logarithmic constant. -/
theorem local_jensen_quotient_le {N : ℕ} (hN : 2 ≤ N)
    (hlog : 1 ≤ Real.log (N : ℝ)) {K : ℝ} (hK : 0 ≤ K) :
    (Real.log (N + 1) / 2 + Real.log 2 +
      2 * N * ((2 * K + 1) / N + 2 * (ArcEnergy.arcScale * Real.log N / N))) /
      Real.log 2 ≤ localCountConstant K * Real.log N := by
  have hb := LocalZeroCount.local_jensen_quotient_le hN hlog hK
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h2u : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have he : (Real.log (N + 1) / 2 + Real.log 2 +
      2 * N * ((2 * K + 1) / N + 2 * (ArcEnergy.arcScale * Real.log N / N))) / Real.log 2 =
      (Real.log (N + 1) / 2 + Real.log 2 / 2 +
      2 * N * ((2 * K + 1) / N + 2 * (ArcEnergy.arcScale * Real.log N / N))) / Real.log 2 + 1 / 2 := by
    field_simp
    ring
  have herr : (1 / 2 : ℝ) ≤ (2 / Real.log 2) * Real.log N := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ h2).mpr
    linarith
  rw [he, localCountConstant, add_mul]
  exact add_le_add hb herr

/-- All closed disks at reciprocal-degree scale obey the Gaussian local-count bound,
with the arc and coefficient-energy exceptional probabilities displayed separately. -/
theorem simultaneous_local_zero_count (N : ℕ) (hN : 2 ≤ N)
    (hwidth : ArcEnergy.arcScale * Real.log N / N ≤ 1) {K : ℝ} (hK : 0 ≤ K) :
    (gaussianCoefficientMeasure (N + 1)).real {g | ∃ z₀ : ℂ,
      |‖z₀‖ - 1| ≤ 1 / (N : ℝ) ∧
      localCountConstant K * Real.log N <
        (zeroCountIn (gaussianPolynomial N g) (Metric.closedBall z₀ (2 * K / N)) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + Real.exp (-3 * (N + 1 : ℝ) / 32) := by
  have hlog := one_le_log_of_arcWidth_le_one hN hwidth
  obtain ⟨J, hJ, hcover⟩ := exists_logarithmic_angular_cover hN hlog
  have hbase := simultaneous_local_count_of_cover N hN (angularGrid J)
    (by simpa using hJ) (hwidth.trans (by linarith [Real.two_le_pi])) hcover hK
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hbase
  intro g hg
  obtain ⟨z₀, hz₀, hcount⟩ := hg
  exact ⟨z₀, hz₀, lt_of_le_of_lt (local_jensen_quotient_le hN hlog hK) hcount⟩

end GaussianLocalZeroCount
end Erdos522

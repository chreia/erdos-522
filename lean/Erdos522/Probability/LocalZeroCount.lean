/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Basic.RademacherPolynomial
import Erdos522.Analysis.LocalJensenBound
import Erdos522.Probability.ArcEnergy
import Erdos522.Analysis.AngularSeparation
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Simultaneous local zero counts for Rademacher polynomials

Arc energy supplies large values near every angular position. A local Jensen
bound turns these values into root-count bounds on disks of radius proportional
to the reciprocal degree.
-/

noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators

namespace Erdos522
namespace LocalZeroCount

/-- The finite Rademacher polynomial with all deterministic weights equal to one. -/
abbrev rademacherPolynomial {N : ℕ} (ω : LogMoments.SignVector N) : Polynomial ℂ :=
  Erdos522.rademacherPolynomial N ω

/-- Its unit-circle values agree with the real-coordinate Fourier sum used for arc energy. -/
theorem eval_rademacherPolynomial_circle {N : ℕ} (ω : LogMoments.SignVector N)
    (θ : AddCircle (1 : ℝ)) :
    (rademacherPolynomial ω).eval (AddCircle.toCircle θ : ℂ) =
      ArcEnergy.fourierSum (fun k => LogMoments.realSign (ω k)) θ := by
  change LogMoments.fourierPolynomial (fun _ => 1) ω θ = _
  rw [LogMoments.fourierPolynomial_eq_sum]
  simp only [ArcEnergy.fourierSum, mul_one, Complex.real_smul, LogMoments.ofReal_realSign]

/-- A deterministic modulus bound for every sign realization on a fixed disk. -/
theorem norm_eval_rademacherPolynomial_le {N : ℕ} (ω : LogMoments.SignVector N)
    {z : ℂ} {B : ℝ} (hB : 1 ≤ B) (hz : ‖z‖ ≤ B) :
    ‖(rademacherPolynomial ω).eval z‖ ≤ (N + 1 : ℝ) * B ^ N := by
  classical
  simp only [rademacherPolynomial, Erdos522.rademacherPolynomial, LogMoments.signedPolynomial, eval_finsetSum,
    eval_monomial, mul_one]
  calc
    _ ≤ ∑ k : Fin (N + 1), ‖LogMoments.sign (ω k) * z ^ k.val‖ := norm_sum_le _ _
    _ = ∑ k : Fin (N + 1), ‖z‖ ^ k.val := by
      simp only [norm_mul, LogMoments.norm_sign, norm_pow, one_mul]
    _ ≤ ∑ _k : Fin (N + 1), B ^ N := by
      apply Finset.sum_le_sum
      intro k _
      exact (pow_le_pow_left₀ (norm_nonneg _) hz k.val).trans
        (pow_le_pow_right₀ hB (Nat.le_of_lt_succ k.isLt))
    _ = _ := by simp

/-- Exponential form of the disk modulus bound around a point on the unit circle. -/
theorem norm_eval_rademacherPolynomial_le_exp {N : ℕ} (ω : LogMoments.SignVector N)
    {c z : ℂ} (hc : ‖c‖ = 1) {R : ℝ} (hR : 0 ≤ R)
    (hz : z ∈ Metric.closedBall c (2 * R)) :
    ‖(rademacherPolynomial ω).eval z‖ ≤ (N + 1 : ℝ) * Real.exp (2 * N * R) := by
  have hnorm : ‖z‖ ≤ 1 + 2 * R := by
    have htri := norm_le_norm_sub_add z c
    have hdist : ‖z - c‖ ≤ 2 * R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    rw [hc] at htri
    linarith
  apply (norm_eval_rademacherPolynomial_le ω (by linarith : 1 ≤ 1 + 2 * R) hnorm).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + 2 * R) (by simpa only [add_comm] using Real.add_one_le_exp (2 * R)) N
  calc
    _ ≤ (Real.exp (2 * R)) ^ N := hp
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- A large value on the unit circle gives an explicit nearby closed-disk root count. -/
theorem zero_count_bound_of_large_circle_value {N : ℕ} (ω : LogMoments.SignVector N)
    {c : ℂ} (hc : ‖c‖ = 1) {R : ℝ} (hR : 0 < R)
    (hlarge : (N + 1 : ℝ) / 2 ≤ ‖(rademacherPolynomial ω).eval c‖ ^ 2) :
    (zeroCountIn (rademacherPolynomial ω) (Metric.closedBall c R) : ℝ) ≤
      (Real.log (N + 1) / 2 + Real.log 2 / 2 + 2 * N * R) / Real.log 2 := by
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hnorm : 0 < ‖(rademacherPolynomial ω).eval c‖ := by
    by_contra! h
    have hz : ‖(rademacherPolynomial ω).eval c‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [hz] at hlarge
    nlinarith
  have hM : 1 ≤ (N + 1 : ℝ) * Real.exp (2 * N * R) := by
    have hexp : 1 ≤ Real.exp (2 * N * R) := Real.one_le_exp (by positivity)
    have hn : (1 : ℝ) ≤ N + 1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
    nlinarith
  have hbase := local_zero_count_bound (rademacherPolynomial ω) c hR (by linarith : R < 2 * R)
    hM (norm_pos_iff.mp hnorm) (fun z hz =>
      norm_eval_rademacherPolynomial_le_exp ω hc hR.le (Metric.sphere_subset_closedBall hz))
  have hloglarge : (Real.log (N + 1) - Real.log 2) / 2 ≤
      Real.log ‖(rademacherPolynomial ω).eval c‖ := by
    have h := Real.log_le_log (by positivity : 0 < (N + 1 : ℝ) / 2) hlarge
    rw [Real.log_div hN1.ne' (by norm_num), Real.log_pow] at h
    norm_num at h
    linarith
  rw [show (2 * R) / R = 2 by field_simp, Real.log_mul hN1.ne' (Real.exp_ne_zero _),
    Real.log_exp] at hbase
  apply hbase.trans
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  linarith


/-- Chord distance is bounded by angular distance measured in radians. -/
theorem circle_chord_le_angular_distance (θ φ : AddCircle (1 : ℝ)) :
    ‖(AddCircle.toCircle θ : ℂ) - (AddCircle.toCircle φ : ℂ)‖ ≤
      2 * Real.pi * dist θ φ := by
  have hone (x : ℝ) : ‖angularCharacter x - 1‖ ≤ 2 * Real.pi * |x - round x| := by
    rw [← angularCharacter_sub_int x (round x), angularCharacter_eq, unitCirclePoint]
    have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (x - round x))
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] using h
  induction θ using QuotientAddGroup.induction_on
  rename_i x
  induction φ using QuotientAddGroup.induction_on
  rename_i y
  have h := hone (x - y)
  rw [← norm_angularCharacter_sub] at h
  simpa only [angularCharacter, fourier_one, dist_eq_norm,
    ← AddCircle.coe_sub, UnitAddCircle.norm_eq] using h

/-- The equally spaced angular grid with `J` points. -/
def angularGrid (J : ℕ) (i : Fin J) : AddCircle (1 : ℝ) := ((i.val : ℝ) / J : ℝ)

/-- Every angle is within one grid spacing of an equally spaced angular grid. -/
theorem exists_near_angularGrid {J : ℕ} (hJ : 0 < J) (θ : AddCircle (1 : ℝ)) :
    ∃ i : Fin J, dist θ (angularGrid J i) ≤ 1 / (J : ℝ) := by
  let x : ℝ := AddCircle.equivIco (1 : ℝ) 0 θ
  have hx0 : 0 ≤ x := (AddCircle.equivIco (1 : ℝ) 0 θ).property.1
  have hx1 : x < 1 := by simpa using (AddCircle.equivIco (1 : ℝ) 0 θ).property.2
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hxJ0 : 0 ≤ (J : ℝ) * x := mul_nonneg hJ0.le hx0
  have hi : ⌊(J : ℝ) * x⌋₊ < J := (Nat.floor_lt hxJ0).mpr (by nlinarith)
  let i : Fin J := ⟨⌊(J : ℝ) * x⌋₊, hi⟩
  refine ⟨i, ?_⟩
  have hθ : (x : AddCircle (1 : ℝ)) = θ := AddCircle.coe_equivIco
  rw [← hθ, angularGrid, dist_eq_norm, ← AddCircle.coe_sub]
  apply QuotientAddGroup.norm_mk_le_norm.trans
  rw [Real.norm_eq_abs]
  have hf := Nat.abs_sub_floor_le hxJ0
  have heq : x - (i.val : ℝ) / J = ((J : ℝ) * x - ⌊(J : ℝ) * x⌋₊) / J := by
    dsimp [i]
    field_simp
  rw [heq, abs_div, abs_of_pos hJ0]
  exact div_le_div_of_nonneg_right hf hJ0.le

/-- Radial normalization moves a nonzero point exactly its distance in modulus to the unit circle. -/
theorem dist_normalize_eq {z : ℂ} (hz : z ≠ 0) :
    dist z (NormedSpace.normalize z) = |‖z‖ - 1| := by
  rw [dist_eq_norm]
  conv_lhs => arg 1; lhs; rw [← NormedSpace.norm_smul_normalize z]
  rw [show ‖z‖ • NormedSpace.normalize z - NormedSpace.normalize z =
    (‖z‖ - 1) • NormedSpace.normalize z by rw [sub_smul, one_smul]]
  rw [norm_smul, Real.norm_eq_abs, NormedSpace.norm_normalize hz, mul_one]


/-- A short angular cover and large values on its arcs control every nearby center. -/
theorem exists_large_value_near_center {N : ℕ} (ω : LogMoments.SignVector N)
    {ι : Type*} (θ : ι → AddCircle (1 : ℝ)) {h : ℝ} (_hh : 0 ≤ h)
    (hcover : ∀ φ, ∃ i, dist φ (θ i) ≤ h / (2 * Real.pi))
    (hvalues : ∀ i, ∃ t ∈ ArcEnergy.arc (θ i) h,
      (N + 1 : ℝ) / 2 ≤ ‖ArcEnergy.fourierSum (fun k => LogMoments.realSign (ω k)) t‖ ^ 2)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      dist z₀ c ≤ |‖z₀‖ - 1| + 2 * h ∧
      (N + 1 : ℝ) / 2 ≤ ‖(rademacherPolynomial ω).eval c‖ ^ 2 := by
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
  · simpa only [eval_rademacherPolynomial_circle] using hlarge

/-- The Jensen radius contains every target disk whenever the large center value is close enough. -/
theorem local_count_of_nearby_large_value {N : ℕ} (ω : LogMoments.SignVector N)
    {K h : ℝ} (hK : 0 ≤ K) (hh : 0 ≤ h) (hN : 0 < N)
    {z₀ c : ℂ} (hc : ‖c‖ = 1)
    (hdist : dist z₀ c ≤ 1 / (N : ℝ) + 2 * h)
    (hlarge : (N + 1 : ℝ) / 2 ≤ ‖(rademacherPolynomial ω).eval c‖ ^ 2) :
    (zeroCountIn (rademacherPolynomial ω) (Metric.closedBall z₀ (2 * K / N)) : ℝ) ≤
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
  have hcount : (zeroCountIn (rademacherPolynomial ω) (Metric.closedBall z₀ (2 * K / N)) : ℝ) ≤
      zeroCountIn (rademacherPolynomial ω) (Metric.closedBall c ((2 * K + 1) / N + 2 * h)) := by
    exact_mod_cast zeroCountIn_mono (rademacherPolynomial ω) hsub
  exact hcount.trans (zero_count_bound_of_large_circle_value ω hc hR hlarge)


/-- An explicit finite angular cover gives a simultaneous root-count estimate
under the actual product law of the Rademacher coefficients. -/
theorem simultaneous_local_count_of_cover (N : ℕ) (hN : 2 ≤ N)
    {ι : Type*} [Fintype ι] (θ : ι → AddCircle (1 : ℝ))
    (hcard : Fintype.card ι ≤ 8 * N)
    (hwidth : ArcEnergy.arcScale * Real.log N / N ≤ Real.pi)
    (hcover : ∀ φ, ∃ i, dist φ (θ i) ≤
      (ArcEnergy.arcScale * Real.log N / N) / (2 * Real.pi))
    {K : ℝ} (hK : 0 ≤ K) :
    (LogMoments.signMeasure N).real {ω | ∃ z₀ : ℂ,
      |‖z₀‖ - 1| ≤ 1 / (N : ℝ) ∧
      (Real.log (N + 1) / 2 + Real.log 2 / 2 +
        2 * N * ((2 * K + 1) / N + 2 * (ArcEnergy.arcScale * Real.log N / N))) / Real.log 2 <
      (zeroCountIn (rademacherPolynomial ω) (Metric.closedBall z₀ (2 * K / N)) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hh : 0 ≤ ArcEnergy.arcScale * Real.log N / N := by
    unfold ArcEnergy.arcScale
    positivity
  apply le_trans _ (ArcEnergy.simultaneous_large_values N hN θ hcard hwidth)
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  obtain ⟨z₀, hz₀, hcount⟩ := hω
  by_contra hfailure
  change ¬ ∃ i, ∀ t ∈ ArcEnergy.arc (θ i) (ArcEnergy.arcScale * Real.log N / N),
    ‖ArcEnergy.fourierSum (fun k => LogMoments.realSign (ω k)) t‖ ^ 2 ≤ (N + 1 : ℝ) / 2 at hfailure
  push Not at hfailure
  have hz₀ne : z₀ ≠ 0 := by
    intro hz
    have hbad : (1 : ℝ) ≤ 1 / N := by simpa [hz] using hz₀
    have := (le_div_iff₀ hN0).mp hbad
    nlinarith
  obtain ⟨c, hc, hdist, hlarge⟩ := exists_large_value_near_center ω θ hh hcover
    (fun i => by
      obtain ⟨t, ht, hv⟩ := hfailure i
      exact ⟨t, ht, hv.le⟩) hz₀ne
  have hdist' : dist z₀ c ≤ 1 / (N : ℝ) + 2 * (ArcEnergy.arcScale * Real.log N / N) := by
    exact hdist.trans (add_le_add hz₀ le_rfl)
  have hbound := local_count_of_nearby_large_value ω hK hh (by omega) hc hdist' hlarge
  exact (not_lt_of_ge hbound) hcount

/-- The constant in the simultaneous local root-count estimate. -/
def localCountConstant (K : ℝ) : ℝ :=
  (4 * ArcEnergy.arcScale + 4 * K + 4) / Real.log 2

/-- The short-arc condition itself puts the degree in the logarithmic regime. -/
theorem one_le_log_of_arcWidth_le_one {N : ℕ} (hN : 2 ≤ N)
    (hwidth : ArcEnergy.arcScale * Real.log N / N ≤ 1) :
    1 ≤ Real.log (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log (N : ℝ) :=
    (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hN2)
  have hlarge := (div_le_one₀ hN0).mp hwidth
  have hscale : 6 ≤ ArcEnergy.arcScale := by
    unfold ArcEnergy.arcScale
    nlinarith [Real.two_le_pi]
  have hN3 : (3 : ℝ) ≤ N := by nlinarith
  exact (Real.le_log_iff_exp_le hN0).mpr (Real.exp_one_lt_three.le.trans hN3)

/-- The ceiling grid at the logarithmic arc scale uses at most `N` angles. -/
theorem exists_logarithmic_angular_cover {N : ℕ} (hN : 2 ≤ N)
    (hlog : 1 ≤ Real.log (N : ℝ)) :
    ∃ J : ℕ, J ≤ 8 * N ∧ ∀ φ : AddCircle (1 : ℝ),
      ∃ i : Fin J, dist φ (angularGrid J i) ≤
        (ArcEnergy.arcScale * Real.log N / N) / (2 * Real.pi) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hscale : 0 < ArcEnergy.arcScale := by unfold ArcEnergy.arcScale; positivity
  let h := ArcEnergy.arcScale * Real.log N / N
  have hh : 0 < h := by dsimp [h]; positivity
  let J := ⌈2 * Real.pi / h⌉₊
  have hJ : 0 < J := Nat.ceil_pos.mpr (by positivity)
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJN : J ≤ N := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hh).mpr
    dsimp [h]
    rw [mul_div_cancel₀ _ hN0.ne']
    unfold ArcEnergy.arcScale
    nlinarith [Real.pi_pos]
  refine ⟨J, hJN.trans (by omega), fun φ => ?_⟩
  obtain ⟨i, hi⟩ := exists_near_angularGrid hJ φ
  refine ⟨i, hi.trans ?_⟩
  have hc : 2 * Real.pi / h ≤ (J : ℝ) := Nat.le_ceil _
  have hc' := (div_le_iff₀ hh).mp hc
  apply (div_le_div_iff₀ hJr (by positivity : 0 < 2 * Real.pi)).mpr
  dsimp [h] at hc' ⊢
  nlinarith

/-- The exact Jensen quotient is bounded by the displayed logarithmic constant. -/
theorem local_jensen_quotient_le {N : ℕ} (hN : 2 ≤ N)
    (hlog : 1 ≤ Real.log (N : ℝ)) {K : ℝ} (hK : 0 ≤ K) :
    (Real.log (N + 1) / 2 + Real.log 2 / 2 +
      2 * N * ((2 * K + 1) / N + 2 * (ArcEnergy.arcScale * Real.log N / N))) /
      Real.log 2 ≤ localCountConstant K * Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogNp : Real.log (N + 1 : ℝ) ≤ Real.log (N : ℝ) + Real.log 2 := by
    calc
      _ ≤ Real.log ((N : ℝ) * 2) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := Real.log_mul hN0.ne' (by norm_num)
  have heq : 2 * (N : ℝ) * ((2 * K + 1) / N +
      2 * (ArcEnergy.arcScale * Real.log N / N)) =
      4 * K + 2 + 4 * ArcEnergy.arcScale * Real.log N := by field_simp; ring
  rw [heq, localCountConstant, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  nlinarith [mul_nonneg (by linarith : 0 ≤ 4 * K + 3) (sub_nonneg.mpr hlog)]

/-- Every disk of radius `2K/N` centered within `1/N` of the unit circle has at
most `localCountConstant K * log N` zeros, counted with multiplicity, outside an
event of probability at most `N⁻³`. -/
theorem simultaneous_local_zero_count (N : ℕ) (hN : 2 ≤ N)
    (hwidth : ArcEnergy.arcScale * Real.log N / N ≤ 1)
    {K : ℝ} (hK : 0 ≤ K) :
    (LogMoments.signMeasure N).real {ω | ∃ z₀ : ℂ,
      |‖z₀‖ - 1| ≤ 1 / (N : ℝ) ∧
      localCountConstant K * Real.log N <
        (zeroCountIn (rademacherPolynomial ω) (Metric.closedBall z₀ (2 * K / N)) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 := by
  have hlog := one_le_log_of_arcWidth_le_one hN hwidth
  obtain ⟨J, hJ, hcover⟩ := exists_logarithmic_angular_cover hN hlog
  have hbase := simultaneous_local_count_of_cover N hN (angularGrid J)
    (by simpa using hJ) (hwidth.trans (by linarith [Real.two_le_pi])) hcover hK
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hbase
  intro ω hω
  obtain ⟨z₀, hz₀, hcount⟩ := hω
  exact ⟨z₀, hz₀, lt_of_le_of_lt (local_jensen_quotient_le hN hlog hK) hcount⟩

end LocalZeroCount
end Erdos522

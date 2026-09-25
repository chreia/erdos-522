/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.HarmonicRestriction
import Erdos522.Probability.LogarithmicConcentrationRate
import Erdos522.Probability.RealPowerConcentration
import Erdos522.Limits.SparseDegreeParameters

/-!
# Adjustable power rates for logarithmic concentration

Clipping at height `t log N`, with occupation threshold `N^(-2t)`, gives a
logarithmic-integral error of order `N^(-t) (log N)^6`. The three exceptional
probabilities keep their individual powers. This permits every sparse degree
exponent greater than two after choosing a sufficiently small positive `t`.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522
open LogMoments

/-- The square-integral cutoff at logarithmic moment order `6 log N`. -/
def powerLogarithmicMomentCutoff (A : ℝ) (N : ℕ) : ℝ :=
  Real.exp 1 * (12 * A * Real.log N) ^ 6

/-- A finite tolerance for the adjustable logarithmic concentration estimate. -/
def logarithmicPowerTolerance (t A H : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (-t) * (5 / 2 + 2 * t * H * Real.log N +
    powerLogarithmicMomentCutoff A N * Real.sqrt (2 + H))

/-- The three exceptional-probability terms at a general clipping exponent. -/
def logarithmicPowerFailure (t H : ℝ) (N : ℕ) : ℝ :=
  H * (N : ℝ) ^ (-1 / 2 + 4 * t) + (N : ℝ) ^ (-12 : ℝ) +
    4 * t ^ 2 * H * (N : ℝ) ^ (-1 / 2 + 2 * t) * (Real.log N) ^ 2

theorem power_logarithmic_moment_cutoff_failure {N : ℕ} (hN : 1 < N)
    {A : ℝ} (hA : 0 < A) :
    (A * (2 * (6 * Real.log N))) ^ (12 * (6 * Real.log N)) /
      (powerLogarithmicMomentCutoff A N ^ 2) ^ (6 * Real.log N) =
        (N : ℝ) ^ (-12 : ℝ) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hlog := Real.log_pos hn
  have hc : 0 < 12 * A * Real.log N := by positivity
  have h := logarithmic_moment_failure_identity (Real.exp 1)
    (12 * A * Real.log N) 6 (6 * Real.log N) (Real.exp_pos _) hc
  rw [show (12 * A * Real.log N) ^ (6 : ℝ) = (12 * A * Real.log N) ^ (6 : ℕ) from
    Real.rpow_natCast _ 6] at h
  unfold powerLogarithmicMomentCutoff
  calc
    _ = Real.exp 1 ^ (-2 * (6 * Real.log N)) := by
      simpa only [show A * (2 * (6 * Real.log N)) = 12 * A * Real.log N by ring,
        show (2 * 6 : ℝ) = 12 by norm_num] using h
    _ = _ := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
        Real.rpow_def_of_pos (by linarith : (0 : ℝ) < N)]
      congr 1
      ring

theorem power_logarithmic_clipping_exp {x : ℝ} (hx : 0 < x) (t : ℝ) :
    Real.exp (-2 * (t * Real.log x)) = x ^ (-2 * t) := by
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- The lower-tail occupation mass has square root of order `N^(-t)`. -/
theorem power_logarithmic_clipping_sqrt_le {x t H : ℝ}
    (hx : 1 ≤ x) (ht : t ≤ 1 / 4) (hH : 0 ≤ H) :
    Real.sqrt (Real.exp (-2 * (t * Real.log x)) + H / Real.sqrt x + x ^ (-2 * t)) ≤
      Real.sqrt (2 + H) * x ^ (-t) := by
  have hxp : 0 < x := by linarith
  have herror : H / Real.sqrt x ≤ H * x ^ (-2 * t) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hxp.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) hH
  rw [power_logarithmic_clipping_exp hxp]
  calc
    _ ≤ Real.sqrt ((2 + H) * x ^ (-2 * t)) := by
      apply Real.sqrt_le_sqrt
      linarith
    _ = _ := by
      rw [Real.sqrt_mul (by linarith), Real.sqrt_eq_rpow (x ^ (-2 * t)),
        ← Real.rpow_mul hxp.le]
      congr 2
      ring

/-- The complete finite clipping threshold lies below the adjustable tolerance. -/
theorem logarithmic_power_threshold_le {N : ℕ} (hN : 1 ≤ N)
    {t A H : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) (hH : 0 ≤ H) :
    (N : ℝ) ^ (-t) + 2 * (t * Real.log N) * (H / Real.sqrt N) +
      powerLogarithmicMomentCutoff A N * Real.sqrt
        (Real.exp (-2 * (t * Real.log N)) + H / Real.sqrt N + (N : ℝ) ^ (-2 * t)) +
      (3 / 2 : ℝ) * Real.exp (-2 * (t * Real.log N)) ≤
        logarithmicPowerTolerance t A H N := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hn1
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hn1
  have herror : H / Real.sqrt N ≤ H * (N : ℝ) ^ (-t) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hn.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) hH
  have hbias := mul_le_mul_of_nonneg_left herror
    (show 0 ≤ 2 * (t * Real.log N) by positivity)
  have htail := mul_le_mul_of_nonneg_left
    (power_logarithmic_clipping_sqrt_le hn1 ht hH)
    (show 0 ≤ powerLogarithmicMomentCutoff A N by unfold powerLogarithmicMomentCutoff; positivity)
  have hpos : (3 / 2 : ℝ) * Real.exp (-2 * (t * Real.log N)) ≤
      (3 / 2 : ℝ) * (N : ℝ) ^ (-t) := by
    rw [power_logarithmic_clipping_exp hn]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  unfold logarithmicPowerTolerance
  nlinarith only [hbias, htail, hpos]

/-- Exact powers in the occupation and truncated-logarithm variance terms. -/
theorem logarithmic_power_failure_identity {N : ℕ} (hN : 1 < N)
    {A : ℝ} (hA : 0 < A) (t H : ℝ) :
    (H / Real.sqrt N) / ((N : ℝ) ^ (-2 * t)) ^ 2 +
      (A * (2 * (6 * Real.log N))) ^ (12 * (6 * Real.log N)) /
        (powerLogarithmicMomentCutoff A N ^ 2) ^ (6 * Real.log N) +
      4 * (t * Real.log N) ^ 2 * (H / Real.sqrt N) / ((N : ℝ) ^ (-t)) ^ 2 =
        logarithmicPowerFailure t H N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have he : H / Real.sqrt N = H * (N : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hn.le]
    congr 2
    ring
  have hp (a : ℝ) : ((N : ℝ) ^ a) ^ 2 = (N : ℝ) ^ (2 * a) := by
    rw [← Real.rpow_mul_natCast hn.le]
    congr 1
    ring
  rw [power_logarithmic_moment_cutoff_failure hN hA, he, hp, hp]
  have h₁ : (N : ℝ) ^ (-1 / 2 : ℝ) / (N : ℝ) ^ (2 * (-2 * t)) =
      (N : ℝ) ^ (-1 / 2 + 4 * t) := by rw [← Real.rpow_sub hn]; congr 1; ring
  have h₂ : (N : ℝ) ^ (-1 / 2 : ℝ) / (N : ℝ) ^ (2 * (-t)) =
      (N : ℝ) ^ (-1 / 2 + 2 * t) := by rw [← Real.rpow_sub hn]; congr 1; ring
  calc
    _ = H * ((N : ℝ) ^ (-1 / 2 : ℝ) / (N : ℝ) ^ (2 * (-2 * t))) +
        (N : ℝ) ^ (-12 : ℝ) + 4 * t ^ 2 * H *
          ((N : ℝ) ^ (-1 / 2 : ℝ) / (N : ℝ) ^ (2 * (-t))) * (Real.log N) ^ 2 := by ring
    _ = _ := by rw [h₁, h₂]; rfl

/-- The finite constants are uniform in the radius throughout a fixed annulus. -/
theorem exists_rademacher_logarithmic_power_concentration :
    ∃ B : ℝ, 0 < B ∧ ∀ (t : ℝ), 0 < t → t ≤ 1 / 4 →
      ∀ K : ℝ, 0 ≤ K → ∀ᶠ N : ℕ in atTop,
      ∀ r : ℝ, 1 - K / N ≤ r → r ≤ 1 + K / N →
        (signMeasure N).real {ω |
          logarithmicPowerTolerance t (fourierLogarithmicConstant harmonicRestrictionConstant)
            (rademacherOccupationConstant B K) N <
          |logCircleAverage (rademacherPolynomial N ω) r - Real.log (radialSigma N r) - circularLogMean|} ≤
            logarithmicPowerFailure t (rademacherOccupationConstant B K) N := by
  obtain ⟨B, hB, hbound⟩ := exists_rademacher_logarithmic_concentration_constant
    one_le_harmonicRestrictionConstant harmonic_l2_restriction
  refine ⟨B, hB, ?_⟩
  intro t ht0 ht K hK
  let H := rademacherOccupationConstant B K
  let A := fourierLogarithmicConstant harmonicRestrictionConstant
  have hH : 0 < H := rademacherOccupationConstant_pos B K
  have hA : 0 < A := fourierLogarithmicConstant_pos one_le_harmonicRestrictionConstant
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * K),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((6400 * Real.exp (8 * K)) ^ 2),
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1]
      with N hN hNK hdegree hlog
  change 1 ≤ Real.log N at hlog
  intro r hrl hru
  have hn : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hn
  have hD : 0 < powerLogarithmicMomentCutoff A N := by
    unfold powerLogarithmicMomentCutoff
    have hl : 0 < Real.log N := by linarith
    positivity
  have hthreshold := logarithmic_power_threshold_le (by omega : 1 ≤ N) ht0.le ht hH.le (A := A)
  have h := hbound N hn K r hK hNK hrl hru hdegree (6 * Real.log N) (by linarith)
    (t * Real.log N) ((N : ℝ) ^ (-t)) ((N : ℝ) ^ (-2 * t))
    (powerLogarithmicMomentCutoff A N) (by positivity)
    (Real.rpow_pos_of_pos hNr _) (Real.rpow_pos_of_pos hNr _) hD
  have hprob := (measure_mono (μ := signMeasure N) (show
      {ω | logarithmicPowerTolerance t A H N <
        |logCircleAverage (rademacherPolynomial N ω) r - Real.log (radialSigma N r) - circularLogMean|} ⊆
      {ω | (N : ℝ) ^ (-t) + 2 * (t * Real.log N) * (H / Real.sqrt N) +
        powerLogarithmicMomentCutoff A N * Real.sqrt
          (Real.exp (-2 * (t * Real.log N)) + H / Real.sqrt N + (N : ℝ) ^ (-2 * t)) +
        (3 / 2 : ℝ) * Real.exp (-2 * (t * Real.log N)) <
          |logCircleAverage (rademacherPolynomial N ω) r - Real.log (radialSigma N r) - circularLogMean|}
      from fun _ hω => lt_of_le_of_lt hthreshold hω)).trans h
  rw [logarithmic_power_failure_identity (by omega : 1 < N) hA] at hprob
  have hnneg : 0 ≤ logarithmicPowerFailure t H N := by unfold logarithmicPowerFailure; positivity
  dsimp only [H] at hnneg
  simpa only [measureReal_def, ENNReal.toReal_ofReal hnneg] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob

/-- The tolerance remains negligible after division by a thinner radial scale. -/
theorem tendsto_rpow_mul_logarithmicPowerTolerance {t κ : ℝ} (hκ : κ < t) (A H : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ κ * logarithmicPowerTolerance t A H N)
      atTop (𝓝 0) := by
  have hlim (k : ℕ) : Tendsto (fun N : ℕ =>
      (N : ℝ) ^ (κ - t) * (Real.log N) ^ k) atTop (𝓝 0) := by
    have h := tendsto_log_pow_div_nat_rpow k (show 0 < t - κ by linarith)
    apply h.congr
    intro N
    rw [show κ - t = -(t - κ) by ring, Real.rpow_neg (Nat.cast_nonneg _)]
    ring
  have h := ((hlim 0).const_mul (5 / 2 : ℝ) |>.add
    ((hlim 1).const_mul (2 * t * H))).add
      ((hlim 6).const_mul (Real.exp 1 * (12 * A) ^ 6 * Real.sqrt (2 + H)))
  simp only [mul_zero, add_zero, pow_zero, mul_one, pow_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold logarithmicPowerTolerance powerLogarithmicMomentCutoff
  rw [show (N : ℝ) ^ κ * ((N : ℝ) ^ (-t) *
      (5 / 2 + 2 * t * H * Real.log N +
        Real.exp 1 * (12 * A * Real.log N) ^ 6 * Real.sqrt (2 + H))) =
      ((N : ℝ) ^ κ * (N : ℝ) ^ (-t)) *
        (5 / 2 + 2 * t * H * Real.log N +
          Real.exp 1 * (12 * A * Real.log N) ^ 6 * Real.sqrt (2 + H)) by ring,
    ← Real.rpow_add hn]
  rw [show κ + -t = κ - t by ring]
  ring

theorem tendsto_logarithmicPowerTolerance {t : ℝ} (ht : 0 < t) (A H : ℝ) :
    Tendsto (logarithmicPowerTolerance t A H) atTop (𝓝 0) := by
  simpa only [Real.rpow_zero, one_mul] using tendsto_rpow_mul_logarithmicPowerTolerance ht A H

/-- The exact three-term failure budget is summable at every admissible degree exponent. -/
theorem summable_logarithmicPowerFailure {q t : ℝ} (hq : 2 < q) (ht : 0 < t)
    (hs : 1 < q * (1 / 2 - 4 * t)) (H : ℝ) :
    Summable (fun j : ℕ => logarithmicPowerFailure t H (realPowerDegree q j)) := by
  have hq0 : 0 < q := by linarith
  have h₁ := (summable_realPowerDegree_rpow hq0
    (show q * (-1 / 2 + 4 * t) < -1 by nlinarith)).mul_left H
  have h₂ := summable_realPowerDegree_rpow hq0 (show q * (-12 : ℝ) < -1 by linarith)
  have h₃ := (summable_realPowerDegree_rpow_mul_log_pow hq0
    (show q * (-1 / 2 + 2 * t) < -1 from
      lt_trans (by nlinarith [mul_pos hq0 ht] : q * (-1 / 2 + 2 * t) < q * (-1 / 2 + 4 * t))
        (by nlinarith [hs])) 2).mul_left (4 * t ^ 2 * H)
  apply (h₁.add h₂ |>.add h₃).congr
  intro j
  unfold logarithmicPowerFailure
  ring

/-- Actual almost-sure logarithmic control for every admissible clipping power,
simultaneously on a fixed finite family of radii. -/
theorem exists_ae_real_power_logarithmic_power_bound {q t : ℝ} (hq : 2 < q) (ht : 0 < t)
    (hs : 1 < q * (1 / 2 - 4 * t)) {ι : Type*} [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) (r : ℕ → ι → ℝ)
    (hr : ∀ᶠ N : ℕ in atTop, ∀ i, 1 - K / N ≤ r N i ∧ r N i ≤ 1 + K / N) :
    ∃ H : ℝ, 0 < H ∧ ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop, ∀ i,
      |logCircleAverage (rademacherPolynomial (realPowerDegree q j)
          (rademacherPrefix (realPowerDegree q j) ω)) (r (realPowerDegree q j) i) -
        Real.log (radialSigma (realPowerDegree q j) (r (realPowerDegree q j) i)) -
          circularLogMean| ≤ logarithmicPowerTolerance t
            (fourierLogarithmicConstant harmonicRestrictionConstant) H (realPowerDegree q j) := by
  have hq0 : 0 < q := by linarith
  have ht4 : t ≤ 1 / 4 := by
    by_contra h
    have hnegative : 1 / 2 - 4 * t < 0 := by linarith
    have := mul_neg_of_pos_of_neg hq0 hnegative
    linarith
  obtain ⟨B, _, hbound⟩ := exists_rademacher_logarithmic_power_concentration
  let H := rademacherOccupationConstant B K
  let A := fourierLogarithmicConstant harmonicRestrictionConstant
  let E (N : ℕ) : Set (SignVector N) := {v | ∃ i,
    logarithmicPowerTolerance t A H N <
      |logCircleAverage (rademacherPolynomial N v) (r N i) -
        Real.log (radialSigma N (r N i)) - circularLogMean|}
  have hprob : ∀ᶠ N : ℕ in atTop, (signMeasure N).real (E N) ≤
      (Fintype.card ι : ℝ) * logarithmicPowerFailure t H N := by
    filter_upwards [hbound t ht ht4 K hK, hr] with N hN hrN
    have heq : E N = ⋃ i, {v | logarithmicPowerTolerance t A H N <
        |logCircleAverage (rademacherPolynomial N v) (r N i) -
          Real.log (radialSigma N (r N i)) - circularLogMean|} := by ext v; simp [E]
    rw [heq]
    calc
      _ ≤ ∑ i, (signMeasure N).real {v | logarithmicPowerTolerance t A H N <
          |logCircleAverage (rademacherPolynomial N v) (r N i) -
            Real.log (radialSigma N (r N i)) - circularLogMean|} := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : ι, logarithmicPowerFailure t H N :=
        Finset.sum_le_sum fun i _ => hN (r N i) (hrN i).1 (hrN i).2
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum : Summable (fun j : ℕ => (signMeasure (realPowerDegree q j)).real (E (realPowerDegree q j))) := by
    apply ((summable_logarithmicPowerFailure hq ht hs H).mul_left (Fintype.card ι : ℝ)).of_norm_bounded_eventually_nat
    filter_upwards [(tendsto_realPowerDegree hq0).eventually hprob] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact hj
  refine ⟨H, rademacherOccupationConstant_pos B K, ?_⟩
  filter_upwards [ae_eventually_rademacherPrefix_notMem (realPowerDegree q) E hsum] with ω hω
  filter_upwards [hω] with j hj
  intro i
  exact le_of_not_gt (fun hlarge => hj ⟨i, hlarge⟩)

end Erdos522

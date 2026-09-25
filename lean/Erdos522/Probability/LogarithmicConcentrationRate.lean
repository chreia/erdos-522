/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.RademacherLogarithmicConcentration
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A polynomial logarithmic-concentration rate

The moment order is `log N`. The square-integral cutoff has order
`(log N)^6`, leaving a logarithmic margin inside the tolerance
`N^(-1/32) (log N)^7`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Erdos522
open LogMoments

/-- The logarithmic-integral tolerance used in radial Jensen secants. -/
def logarithmicTolerance (N : ℕ) : ℝ :=
  (N : ℝ) ^ (-1 / 32 : ℝ) * (Real.log N) ^ 7

/-- The logarithmic square-integral cutoff at moment order `log N`. -/
def logarithmicMomentCutoff (A : ℝ) (N : ℕ) : ℝ :=
  Real.exp 6 * (2 * A * Real.log N) ^ 6

theorem logarithmicTolerance_pos {N : ℕ} (hN : 1 < N) :
    0 < logarithmicTolerance N := by
  unfold logarithmicTolerance
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos (Real.log_pos hn) _)

/-- The moment cutoff makes the moment failure exactly `N^(-12)`. -/
theorem logarithmic_moment_cutoff_failure {N : ℕ} (hN : 1 < N)
    {A : ℝ} (hA : 0 < A) :
    (A * (2 * Real.log N)) ^ (12 * Real.log N) /
      (logarithmicMomentCutoff A N ^ 2) ^ Real.log N = (N : ℝ) ^ (-12 : ℝ) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hlog := Real.log_pos hn
  have hc : 0 < 2 * A * Real.log N := by positivity
  have h := logarithmic_moment_failure_identity (Real.exp 6)
    (2 * A * Real.log N) 6 (Real.log N) (Real.exp_pos _) hc
  rw [show (2 * A * Real.log N) ^ (6 : ℝ) = (2 * A * Real.log N) ^ (6 : ℕ) from
    Real.rpow_natCast _ 6] at h
  unfold logarithmicMomentCutoff
  calc
    _ = Real.exp 6 ^ (-2 * Real.log N) := by
      simpa only [show (2 * 6 : ℝ) = 12 by norm_num,
        show A * (2 * Real.log N) = 2 * A * Real.log N by ring] using h
    _ = _ := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
        Real.rpow_def_of_pos (by linarith : (0 : ℝ) < N)]
      congr 1
      ring

/-- The lower clipping level has its exact power-law mass. -/
theorem logarithmic_clipping_exp {x : ℝ} (hx : 0 < x) :
    Real.exp (-2 * (Real.log x / 32)) = x ^ (-1 / 16 : ℝ) := by
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- An inverse square root is bounded by the lower clipping mass. -/
theorem logarithmic_occupation_error_le {x H : ℝ} (hx : 1 ≤ x) (hH : 0 ≤ H) :
    H / Real.sqrt x ≤ H * x ^ (-1 / 16 : ℝ) := by
  have heq : H / Real.sqrt x = H * x ^ (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg (by linarith : 0 ≤ x)]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx (by norm_num)) hH

/-- The low-value Cauchy--Schwarz term separates into a constant and `N^(-1/32)`. -/
theorem logarithmic_clipping_mass_sqrt_le {x H : ℝ} (hx : 1 ≤ x) (hH : 0 ≤ H) :
    Real.sqrt (Real.exp (-2 * (Real.log x / 32)) + H / Real.sqrt x +
      x ^ (-1 / 16 : ℝ)) ≤ Real.sqrt (2 + H) * x ^ (-1 / 32 : ℝ) := by
  have hxp : 0 < x := by linarith
  rw [logarithmic_clipping_exp hxp]
  calc
    _ ≤ Real.sqrt ((2 + H) * x ^ (-1 / 16 : ℝ)) := by
      apply Real.sqrt_le_sqrt
      linarith [logarithmic_occupation_error_le hx hH]
    _ = _ := by
      rw [Real.sqrt_mul (by linarith : 0 ≤ 2 + H)]
      simp only [Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul hxp.le]
      norm_num

/-- Exact simplification of the occupation and clipping failure terms. -/
theorem logarithmic_probability_scale_identity {N : ℕ} (hN : 1 < N) (H : ℝ) :
    (H / Real.sqrt N) / ((N : ℝ) ^ (-1 / 16 : ℝ)) ^ 2 =
      H * (N : ℝ) ^ (-3 / 8 : ℝ) ∧
    4 * (Real.log N / 32) ^ 2 * (H / Real.sqrt N) /
      (logarithmicTolerance N / 2) ^ 2 =
      H / 64 * (N : ℝ) ^ (-7 / 16 : ℝ) / (Real.log N) ^ 12 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have hp (a : ℝ) : ((N : ℝ) ^ a) ^ 2 = (N : ℝ) ^ (2 * a) := by
    rw [← Real.rpow_mul_natCast hn.le]
    congr 1
    ring
  have he : (H / Real.sqrt N) = H * (N : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hn.le]
    ring
  rw [he, hp]
  constructor
  · rw [mul_div_assoc, ← Real.rpow_sub hn]
    norm_num
  · unfold logarithmicTolerance
    simp only [div_pow, mul_pow]
    rw [hp]
    have hquot : (N : ℝ) ^ (-1 / 2 : ℝ) / (N : ℝ) ^ (2 * (-1 / 32 : ℝ)) =
        (N : ℝ) ^ (-7 / 16 : ℝ) := by
      rw [← Real.rpow_sub hn]
      norm_num
    calc
      _ = H / 64 * ((N : ℝ) ^ (-1 / 2 : ℝ) /
          (N : ℝ) ^ (2 * (-1 / 32 : ℝ))) / (Real.log N) ^ 12 := by
        field_simp
        ring
      _ = _ := by rw [hquot]

/-- The three nonfluctuation errors relative to the logarithmic tolerance. -/
def logarithmicRelativeError (A H : ℝ) (N : ℕ) : ℝ :=
  H / 16 * (N : ℝ) ^ (-15 / 32 : ℝ) +
    Real.exp 6 * (2 * A) ^ 6 * Real.sqrt (2 + H) / Real.log N +
    (3 / 2 : ℝ) * (N : ℝ) ^ (-1 / 32 : ℝ)

/-- Every relative error tends to zero at fixed moment and occupation constants. -/
theorem tendsto_logarithmicRelativeError (A H : ℝ) :
    Tendsto (logarithmicRelativeError A H) atTop (𝓝 0) := by
  unfold logarithmicRelativeError
  have h₁ := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 15 / 32)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h₂ := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
  have h₃ := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 32)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa [Function.comp_def, div_eq_mul_inv] using
    ((h₁.const_mul (H / 16)).add
      (h₂.const_mul (Real.exp 6 * (2 * A) ^ 6 * Real.sqrt (2 + H)))).add
        (h₃.const_mul (3 / 2 : ℝ))

/-- The finite clipping threshold is bounded by the tolerance and a vanishing relative error. -/
theorem logarithmic_threshold_le {N : ℕ} (hlog : 1 ≤ Real.log N)
    {A H : ℝ} (hH : 0 ≤ H) :
    logarithmicTolerance N / 2 + 2 * (Real.log N / 32) * (H / Real.sqrt N) +
        logarithmicMomentCutoff A N * Real.sqrt
          (Real.exp (-2 * (Real.log N / 32)) + H / Real.sqrt N + (N : ℝ) ^ (-1 / 16 : ℝ)) +
        (3 / 2 : ℝ) * Real.exp (-2 * (Real.log N / 32)) ≤
      logarithmicTolerance N / 2 + logarithmicRelativeError A H N * logarithmicTolerance N := by
  have hn1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  have hn : (0 : ℝ) < N := by linarith
  have hl : Real.log N ≠ 0 := ne_of_gt (by linarith)
  have hl7 : Real.log N ≤ (Real.log N) ^ 7 := by
    simpa only [pow_one] using pow_le_pow_right₀ hlog (show 1 ≤ 7 by norm_num)
  have hp7 : 1 ≤ (Real.log N) ^ 7 := one_le_pow₀ hlog
  have hpow (a b : ℝ) : (N : ℝ) ^ a * (N : ℝ) ^ b = (N : ℝ) ^ (a + b) :=
    (Real.rpow_add hn _ _).symm
  have hden : H / Real.sqrt N = H * (N : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hn.le]
    ring
  have hbias : 2 * (Real.log N / 32) * (H / Real.sqrt N) ≤
      (H / 16 * (N : ℝ) ^ (-15 / 32 : ℝ)) * logarithmicTolerance N := by
    rw [hden]
    calc
      _ ≤ H / 16 * (N : ℝ) ^ (-1 / 2 : ℝ) * (Real.log N) ^ 7 := by
        convert mul_le_mul_of_nonneg_left hl7
          (show 0 ≤ H / 16 * (N : ℝ) ^ (-1 / 2 : ℝ) by positivity) using 1
        ring
      _ = _ := by
        unfold logarithmicTolerance
        rw [show H / 16 * (N : ℝ) ^ (-15 / 32 : ℝ) *
            ((N : ℝ) ^ (-1 / 32 : ℝ) * Real.log N ^ 7) =
          H / 16 * ((N : ℝ) ^ (-15 / 32 : ℝ) * (N : ℝ) ^ (-1 / 32 : ℝ)) *
            Real.log N ^ 7 by ring, hpow]
        norm_num
  have htail : logarithmicMomentCutoff A N * Real.sqrt
        (Real.exp (-2 * (Real.log N / 32)) + H / Real.sqrt N + (N : ℝ) ^ (-1 / 16 : ℝ)) ≤
      (Real.exp 6 * (2 * A) ^ 6 * Real.sqrt (2 + H) / Real.log N) * logarithmicTolerance N := by
    refine (mul_le_mul_of_nonneg_left (logarithmic_clipping_mass_sqrt_le hn1.le hH)
      (show 0 ≤ logarithmicMomentCutoff A N by unfold logarithmicMomentCutoff; positivity)).trans_eq ?_
    unfold logarithmicMomentCutoff logarithmicTolerance
    field_simp
  have hpos : (3 / 2 : ℝ) * Real.exp (-2 * (Real.log N / 32)) ≤
      ((3 / 2 : ℝ) * (N : ℝ) ^ (-1 / 32 : ℝ)) * logarithmicTolerance N := by
    rw [logarithmic_clipping_exp hn]
    calc
      _ ≤ (3 / 2 : ℝ) * (N : ℝ) ^ (-1 / 16 : ℝ) * (Real.log N) ^ 7 := by
        convert mul_le_mul_of_nonneg_left hp7
          (show 0 ≤ (3 / 2 : ℝ) * (N : ℝ) ^ (-1 / 16 : ℝ) by positivity) using 1
        ring
      _ = _ := by
        unfold logarithmicTolerance
        rw [show (3 / 2 : ℝ) * (N : ℝ) ^ (-1 / 32 : ℝ) *
            ((N : ℝ) ^ (-1 / 32 : ℝ) * Real.log N ^ 7) =
          (3 / 2 : ℝ) * ((N : ℝ) ^ (-1 / 32 : ℝ) * (N : ℝ) ^ (-1 / 32 : ℝ)) *
            Real.log N ^ 7 by ring, hpow]
        norm_num
  dsimp only [logarithmicRelativeError]
  nlinarith only [hbias, htail, hpos]

/-- The combined finite failure budget is bounded by a single summable power. -/
theorem logarithmic_failure_le {N : ℕ} (hlog : 1 ≤ Real.log N)
    {A H : ℝ} (hA : 0 < A) (hH : 0 ≤ H) :
    (H / Real.sqrt N) / ((N : ℝ) ^ (-1 / 16 : ℝ)) ^ 2 +
      (A * (2 * Real.log N)) ^ (12 * Real.log N) /
        (logarithmicMomentCutoff A N ^ 2) ^ Real.log N +
      4 * (Real.log N / 32) ^ 2 * (H / Real.sqrt N) / (logarithmicTolerance N / 2) ^ 2 ≤
      (2 * H + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) := by
  have hn1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  have hN : 1 < N := by exact_mod_cast hn1
  rw [(logarithmic_probability_scale_identity hN H).1,
    logarithmic_moment_cutoff_failure hN hA, (logarithmic_probability_scale_identity hN H).2]
  have hmoment : (N : ℝ) ^ (-12 : ℝ) ≤ (N : ℝ) ^ (-3 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1.le (by norm_num)
  have hclip : H / 64 * (N : ℝ) ^ (-7 / 16 : ℝ) / (Real.log N) ^ 12 ≤
      H * (N : ℝ) ^ (-3 / 8 : ℝ) := by
    calc
      _ ≤ H / 64 * (N : ℝ) ^ (-7 / 16 : ℝ) :=
        div_le_self (by positivity) (one_le_pow₀ hlog)
      _ ≤ H / 64 * (N : ℝ) ^ (-3 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hn1.le (by norm_num)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  linarith

/-- Uniformity in the radius is retained while all scalar thresholds are absorbed
into a finite initial degree. -/
theorem exists_eventually_rademacher_logarithmic_concentration {C : ℝ}
    (hC : 1 ≤ C) (hR : HarmonicL2Restriction C) :
    ∃ B : ℝ, 0 < B ∧ ∀ K : ℝ, 0 ≤ K → ∀ᶠ N : ℕ in atTop,
      ∀ r : ℝ, 1 - K / N ≤ r → r ≤ 1 + K / N →
        (signMeasure N).real {ω | logarithmicTolerance N <
          |logCircleAverage (rademacherPolynomial N ω) r - Real.log (radialSigma N r) - circularLogMean|} ≤
          (2 * rademacherOccupationConstant B K + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) := by
  obtain ⟨B, hB, hbound⟩ := exists_rademacher_logarithmic_concentration_constant hC hR
  refine ⟨B, hB, ?_⟩
  intro K hK
  let H := rademacherOccupationConstant B K
  let A := fourierLogarithmicConstant C
  have hH : 0 < H := rademacherOccupationConstant_pos B K
  have hA : 0 < A := fourierLogarithmicConstant_pos hC
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * K),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((6400 * Real.exp (8 * K)) ^ 2),
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1,
    (tendsto_logarithmicRelativeError A H).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)]
      with N hN hNK hdegree hlog herror
  change 1 ≤ Real.log N at hlog
  intro r hrl hru
  have hn : 1 < N := by omega
  have hn0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hn0
  have htol := logarithmicTolerance_pos hn
  have hD : 0 < logarithmicMomentCutoff A N := by
    unfold logarithmicMomentCutoff
    have hl : 0 < Real.log N := by linarith
    positivity
  have hthreshold := (logarithmic_threshold_le (A := A) hlog hH.le).trans
    (show logarithmicTolerance N / 2 + logarithmicRelativeError A H N * logarithmicTolerance N ≤
      logarithmicTolerance N by nlinarith)
  have h := hbound N hn0 K r hK hNK hrl hru hdegree (Real.log N) hlog
    (Real.log N / 32) (logarithmicTolerance N / 2) ((N : ℝ) ^ (-1 / 16 : ℝ))
    (logarithmicMomentCutoff A N) (by linarith) (by positivity)
    (Real.rpow_pos_of_pos hNr _) hD
  have hprob := (measure_mono (μ := signMeasure N) (show
      {ω | logarithmicTolerance N <
        |logCircleAverage (rademacherPolynomial N ω) r - Real.log (radialSigma N r) - circularLogMean|} ⊆
      {ω | logarithmicTolerance N / 2 + 2 * (Real.log N / 32) * (H / Real.sqrt N) +
          logarithmicMomentCutoff A N * Real.sqrt
            (Real.exp (-2 * (Real.log N / 32)) + H / Real.sqrt N + (N : ℝ) ^ (-1 / 16 : ℝ)) +
          (3 / 2 : ℝ) * Real.exp (-2 * (Real.log N / 32)) <
        |logCircleAverage (rademacherPolynomial N ω) r - Real.log (radialSigma N r) - circularLogMean|}
      from fun _ hω => lt_of_le_of_lt hthreshold hω)).trans h
  have hfinal := hprob.trans (ENNReal.ofReal_le_ofReal (logarithmic_failure_le hlog hA hH.le))
  have hnneg : 0 ≤ (2 * H + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) := by positivity
  dsimp only [H] at hnneg
  simpa only [measureReal_def, ENNReal.toReal_ofReal hnneg] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hfinal

/-- The tolerance tends to zero, with its exact logarithmic power. -/
theorem tendsto_logarithmicTolerance : Tendsto logarithmicTolerance atTop (𝓝 0) := by
  have ht := (isLittleO_log_rpow_rpow_atTop (7 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 32)).tendsto_div_nhds_zero
  have hn := ht.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hn.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  simp only [Function.comp_def, logarithmicTolerance,
    show (-1 / 32 : ℝ) = -(1 / 32 : ℝ) by ring, Real.rpow_neg hNr, div_eq_mul_inv, mul_comm]
  rw [show (Real.log N) ^ (7 : ℝ) = (Real.log N) ^ (7 : ℕ) from Real.rpow_natCast _ 7]

end Erdos522

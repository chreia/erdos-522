/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SparseAnnularTightness
import Erdos522.Analysis.KacProfileDerivative

/-!
# Sparse radial limits at a vanishing scaled coordinate

Fixed radial probes squeeze any target radius whose scaled displacement tends
to zero. Countably many probe widths suffice on the probability space of one
infinite sign sequence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Polynomial
open scoped Topology
namespace Erdos522
open LogMoments

def radialLowerSecantEnvelope (K : ℝ) (N : ℕ) : ℝ :=
  (Real.log (radialSigma N (radialSecantRadii K N 1)) -
      Real.log (radialSigma N (radialSecantRadii K N 0)) - 2 * logarithmicTolerance N) /
    ((N : ℝ) * Real.log (radialSecantRadii K N 1 / radialSecantRadii K N 0))

def radialUpperSecantEnvelope (K : ℝ) (N : ℕ) : ℝ :=
  (Real.log (radialSigma N (radialSecantRadii K N 3)) -
      Real.log (radialSigma N (radialSecantRadii K N 2)) + 2 * logarithmicTolerance N) /
    ((N : ℝ) * Real.log (radialSecantRadii K N 3 / radialSecantRadii K N 2))

/-- The closed-disk zero fraction between the two middle probes is squeezed
between the outer logarithmic secants. -/
theorem radial_fraction_between_variance_secants (P : Polynomial ℂ) (N : ℕ)
    {K r : ℝ} (hK : 0 < K) (hNK : 2 * K < N)
    (hrl : radialSecantRadii K N 1 ≤ r) (hru : r ≤ radialSecantRadii K N 2)
    (hlog : ∀ i : Fin 4,
      |logCircleAverage P (radialSecantRadii K N i) -
        Real.log (radialSigma N (radialSecantRadii K N i)) - circularLogMean| ≤ logarithmicTolerance N) :
    radialLowerSecantEnvelope K N ≤ (closedZeroCount P r : ℝ) / N ∧
      (closedZeroCount P r : ℝ) / N ≤ radialUpperSecantEnvelope K N := by
  have hn : (0 : ℝ) < N := by linarith
  have ha : 0 < K / N := div_pos hK hn
  have ha' : K / N < 1 / 2 := (div_lt_iff₀ hn).mpr (by linarith)
  have hr₀ : radialSecantRadii K N 0 = 1 - K / N := by simp [radialSecantRadii]; ring
  have hr₁ : radialSecantRadii K N 1 = 1 - (K / N) / 2 := by simp [radialSecantRadii]; ring
  have hr₂ : radialSecantRadii K N 2 = 1 + (K / N) / 2 := by simp [radialSecantRadii]; ring
  have hr₃ : radialSecantRadii K N 3 = 1 + K / N := by simp [radialSecantRadii]
  have h₀ : 0 < radialSecantRadii K N 0 := by rw [hr₀]; linarith
  have h₀₁ : radialSecantRadii K N 0 < radialSecantRadii K N 1 := by rw [hr₀, hr₁]; linarith
  have h₂ : 0 < radialSecantRadii K N 2 := by rw [hr₂]; linarith
  have h₂₃ : radialSecantRadii K N 2 < radialSecantRadii K N 3 := by rw [hr₂, hr₃]; linarith
  have hd₁ := (radial_zero_count_bound P h₀ h₀₁).2
  have hd₂ := (radial_zero_count_bound P h₂ h₂₃).1
  have hc₁ : (closedZeroCount P (radialSecantRadii K N 1) : ℝ) ≤ closedZeroCount P r :=
    Nat.cast_le.mpr (closedZeroCount_mono P hrl)
  have hc₂ : (closedZeroCount P r : ℝ) ≤ closedZeroCount P (radialSecantRadii K N 2) :=
    Nat.cast_le.mpr (closedZeroCount_mono P hru)
  have hl₁ : 0 < Real.log (radialSecantRadii K N 1 / radialSecantRadii K N 0) :=
    Real.log_pos ((one_lt_div h₀).mpr h₀₁)
  have hl₂ : 0 < Real.log (radialSecantRadii K N 3 / radialSecantRadii K N 2) :=
    Real.log_pos ((one_lt_div h₂).mpr h₂₃)
  have he₀ := abs_le.mp (hlog 0)
  have he₁ := abs_le.mp (hlog 1)
  have he₂ := abs_le.mp (hlog 2)
  have he₃ := abs_le.mp (hlog 3)
  constructor
  · have he : Real.log (radialSigma N (radialSecantRadii K N 1)) -
        Real.log (radialSigma N (radialSecantRadii K N 0)) - 2 * logarithmicTolerance N ≤
      logCircleAverage P (radialSecantRadii K N 1) - logCircleAverage P (radialSecantRadii K N 0) := by linarith
    have h := (div_le_div_of_nonneg_right he hl₁.le).trans (hd₁.trans hc₁)
    have hh := div_le_div_of_nonneg_right h hn.le
    simpa only [radialLowerSecantEnvelope, div_div, mul_comm] using hh
  · have he : logCircleAverage P (radialSecantRadii K N 3) - logCircleAverage P (radialSecantRadii K N 2) ≤
      Real.log (radialSigma N (radialSecantRadii K N 3)) -
        Real.log (radialSigma N (radialSecantRadii K N 2)) + 2 * logarithmicTolerance N := by linarith
    have h := (hc₂.trans hd₂).trans (div_le_div_of_nonneg_right he hl₂.le)
    have hh := div_le_div_of_nonneg_right h hn.le
    simpa only [radialUpperSecantEnvelope, div_div, mul_comm] using hh

theorem tendsto_radialLowerSecantEnvelope {K : ℝ} (hK : 0 < K) :
    Tendsto (radialLowerSecantEnvelope K) atTop
      (𝓝 ((kacLogVarianceProfile (-K / 2) - kacLogVarianceProfile (-K)) / (K / 2))) := by
  unfold radialLowerSecantEnvelope
  have ht := ((tendsto_log_radialSigma_sub (-K) (-K / 2)).sub
    (tendsto_logarithmicTolerance.const_mul 2)).div
      (tendsto_degree_mul_log_radius_ratio (-K) (-K / 2)) (by linarith : -K / 2 - -K ≠ 0)
  simpa [radialSecantRadii, Pi.div_def, show -K / 2 - -K = K / 2 by ring] using ht

theorem tendsto_radialUpperSecantEnvelope {K : ℝ} (hK : 0 < K) :
    Tendsto (radialUpperSecantEnvelope K) atTop
      (𝓝 ((kacLogVarianceProfile K - kacLogVarianceProfile (K / 2)) / (K / 2))) := by
  unfold radialUpperSecantEnvelope
  have ht := ((tendsto_log_radialSigma_sub (K / 2) K).add
    (tendsto_logarithmicTolerance.const_mul 2)).div
      (tendsto_degree_mul_log_radius_ratio (K / 2) K) (by linarith : K - K / 2 ≠ 0)
  simpa [radialSecantRadii, Pi.div_def, show K - K / 2 = K / 2 by ring] using ht

/-- A countable family of lower and upper envelopes determines a common limit. -/
theorem tendsto_of_countable_envelopes (X : ℕ → ℝ) (L U : ℕ → ℕ → ℝ) (l u : ℕ → ℝ) (c : ℝ)
    (hL : ∀ m, Tendsto (L m) atTop (𝓝 (l m)))
    (hU : ∀ m, Tendsto (U m) atTop (𝓝 (u m)))
    (hl : Tendsto l atTop (𝓝 c)) (hu : Tendsto u atTop (𝓝 c))
    (hbound : ∀ m, ∀ᶠ n in atTop, L m n ≤ X n ∧ X n ≤ U m n) :
    Tendsto X atTop (𝓝 c) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨m, hm⟩ := (hl.eventually_const_lt ha).exists
    filter_upwards [hbound m, (hL m).eventually_const_lt hm] with n hn hLn
    exact hLn.trans_le hn.1
  · intro a ha
    obtain ⟨m, hm⟩ := (hu.eventually_lt_const ha).exists
    filter_upwards [hbound m, (hU m).eventually_lt_const hm] with n hn hUn
    exact hn.2.trans_lt hUn

/-- The countable positive widths used to approach the unit circle. -/
def reciprocalProbeWidth (m : ℕ) : ℝ := 2 / ((m : ℝ) + 1)

theorem reciprocalProbeWidth_pos (m : ℕ) : 0 < reciprocalProbeWidth m := by
  unfold reciprocalProbeWidth
  positivity

theorem tendsto_reciprocal_lower_profile_secant :
    Tendsto (fun m : ℕ =>
      (kacLogVarianceProfile (-reciprocalProbeWidth m / 2) -
        kacLogVarianceProfile (-reciprocalProbeWidth m)) / (reciprocalProbeWidth m / 2))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  apply (tendsto_kac_profile_two_scale_secant (s := -1) (by norm_num)).congr
  intro m
  have h₁ : -reciprocalProbeWidth m / 2 = (-1 : ℝ) / ((m : ℝ) + 1) := by
    unfold reciprocalProbeWidth
    ring
  have h₂ : -reciprocalProbeWidth m = 2 * ((-1 : ℝ) / ((m : ℝ) + 1)) := by
    unfold reciprocalProbeWidth
    ring
  have h₃ : reciprocalProbeWidth m / 2 = -((-1 : ℝ) / ((m : ℝ) + 1)) := by
    unfold reciprocalProbeWidth
    ring
  rw [h₁, h₂, h₃, div_neg]
  ring

theorem tendsto_reciprocal_upper_profile_secant :
    Tendsto (fun m : ℕ =>
      (kacLogVarianceProfile (reciprocalProbeWidth m) -
        kacLogVarianceProfile (reciprocalProbeWidth m / 2)) / (reciprocalProbeWidth m / 2))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  apply (tendsto_kac_profile_two_scale_secant (s := 1) (by norm_num)).congr
  intro m
  have h₁ : reciprocalProbeWidth m / 2 = (1 : ℝ) / ((m : ℝ) + 1) := by
    unfold reciprocalProbeWidth
    ring
  have h₂ : reciprocalProbeWidth m = 2 * ((1 : ℝ) / ((m : ℝ) + 1)) := by
    unfold reciprocalProbeWidth
    ring
  rw [h₁, h₂]

/-- A radius with vanishing scaled displacement eventually lies between any two fixed middle probes. -/
theorem eventually_between_radial_probes {r : ℕ → ℝ}
    (hr : Tendsto (fun N : ℕ => (N : ℝ) * (r N - 1)) atTop (𝓝 0))
    {K : ℝ} (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop, radialSecantRadii K N 1 ≤ r N ∧ r N ≤ radialSecantRadii K N 2 := by
  filter_upwards [eventually_ge_atTop 1,
    hr.eventually_const_lt (show -K / 2 < (0 : ℝ) by linarith),
    hr.eventually_lt_const (show (0 : ℝ) < K / 2 by linarith)] with N hN hlo hup
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : -K / 2 / N < r N - 1 := (div_lt_iff₀ hn).mpr (by nlinarith)
  have hu : r N - 1 < K / 2 / N := (lt_div_iff₀ hn).mpr (by nlinarith)
  have hr₁ : radialSecantRadii K N 1 = 1 + (-K / 2) / N := by simp [radialSecantRadii]
  have hr₂ : radialSecantRadii K N 2 = 1 + (K / 2) / N := by simp [radialSecantRadii]
  rw [hr₁, hr₂]
  constructor <;> linarith

/-- Sparse root counts tend to one half at every deterministic target radius
whose displacement from the unit circle is `o(1/N)`. -/
theorem ae_sparse_radial_fraction_limit_of_scaled_radius_zero {C : ℝ}
    (hC : 1 ≤ C) (hR : HarmonicL2Restriction C) (r : ℕ → ℝ)
    (hr : Tendsto (fun N : ℕ => (N : ℝ) * (r N - 1)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherRadialFraction ω (j ^ 8) (r (j ^ 8))) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlog : ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ m : ℕ, ∀ᶠ j : ℕ in atTop, ∀ i : Fin 4,
      |logCircleAverage (polynomialPrefix (fun k => sign (ω k)) (fun _ => 1) (j ^ 8))
          (radialSecantRadii (reciprocalProbeWidth m) (j ^ 8) i) -
        Real.log (radialSigma (j ^ 8) (radialSecantRadii (reciprocalProbeWidth m) (j ^ 8) i)) -
          circularLogMean| ≤ logarithmicTolerance (j ^ 8) := by
    apply ae_all_iff.mpr
    intro m
    exact ae_eventually_four_radial_logarithmic_bound hC hR (reciprocalProbeWidth m)
      (reciprocalProbeWidth_pos m).le
  filter_upwards [hlog] with ω hω
  have hp := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  apply tendsto_of_countable_envelopes _
    (fun m j => radialLowerSecantEnvelope (reciprocalProbeWidth m) (j ^ 8))
    (fun m j => radialUpperSecantEnvelope (reciprocalProbeWidth m) (j ^ 8)) _ _ (1 / 2)
    (fun m => (tendsto_radialLowerSecantEnvelope (reciprocalProbeWidth_pos m)).comp hp)
    (fun m => (tendsto_radialUpperSecantEnvelope (reciprocalProbeWidth_pos m)).comp hp)
    tendsto_reciprocal_lower_profile_secant tendsto_reciprocal_upper_profile_secant
  intro m
  have hK := reciprocalProbeWidth_pos m
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hp
  filter_upwards [hω m, hp.eventually (eventually_between_radial_probes hr hK),
    ht.eventually_gt_atTop (2 * reciprocalProbeWidth m)] with j hj hrad hN
  exact radial_fraction_between_variance_secants
    (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω)) (j ^ 8) hK hN hrad.1 hrad.2
    (by simpa only [rademacherPrefix_polynomial] using hj)

end Erdos522

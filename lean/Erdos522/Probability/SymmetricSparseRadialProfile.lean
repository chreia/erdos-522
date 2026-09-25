/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SymmetricSparseLogarithms
import Erdos522.Probability.SparseRadialProfile
import Erdos522.Probability.DegreeBoundedRadialMass

/-!
# Sparse symmetric coefficient radial profiles

Jensen secants convert simultaneous logarithmic concentration into annular
tightness and the Kac radial profile. All zero counts use algebraic
multiplicity and closed disks, on one infinite symmetric coefficient sequence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Erdos522

/-- The multiplicity-counted closed-disk fraction for a symmetric coefficient prefix. -/
def coefficientRadialFraction (ω : ℕ → ℂ) (N : ℕ) (r : ℝ) : ℝ :=
  (closedZeroCount (Polynomial.ofFn (N + 1) (coefficientPrefix N ω)) r : ℝ) / N

/-- Sparse symmetric coefficient root mass outside the closed annulus of width `K/N`. -/
def coefficientSparseAnnularTailFraction (ω : ℕ → ℂ) (K j : ℕ) : ℝ :=
  (zeroCountIn (Polynomial.ofFn (j ^ 8 + 1) (coefficientPrefix (j ^ 8) ω))
    {z | |‖z‖ - 1| ≤ (K : ℝ) / (j ^ 8 : ℕ)}ᶜ : ℝ) / ((j ^ 8 : ℕ) : ℝ)

/-- The exact four-probe annular Jensen bound holds along the shared sparse prefixes. -/
theorem ae_eventually_symmetric_sparse_annular_variance_bound (μ : Measure ℂ) [IsProbabilityMeasure μ] [μ.IsNegInvariant]
    (B : ℝ) (hB : 0 < B) (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
    (hsecond : (∫ z, ‖z‖ ^ 2 ∂μ) = 1) (K : ℕ) (hK : 0 < K) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ᶠ j : ℕ in atTop,
      coefficientSparseAnnularTailFraction ω K j ≤ radialVarianceSecantEnvelope K (j ^ 8) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  filter_upwards [ae_eventually_symmetric_four_radial_logarithmic_bound μ B hB hbound hsecond K hK'.le] with ω hω
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).comp
    (tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num))
  filter_upwards [hω, ht.eventually_gt_atTop (2 * K)] with j hj hNj
  apply radial_mass_le_variance_secant_envelope_of_degree_le
    (Polynomial.ofFn (j ^ 8 + 1) (coefficientPrefix (j ^ 8) ω)) (j ^ 8)
    (by rw [coefficientPrefix_polynomial]; exact polynomialPrefix_natDegree_le _ _ _) hK' hNj
  simpa only [coefficientPrefix_polynomial] using hj

/-- The four-secant tail coefficient applies simultaneously to every integer width. -/
theorem ae_symmetric_sparse_annular_tail_bound (μ : Measure ℂ) [IsProbabilityMeasure μ] [μ.IsNegInvariant]
    (B : ℝ) (hB : 0 < B) (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
    (hsecond : (∫ z, ‖z‖ ^ 2 ∂μ) = 1) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j : ℕ in atTop, coefficientSparseAnnularTailFraction ω (K + 1) j ≤
        2 * Real.log 2 / ((K : ℝ) + 1) + ε := by
  have hbase : ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ K : ℕ, ∀ᶠ j : ℕ in atTop,
      coefficientSparseAnnularTailFraction ω (K + 1) j ≤
        radialVarianceSecantEnvelope ((K : ℝ) + 1) (j ^ 8) := by
    apply ae_all_iff.mpr
    intro K
    simpa only [Nat.cast_add, Nat.cast_one] using
      ae_eventually_symmetric_sparse_annular_variance_bound μ B hB hbound hsecond (K + 1) (by omega)
  filter_upwards [hbase] with ω hω
  intro K ε hε
  have hK : (0 : ℝ) < K + 1 := by positivity
  have hlim := (tendsto_radialVarianceSecantEnvelope hK).comp
    (tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num))
  have hcoef := kacAnnularTailCoefficient_le hK
  filter_upwards [hω K, hlim.eventually_lt_const (show kacAnnularTailCoefficient ((K : ℝ) + 1) <
    2 * Real.log 2 / ((K : ℝ) + 1) + ε by linarith)] with j hj hbound
  exact hj.trans hbound.le

/-- symmetric coefficient sparse zero measures are almost surely tight on the radial scale `1/N`. -/
theorem ae_symmetric_sparse_annular_tightness (μ : Measure ℂ) [IsProbabilityMeasure μ] [μ.IsNegInvariant]
    (B : ℝ) (hB : 0 < B) (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
    (hsecond : (∫ z, ‖z‖ ^ 2 ∂μ) = 1) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ,
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ᶠ j : ℕ in atTop, coefficientSparseAnnularTailFraction ω K j ≤ ε := by
  filter_upwards [ae_symmetric_sparse_annular_tail_bound μ B hB hbound hsecond] with ω hω
  intro ε hε
  have ht := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * Real.log 2)
  simp only [mul_zero] at ht
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (ht.eventually_lt_const (show (0 : ℝ) < ε / 2 by positivity))
  refine ⟨K + 1, ?_⟩
  filter_upwards [hω K (ε / 2) (by positivity)] with j hj
  have hb := hK K le_rfl
  rw [← mul_div_assoc, mul_one] at hb
  linarith

/-- A deterministic target with scaled displacement tending to `x` has the Kac
radial limit along sparse symmetric coefficient prefixes. -/
theorem ae_symmetric_sparse_radial_profile_of_scaled_radius_limit (μ : Measure ℂ) [IsProbabilityMeasure μ] [μ.IsNegInvariant]
    (B : ℝ) (hB : 0 < B) (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
    (hsecond : (∫ z, ‖z‖ ^ 2 ∂μ) = 1) (r : ℕ → ℝ) (x : ℝ)
    (hr : Tendsto (fun N : ℕ => (N : ℝ) * (r N - 1)) atTop (𝓝 x)) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ,
      Tendsto (fun j : ℕ => coefficientRadialFraction ω (j ^ 8) (r (j ^ 8)))
        atTop (𝓝 (kacRadialProfile x)) := by
  let w : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hw (m : ℕ) : 0 < w m := by dsimp [w]; positivity
  have hlog : ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ m : ℕ, ∀ᶠ j : ℕ in atTop, ∀ i : Fin 4,
      |logCircleAverage (polynomialPrefix ω (fun _ => 1) (j ^ 8))
          (scaledRadialProbes x (w m) (j ^ 8) i) -
        Real.log (radialSigma (j ^ 8) (scaledRadialProbes x (w m) (j ^ 8) i)) -
          circularLogMean| ≤ logarithmicTolerance (j ^ 8) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_eventually_symmetric_sparse_radial_logarithmic_bound μ B hB hbound hsecond (|x| + 2 * w m)
      (by positivity) (scaledRadialProbes x (w m))
      (Filter.Eventually.of_forall fun N i => scaledRadialProbes_mem_annulus x (hw m).le N i) 8 (by norm_num)
  filter_upwards [hlog] with ω hω
  have hp := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  apply tendsto_of_countable_envelopes _
    (fun m j => scaledLowerSecantEnvelope x (w m) (j ^ 8))
    (fun m j => scaledUpperSecantEnvelope x (w m) (j ^ 8)) _ _ (kacRadialProfile x)
    (fun m => (tendsto_scaledLowerSecantEnvelope x (hw m)).comp hp)
    (fun m => (tendsto_scaledUpperSecantEnvelope x (hw m)).comp hp)
    (tendsto_shifted_lower_profile_secant x) (tendsto_shifted_upper_profile_secant x)
  intro m
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hp
  filter_upwards [hω m, hp.eventually (eventually_between_scaled_radial_probes hr (hw m)),
    ht.eventually_gt_atTop (|x| + 2 * w m)] with j hj hrad hN
  exact radial_fraction_between_scaled_secants
    (Polynomial.ofFn (j ^ 8 + 1) (coefficientPrefix (j ^ 8) ω)) (j ^ 8) x (hw m) hN hrad.1 hrad.2
    (by simpa only [coefficientPrefix_polynomial] using hj)

/-- Both boundaries of a moving matching window share the same sparse symmetric coefficient profile. -/
theorem ae_symmetric_sparse_moving_radius_profile (μ : Measure ℂ) [IsProbabilityMeasure μ] [μ.IsNegInvariant]
    (B : ℝ) (hB : 0 < B) (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
    (hsecond : (∫ z, ‖z‖ ^ 2 ∂μ) = 1) (x s : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ,
      Tendsto (fun j : ℕ => coefficientRadialFraction ω (j ^ 8)
        (1 + x / (j ^ 8 : ℕ) + s * ((j ^ 8 : ℕ) : ℝ) ^ (-1 - κ)))
        atTop (𝓝 (kacRadialProfile x)) :=
  ae_symmetric_sparse_radial_profile_of_scaled_radius_limit μ B hB hbound hsecond
    (fun N => 1 + x / N + s * (N : ℝ) ^ (-1 - κ)) x (tendsto_scaled_moving_radius x s hκ)

end Erdos522

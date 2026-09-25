/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.AnnularSecantApproximation
import Erdos522.Probability.LogarithmicPowerConcentration

/-!
# Annular tightness on rounded real-power schedules

The retuned logarithmic estimate gives the same explicit annular tail
coefficient for every sparse-degree exponent greater than two.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522
open LogMoments

/-- The annular tail fraction on a rounded real-power schedule. -/
def realPowerAnnularTailFraction (q : ℝ) (ω : RademacherSequence) (K j : ℕ) : ℝ :=
  (zeroCountIn (rademacherPolynomial (realPowerDegree q j) (rademacherPrefix (realPowerDegree q j) ω))
    {z | |‖z‖ - 1| ≤ (K : ℝ) / realPowerDegree q j}ᶜ : ℝ) / realPowerDegree q j

/-- Simultaneous integer-width tail bounds for every degree exponent greater than two. -/
theorem ae_real_power_annular_tail_bound {q : ℝ} (hq : 2 < q) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j : ℕ in atTop, realPowerAnnularTailFraction q ω (K + 1) j ≤
        2 * Real.log 2 / ((K : ℝ) + 1) + ε := by
  have hscale := admissible_sparse_degree_scales hq
  let t := (1 / 2 - 1 / q) / 16
  have ht : 0 < t := hscale.logarithmic_pos
  have hs : 1 < q * (1 / 2 - 4 * t) := hscale.occupation_summability
  have hprobes (K : ℕ) := exists_ae_real_power_logarithmic_power_bound hq ht hs
    ((K : ℝ) + 1) (by positivity) (radialSecantRadii ((K : ℝ) + 1))
    (Filter.Eventually.of_forall fun N i => radialSecantRadii_mem_annulus (by positivity) N i)
  choose H _hH hlog using hprobes
  let e : ℕ → ℕ → ℝ := fun K => logarithmicPowerTolerance t
    (fourierLogarithmicConstant harmonicRestrictionConstant) (H K)
  have he (K : ℕ) : Tendsto (e K) atTop (𝓝 0) := tendsto_logarithmicPowerTolerance ht _ _
  filter_upwards [ae_all_iff.mpr hlog] with ω hω
  intro K ε hε
  have hK : (0 : ℝ) < K + 1 := by positivity
  have hp := tendsto_realPowerDegree (show 0 < q by linarith)
  have hdegree := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hp
  have hlim := (tendsto_approximateAnnularSecantEnvelope (he K) hK).comp hp
  have hcoef := kacAnnularTailCoefficient_le hK
  filter_upwards [hω K, hdegree.eventually_gt_atTop (2 * ((K : ℝ) + 1)),
    hlim.eventually_lt_const (show kacAnnularTailCoefficient ((K : ℝ) + 1) <
      2 * Real.log 2 / ((K : ℝ) + 1) + ε by linarith)] with j hj hN hbound
  have hmass := radial_mass_le_approximate_secant_envelope
    (rademacherPolynomial (realPowerDegree q j) (rademacherPrefix (realPowerDegree q j) ω))
      (realPowerDegree q j) (e K) (rademacherPolynomial_prefix_natDegree ω _) hK hN hj
  have htail : realPowerAnnularTailFraction q ω (K + 1) j ≤
      approximateAnnularSecantEnvelope (e K) ((K : ℝ) + 1) (realPowerDegree q j) := by
    simpa only [realPowerAnnularTailFraction, Nat.cast_add, Nat.cast_one] using hmass
  exact htail.trans hbound.le

/-- The same probability-one event supplies tightness at radial scale `1/N`. -/
theorem ae_real_power_annular_tightness {q : ℝ} (hq : 2 < q) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ᶠ j : ℕ in atTop,
        realPowerAnnularTailFraction q ω K j ≤ ε := by
  filter_upwards [ae_real_power_annular_tail_bound hq] with ω hω
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

end Erdos522

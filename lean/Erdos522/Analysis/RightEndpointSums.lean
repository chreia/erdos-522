/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.UnitIntervalPartition
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Right-endpoint sums as integrals

Sampling at the right endpoint of each uniform cell represents a finite
Riemann sum as the integral of a step function. The sample points approach
the original point from above, which also accommodates integrable power
singularities at the left endpoint.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Erdos522

/-- The right endpoint of the uniform cell containing a nonnegative point. -/
def rightEndpointSample (N : ℕ) (x : ℝ) : ℝ := ((⌊(N : ℝ) * x⌋₊ : ℝ) + 1) / N

theorem measurable_rightEndpointSample (N : ℕ) : Measurable (rightEndpointSample N) := by
  unfold rightEndpointSample
  fun_prop

/-- Sampling is constant on each half-open cell. -/
theorem rightEndpointSample_eq {N : ℕ} (hN : 0 < N) (j : Fin N)
    {x : ℝ} (hx : x ∈ unitIntervalCell j) :
    rightEndpointSample N x = ((j.val : ℝ) + 1) / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo : (j.val : ℝ) ≤ (N : ℝ) * x := by
    have h := (div_le_iff₀ hn).mp hx.1
    nlinarith
  have hhi : (N : ℝ) * x < (j.val : ℝ) + 1 := by
    have h := (lt_div_iff₀ hn).mp hx.2
    nlinarith
  have hfloor := (Nat.floor_eq_iff ((Nat.cast_nonneg j.val).trans hlo)).mpr ⟨hlo, hhi⟩
  simp only [rightEndpointSample, hfloor]

/-- The sample lies within one mesh length above the point. -/
theorem rightEndpointSample_bounds {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : 0 ≤ x) :
    x < rightEndpointSample N x ∧ rightEndpointSample N x ≤ x + 1 / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo := Nat.lt_floor_add_one ((N : ℝ) * x)
  have hhi := Nat.floor_le (mul_nonneg hn.le hx)
  constructor
  · apply (lt_div_iff₀ hn).mpr
    nlinarith
  · apply (div_le_iff₀ hn).mpr
    have hcancel : (x + 1 / (N : ℝ)) * N = (N : ℝ) * x + 1 := by field_simp
    rw [hcancel]
    linarith

/-- Samples of the unit interval stay in its positive closed part. -/
theorem rightEndpointSample_mem {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) : rightEndpointSample N x ∈ Ioc (0 : ℝ) 1 := by
  have hc : x ∈ ⋃ j : Fin N, unitIntervalCell j := by rwa [iUnion_unitIntervalCell hN]
  obtain ⟨j, hj⟩ := mem_iUnion.mp hc
  rw [rightEndpointSample_eq hN j hj]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · positivity
  · apply (div_le_one hn).mpr
    exact_mod_cast Nat.succ_le_of_lt j.isLt

/-- Refining the mesh makes the sample approach every nonnegative point. -/
theorem tendsto_rightEndpointSample {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun N => rightEndpointSample N x) atTop (𝓝 x) := by
  have hu := tendsto_one_div_atTop_nhds_zero_nat.const_add x
  simp only [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (rightEndpointSample_bounds (by omega) hx).1.le
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (rightEndpointSample_bounds (by omega) hx).2

/-- Right-endpoint step functions are integrable on the unit interval,
without a continuity hypothesis on the sampled function. -/
theorem integrableOn_rightEndpointSample {N : ℕ} (hN : 0 < N) (f : ℝ → ℝ) :
    IntegrableOn (fun x => f (rightEndpointSample N x)) (Ico (0 : ℝ) 1) := by
  rw [← iUnion_unitIntervalCell hN]
  apply integrableOn_finite_iUnion.mpr
  intro j
  have hconst : IntegrableOn (fun _ : ℝ => f (((j.val : ℝ) + 1) / N)) (unitIntervalCell j) :=
    integrableOn_const (by simp [unitIntervalCell])
  exact hconst.congr_fun (fun x hx => by rw [rightEndpointSample_eq hN j hx])
    (measurableSet_unitIntervalCell j)

/-- The integral of the sampled function is the normalized finite sum. -/
theorem integral_rightEndpointSample {N : ℕ} (hN : 0 < N) (f : ℝ → ℝ) :
    (∫ x in Ico (0 : ℝ) 1, f (rightEndpointSample N x)) =
      (∑ j : Fin N, f (((j.val : ℝ) + 1) / N)) / N := by
  rw [← iUnion_unitIntervalCell hN, integral_iUnion_fintype
    measurableSet_unitIntervalCell (pairwiseDisjoint_unitIntervalCell hN)
      (fun j => (integrableOn_rightEndpointSample hN f).mono_set (unitIntervalCell_subset hN j))]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [setIntegral_congr_fun (measurableSet_unitIntervalCell j)
    (fun x hx => congrArg f (rightEndpointSample_eq hN j hx)), setIntegral_const,
    smul_eq_mul, measureReal_def, volume_unitIntervalCell,
    ENNReal.toReal_ofReal (by positivity)]
  ring

/-- Dominated convergence for right-endpoint sums permits a varying sampled
function and an integrable singularity at zero. -/
theorem tendsto_rightEndpointSums_of_dominated
    (F : ℕ → ℝ → ℝ) (f bound : ℝ → ℝ)
    (hbound : IntegrableOn bound (Ioo (0 : ℝ) 1))
    (hdom : ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1,
      ‖F N (rightEndpointSample N x)‖ ≤ bound x)
    (hlim : ∀ x ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun N => F N (rightEndpointSample N x)) atTop (𝓝 (f x))) :
    Tendsto (fun N : ℕ => (∑ j : Fin N, F N (((j.val : ℝ) + 1) / N)) / N)
      atTop (𝓝 (∫ x in Ioc (0 : ℝ) 1, f x)) := by
  have hmeas : ∀ᶠ N : ℕ in atTop,
      AEStronglyMeasurable (fun x => F N (rightEndpointSample N x))
        (volume.restrict (Ioo (0 : ℝ) 1)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact ((integrableOn_rightEndpointSample (by omega) (F N)).mono_set Ioo_subset_Ico_self).1
  have hdom' : ∀ᶠ N : ℕ in atTop,
      ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), ‖F N (rightEndpointSample N x)‖ ≤ bound x := by
    filter_upwards [hdom] with N hN
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hN x hx
  have hlim' : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      Tendsto (fun N => F N (rightEndpointSample N x)) atTop (𝓝 (f x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hlim x hx
  have ht := tendsto_integral_filter_of_dominated_convergence bound hmeas hdom' hbound hlim'
  rw [integral_Ioc_eq_integral_Ioo]
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [← integral_rightEndpointSample (by omega) (F N), integral_Ico_eq_integral_Ioo]

end Erdos522

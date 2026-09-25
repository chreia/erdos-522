/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ProductCirclePartition
import Erdos522.Analysis.IntervalPartitionScale

/-!
# Choosing an angular partition with definite dense-cell growth

A uniform partition at scale comparable to `n/Δ` captures at least half the
mass gained by the shift `n τ`. If that scale exceeds the circle length, the
one-cell partition has no boundary loss.
-/

noncomputable section
open MeasureTheory Set
namespace Erdos522

/-- A finite probability product admits a partition whose dense cells capture
at least half a prescribed angular translation gain. -/
theorem exists_spreading_partition {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Fintype Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set (Ω × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    {n : ℕ} (hn : 1 ≤ n) {τ Δ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hgain : (μ.prod AddCircle.haarAddCircle).real
      ((fun x : Ω × AddCircle (1 : ℝ) => (x.1, x.2 + (((n : ℝ) * τ : ℝ) :
        AddCircle (1 : ℝ)))) ⁻¹' E \ E) = Δ) :
    ∃ (q : ℕ) (M : ℝ), 0 < q ∧ 1 ≤ M ∧ M ≤ 16 * n / Δ ∧ 1 / (q : ℝ) = M * τ ∧
      Δ / 2 ≤ (μ.prod AddCircle.haarAddCircle).real
        (densePartitionCells (μ.prod AddCircle.haarAddCircle)
          (productCirclePartitionCell (q := q)) E (Δ / 8) \ E) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hA : 0 < 8 * (n : ℝ) / Δ := by positivity
  have hA1 : 1 ≤ 8 * (n : ℝ) / Δ := by
    apply (le_div_iff₀ hΔ).mpr
    nlinarith
  by_cases hsmall : (8 * (n : ℝ) / Δ) * τ ≤ 1
  · obtain ⟨q, M, hq, hMlo, hMhi, hscale⟩ := exists_uniform_partition_scale hA hτ hsmall
    have hM : 0 < M := hA.trans_le hMlo
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hprod : (q : ℝ) * (M * τ) = 1 := by rw [← hscale]; field_simp
    have hMN : 8 * (n : ℝ) ≤ M * Δ := (div_le_iff₀ hΔ).mp hMlo
    have hcost : (q : ℝ) * ((n : ℝ) * τ) ≤ Δ / 8 := by
      have h := mul_le_mul_of_nonneg_left hMN (mul_nonneg (Nat.cast_nonneg q) hτ.le)
      nlinarith [hprod]
    have hg := dense_product_circle_cells_growth μ hq E hE (by positivity : 0 ≤ Δ / 8)
      (mul_nonneg (Nat.cast_nonneg n) hτ.le)
    rw [hgain] at hg
    refine ⟨q, M, hq, hA1.trans hMlo, ?_, hscale, ?_⟩
    · convert hMhi.le using 1
      ring
    · linarith
  · have hbig : 1 < 8 * (n : ℝ) / Δ * τ := lt_of_not_ge hsmall
    have hMlo : 1 ≤ 1 / τ := (le_div_iff₀ hτ).mpr (by simpa using hτ1)
    have hMhi : 1 / τ ≤ 16 * (n : ℝ) / Δ := by
      apply (div_le_iff₀ hτ).mpr
      rw [show 16 * (n : ℝ) / Δ * τ = 2 * (8 * (n : ℝ) / Δ * τ) by ring]
      linarith
    have hg := dense_product_circle_cells_growth_one μ E hE (by positivity : 0 ≤ Δ / 8)
      ((((n : ℝ) * τ : ℝ) : AddCircle (1 : ℝ)))
    rw [hgain] at hg
    refine ⟨1, 1 / τ, by decide, hMlo, hMhi, ?_, ?_⟩
    · simp [hτ.ne']
    · linarith

end Erdos522

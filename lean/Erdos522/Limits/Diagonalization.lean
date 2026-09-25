/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Limits.SparseToDense
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Deterministic diagonal choices with a summable sequence of exceptional-event bounds. -/

noncomputable section

namespace Erdos522

open Filter
open scoped Topology ENNReal

/-- Increasing thresholds dominating a prescribed sequence of finite cutoffs. -/
def increasingThreshold (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => r 0
  | h + 1 => max (r (h + 1)) (increasingThreshold r h + 1)

theorem le_increasingThreshold (r : ℕ → ℕ) (h : ℕ) : r h ≤ increasingThreshold r h := by
  cases h with
  | zero => exact le_rfl
  | succ h => exact le_max_left _ _

theorem strictMono_increasingThreshold (r : ℕ → ℕ) : StrictMono (increasingThreshold r) := by
  apply strictMono_nat_of_lt_succ
  intro h
  exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)

/-- The mass of a nonnegative extended-real series after a given index. -/
def seriesTail (p : ℕ → ℝ≥0∞) (J : ℕ) : ℝ≥0∞ :=
  ∑' j, if J ≤ j then p j else 0

theorem seriesTail_antitone (p : ℕ → ℝ≥0∞) : Antitone (seriesTail p) := by
  intro I J hIJ
  apply ENNReal.tsum_le_tsum
  intro j
  by_cases hJj : J ≤ j
  · simp [hJj, hIJ.trans hJj]
  · simp [hJj]

theorem tendsto_seriesTail {p : ℕ → ℝ≥0∞} (hp : (∑' j, p j) ≠ ∞) :
    Tendsto (seriesTail p) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_tsum_compl_atTop_zero hp).comp tendsto_finset_range
  convert h using 1
  funext J
  simp only [Function.comp_apply]
  calc
    seriesTail p J = ∑' j, ({j : ℕ | j ∉ Finset.range J}).indicator p j := by
      apply tsum_congr
      intro j
      simp [Set.indicator, Finset.mem_range, not_lt]
    _ = _ := (tsum_subtype {j : ℕ | j ∉ Finset.range J} p).symm

/-- The block selector for increasing cutoffs preserves summability when the selected
tails have a summable bound. -/
theorem tsum_diagonal_ne_top {p : ℕ → ℕ → ℝ≥0∞} {J : ℕ → ℕ} {δ : ℕ → ℝ≥0∞}
    (hJ : StrictMono J) (hp : (∑' j, p 0 j) ≠ ∞)
    (hδ : (∑' h, δ h) ≠ ∞) (htail : ∀ h, seriesTail (p h) (J h) ≤ δ h) :
    (∑' j, p (blockIndex J j) j) ≠ ∞ := by
  have hpoint (j : ℕ) : p (blockIndex J j) j ≤
      p 0 j + ∑' h, if J h ≤ j then p h j else 0 := by
    by_cases hj : J 0 ≤ j
    · have hstart := (blockIndex_bounds hJ hj).1
      calc
        _ ≤ ∑' h, if J h ≤ j then p h j else 0 := by
          simpa only [ite_eq_left hstart] using
            (ENNReal.le_tsum (f := fun h ↦ if J h ≤ j then p h j else 0) (blockIndex J j))
        _ ≤ _ := le_add_left le_rfl
    · have hzero : blockIndex J j = 0 := by
        unfold blockIndex
        apply Nat.findGreatest_eq_zero_iff.mpr
        intro h _ _
        exact fun hJh ↦ hj ((hJ.monotone (Nat.zero_le h)).trans hJh)
      simp only [hzero]
      exact le_add_right le_rfl
  have htotal : (∑' j, p (blockIndex J j) j) ≤ (∑' j, p 0 j) + ∑' h, δ h := by
    calc
      _ ≤ ∑' j, (p 0 j + ∑' h, if J h ≤ j then p h j else 0) :=
        ENNReal.tsum_le_tsum hpoint
      _ = (∑' j, p 0 j) + ∑' h, seriesTail (p h) (J h) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_comm]
        rfl
      _ ≤ _ := add_le_add le_rfl (ENNReal.tsum_le_tsum htail)
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hp, hδ⟩) htotal

/-- Deterministic diagonal selection combines vanishing parameter errors and a summable
array of failure bounds into one vanishing error and one summable failure series. -/
theorem exists_summable_diagonal {a : ℕ → ℝ} {b : ℕ → ℕ → ℝ}
    {p : ℕ → ℕ → ℝ≥0∞} {u : ℕ → ℝ} {δ : ℕ → ℝ≥0∞}
    (ha : Tendsto a atTop (𝓝 0)) (hb : ∀ h, Tendsto (b h) atTop (𝓝 0))
    (hp : ∀ h, (∑' j, p h j) ≠ ∞)
    (hu : ∀ h, 0 < u h) (hu_lim : Tendsto u atTop (𝓝 0))
    (hδpos : ∀ h, 0 < δ h) (hδ : (∑' h, δ h) ≠ ∞) :
    ∃ s : ℕ → ℕ, Tendsto s atTop atTop ∧
      Tendsto (fun j ↦ a (s j) + b (s j) j) atTop (𝓝 0) ∧
      (∑' j, p (s j) j) ≠ ∞ := by
  have hcut (h : ℕ) : ∃ r, ∀ j ≥ r, |b h j| ≤ u h ∧ seriesTail (p h) j ≤ δ h := by
    have hbe : ∀ᶠ j in atTop, |b h j| < u h := by
      have hh : Tendsto (fun j ↦ |b h j|) atTop (𝓝 0) := by
        simpa only [abs_zero] using (hb h).abs
      exact hh.eventually (gt_mem_nhds (hu h))
    have hpe := (tendsto_seriesTail (hp h)).eventually (gt_mem_nhds (hδpos h))
    obtain ⟨r, hr⟩ := eventually_atTop.1 (hbe.and hpe)
    exact ⟨r, fun j hj ↦ ⟨(hr j hj).1.le, (hr j hj).2.le⟩⟩
  choose r hr using hcut
  let J := increasingThreshold r
  have hJ : StrictMono J := strictMono_increasingThreshold r
  let s := blockIndex J
  have hs : Tendsto s atTop atTop := tendsto_blockIndex hJ
  have hselected : Tendsto (fun j ↦ b (s j) j) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun j ↦ u (s j))
    · filter_upwards [eventually_ge_atTop (J 0)] with j hj
      have hstart := (blockIndex_bounds hJ hj).1
      have hh := (hr (s j) j ((le_increasingThreshold r (s j)).trans hstart)).1
      simpa only [Real.norm_eq_abs] using hh
    · exact hu_lim.comp hs
  refine ⟨s, hs, ?_, ?_⟩
  · simpa only [Function.comp_apply, zero_add] using (ha.comp hs).add hselected
  · apply tsum_diagonal_ne_top hJ (hp 0) hδ
    intro h
    exact (hr h (J h) (le_increasingThreshold r h)).2

/-- Vanishing parameterwise errors and finite parameterwise failure sums yield a
deterministic diagonal with a vanishing error and a finite total failure sum. -/
theorem exists_diagonal_of_summable_bounds {a : ℕ → ℝ} {b : ℕ → ℕ → ℝ}
    {p : ℕ → ℕ → ℝ≥0∞}
    (ha : Tendsto a atTop (𝓝 0)) (hb : ∀ h, Tendsto (b h) atTop (𝓝 0))
    (hp : ∀ h, (∑' j, p h j) ≠ ∞) :
    ∃ s : ℕ → ℕ, Tendsto s atTop atTop ∧
      Tendsto (fun j ↦ a (s j) + b (s j) j) atTop (𝓝 0) ∧
      (∑' j, p (s j) j) ≠ ∞ := by
  apply exists_summable_diagonal (u := fun h ↦ 1 / ((h : ℝ) + 1))
    (δ := fun h ↦ ((2 : ℝ≥0∞)⁻¹) ^ h) ha hb hp
  · intro h
    positivity
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · intro h
    exact ENNReal.pow_pos (by norm_num) h
  · rw [ENNReal.tsum_geometric]
    norm_num

end Erdos522

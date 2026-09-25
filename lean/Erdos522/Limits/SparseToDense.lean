/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Find
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.WellFounded
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-! Convergence of normalized real sequences from sparse degrees and block estimates. -/

noncomputable section

namespace Erdos522

open Filter MeasureTheory
open scoped Topology ENNReal

/-- The last subsequence index whose degree does not exceed the given degree. -/
def blockIndex (N : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun j ↦ N j ≤ n) n

/-- An increasing integer subsequence covers every degree after its first term by a block. -/
theorem blockIndex_bounds {N : ℕ → ℕ} (hN : StrictMono N) {n : ℕ}
    (hn : N 0 ≤ n) : N (blockIndex N n) ≤ n ∧ n < N (blockIndex N n + 1) := by
  constructor
  · exact Nat.findGreatest_spec (P := fun j ↦ N j ≤ n) (Nat.zero_le n) hn
  · by_contra h
    have hnext : N (blockIndex N n + 1) ≤ n := by omega
    have hi : blockIndex N n + 1 ≤ n := (hN.id_le _).trans hnext
    exact Nat.findGreatest_is_greatest (P := fun j ↦ N j ≤ n)
      (show Nat.findGreatest (fun j ↦ N j ≤ n) n < blockIndex N n + 1 from
        Nat.lt_succ_self _) hi hnext

/-- The containing-block index tends to infinity with the degree. -/
theorem tendsto_blockIndex {N : ℕ → ℕ} (hN : StrictMono N) :
    Tendsto (blockIndex N) atTop atTop := by
  apply tendsto_atTop.2
  intro j
  filter_upwards [eventually_ge_atTop (N j)] with n hn
  exact Nat.le_findGreatest ((hN.id_le j).trans hn) hn

/-- Eventually the containing block begins at a positive degree. -/
theorem eventually_blockIndex_bounds {N : ℕ → ℕ} (hN : StrictMono N) :
    ∀ᶠ n in atTop, 0 < N (blockIndex N n) ∧
      N (blockIndex N n) ≤ n ∧ n < N (blockIndex N n + 1) := by
  filter_upwards [eventually_ge_atTop (N 0),
    (tendsto_blockIndex hN).eventually (eventually_ge_atTop 1)] with n hn hi
  exact ⟨Nat.zero_lt_one.trans_le (hi.trans (hN.id_le _)), blockIndex_bounds hN hn⟩

/-- Consecutive subsequence ratios tending to one also control the ratio to every degree
inside the corresponding block. -/
theorem tendsto_block_degree_ratio {N : ℕ → ℕ} (hN : StrictMono N)
    (hratio : Tendsto (fun j ↦ (N (j + 1) : ℝ) / N j) atTop (𝓝 1)) :
    Tendsto (fun n ↦ (N (blockIndex N n) : ℝ) / n) atTop (𝓝 1) := by
  have hindex := tendsto_blockIndex hN
  have hlarge := eventually_blockIndex_bounds hN
  have hinverse : Tendsto (fun n : ℕ ↦ (n : ℝ) / N (blockIndex N n)) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hratio.comp hindex)
    · filter_upwards [hlarge] with n hn
      have hp : (0 : ℝ) < N (blockIndex N n) := by exact_mod_cast hn.1
      exact (one_le_div hp).2 (by exact_mod_cast hn.2.1)
    · filter_upwards [hlarge] with n hn
      exact div_le_div_of_nonneg_right (by exact_mod_cast hn.2.2.le) (Nat.cast_nonneg _)
  simpa only [one_div, inv_div, inv_one] using hinverse.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

/-- A normalized real sequence converges if its normalized sparse values converge and
its discrepancy on each block has a vanishing normalized bound. -/
theorem tendsto_normalized_of_sparse_blocks {N : ℕ → ℕ} {X ε : ℕ → ℝ} {c : ℝ}
    (hN : StrictMono N)
    (hratio : Tendsto (fun j ↦ (N (j + 1) : ℝ) / N j) atTop (𝓝 1))
    (hsparse : Tendsto (fun j ↦ X (N j) / N j) atTop (𝓝 c))
    (hε : Tendsto ε atTop (𝓝 0))
    (hblock : ∀ᶠ j in atTop, ∀ n, N j ≤ n → n < N (j + 1) →
      |X n - X (N j)| ≤ ε j * N j) :
    Tendsto (fun n ↦ X n / n) atTop (𝓝 c) := by
  have hindex := tendsto_blockIndex hN
  have hlarge := eventually_blockIndex_bounds hN
  have herror : Tendsto (fun n ↦ (X n - X (N (blockIndex N n))) / n)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n ↦ |ε (blockIndex N n)|)
    · filter_upwards [hlarge, hindex.eventually hblock] with n hn hb
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.1.trans_le hn.2.1
      have hbound : |X n - X (N (blockIndex N n))| ≤ |ε (blockIndex N n)| * n := by
        calc
          _ ≤ ε (blockIndex N n) * N (blockIndex N n) :=
            hb n hn.2.1 hn.2.2
          _ ≤ |ε (blockIndex N n)| * N (blockIndex N n) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _)
          _ ≤ |ε (blockIndex N n)| * n :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast hn.2.1) (abs_nonneg _)
      simpa only [Real.norm_eq_abs, abs_div, abs_of_pos hnpos] using
        (div_le_iff₀ hnpos).2 hbound
    · simpa only [Function.comp_def, abs_zero] using (hε.comp hindex).abs
  have hlim := ((hsparse.comp hindex).mul (tendsto_block_degree_ratio hN hratio)).add
    herror
  simp only [mul_one, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [hlarge] with n hn
  have hbpos : (N (blockIndex N n) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn.1)
  dsimp only [Function.comp_def]
  field_simp
  ring

/-- Fixed-parameter eventual estimates with vanishing parameter errors force convergence
of a nonnegative sequence to zero. -/
theorem tendsto_zero_of_eventual_parameter_bounds {d a : ℕ → ℝ} {b : ℕ → ℕ → ℝ}
    (hd : ∀ᶠ j in atTop, 0 ≤ d j)
    (ha : Tendsto a atTop (𝓝 0))
    (hb : ∀ h, Tendsto (b h) atTop (𝓝 0))
    (hbound : ∀ h, ∀ᶠ j in atTop, d j ≤ a h + b h j) :
    Tendsto d atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨h, hh⟩ := Metric.tendsto_atTop.1 ha (ε / 2) (by positivity)
  have hah : a h < ε / 2 := by
    have := hh h le_rfl
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have hbe : ∀ᶠ j in atTop, b h j < ε / 2 := by
    have := (hb h).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
    simpa using this
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hd.and ((hbound h).and hbe))
  refine ⟨J, fun j hj ↦ ?_⟩
  obtain ⟨hdj, hdjbound, hbj⟩ := hJ j hj
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hdj]
  linarith

/-- The largest normalized discrepancy between a sparse value and values in its block. -/
def normalizedBlockDiscrepancy (N : ℕ → ℕ) (hN : StrictMono N) (X : ℕ → ℝ)
    (j : ℕ) : ℝ :=
  (Finset.Ico (N j) (N (j + 1))).sup'
    (Finset.nonempty_Ico.mpr (hN (Nat.lt_succ_self j)))
    (fun n ↦ |X n - X (N j)| / N j)

theorem normalizedBlockDiscrepancy_nonneg (N : ℕ → ℕ) (hN : StrictMono N)
    (X : ℕ → ℝ) (j : ℕ) : 0 ≤ normalizedBlockDiscrepancy N hN X j := by
  have hmem : N j ∈ Finset.Ico (N j) (N (j + 1)) :=
    Finset.mem_Ico.mpr ⟨le_rfl, hN (Nat.lt_succ_self j)⟩
  have h := Finset.le_sup' (fun n ↦ |X n - X (N j)| / (N j : ℝ)) hmem
  simpa only [normalizedBlockDiscrepancy, sub_self, abs_zero, zero_div] using h

theorem le_normalizedBlockDiscrepancy (N : ℕ → ℕ) (hN : StrictMono N)
    (X : ℕ → ℝ) {j n : ℕ} (hn : N j ≤ n) (hn' : n < N (j + 1)) :
    |X n - X (N j)| / N j ≤ normalizedBlockDiscrepancy N hN X j := by
  exact Finset.le_sup' (fun n ↦ |X n - X (N j)| / (N j : ℝ))
    (Finset.mem_Ico.mpr ⟨hn, hn'⟩)

theorem normalizedBlockDiscrepancy_le (N : ℕ → ℕ) (hN : StrictMono N)
    (X : ℕ → ℝ) {j : ℕ} {u : ℝ}
    (hu : ∀ n, N j ≤ n → n < N (j + 1) → |X n - X (N j)| / N j ≤ u) :
    normalizedBlockDiscrepancy N hN X j ≤ u := by
  apply Finset.sup'_le
  intro n hn
  exact hu n (Finset.mem_Ico.mp hn).1 (Finset.mem_Ico.mp hn).2

/-- A vanishing maximum normalized block discrepancy interpolates normalized sparse limits. -/
theorem tendsto_normalized_of_blockDiscrepancy {N : ℕ → ℕ} {X : ℕ → ℝ} {c : ℝ}
    (hN : StrictMono N)
    (hratio : Tendsto (fun j ↦ (N (j + 1) : ℝ) / N j) atTop (𝓝 1))
    (hsparse : Tendsto (fun j ↦ X (N j) / N j) atTop (𝓝 c))
    (hdiscrepancy : Tendsto (normalizedBlockDiscrepancy N hN X) atTop (𝓝 0)) :
    Tendsto (fun n ↦ X n / n) atTop (𝓝 c) := by
  apply tendsto_normalized_of_sparse_blocks hN hratio hsparse hdiscrepancy
  filter_upwards [eventually_ge_atTop 1] with j hj
  intro n hn hn'
  have hp : (0 : ℝ) < N j := by exact_mod_cast Nat.zero_lt_one.trans_le (hj.trans (hN.id_le j))
  exact (div_le_iff₀ hp).1 (le_normalizedBlockDiscrepancy N hN X hn hn')

/-- Parameterwise eventual block bounds suffice for interpolation, with no uniformity in
the parameter required of their degree thresholds. -/
theorem tendsto_normalized_of_parameter_bounds {N : ℕ → ℕ} {X a : ℕ → ℝ}
    {b : ℕ → ℕ → ℝ} {c : ℝ} (hN : StrictMono N)
    (hratio : Tendsto (fun j ↦ (N (j + 1) : ℝ) / N j) atTop (𝓝 1))
    (hsparse : Tendsto (fun j ↦ X (N j) / N j) atTop (𝓝 c))
    (ha : Tendsto a atTop (𝓝 0)) (hb : ∀ h, Tendsto (b h) atTop (𝓝 0))
    (hbound : ∀ h, ∀ᶠ j in atTop, ∀ n, N j ≤ n → n < N (j + 1) →
      |X n - X (N j)| / N j ≤ a h + b h j) :
    Tendsto (fun n ↦ X n / n) atTop (𝓝 c) := by
  apply tendsto_normalized_of_blockDiscrepancy hN hratio hsparse
  apply tendsto_zero_of_eventual_parameter_bounds
    (Eventually.of_forall (normalizedBlockDiscrepancy_nonneg N hN X)) ha hb
  intro h
  exact (hbound h).mono fun j hj ↦ normalizedBlockDiscrepancy_le N hN X hj

/-- Summable exceptional block events give almost-sure interpolation. -/
theorem ae_tendsto_normalized_of_sparse_blocks {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {N : ℕ → ℕ} {X : ℕ → Ω → ℝ} {ε : ℕ → ℝ} {c : ℝ}
    {E : ℕ → Set Ω} (hN : StrictMono N)
    (hratio : Tendsto (fun j ↦ (N (j + 1) : ℝ) / N j) atTop (𝓝 1))
    (hsparse : ∀ᵐ ω ∂μ, Tendsto (fun j ↦ X (N j) ω / N j) atTop (𝓝 c))
    (hε : Tendsto ε atTop (𝓝 0)) (hE : (∑' j, μ (E j)) ≠ ∞)
    (hblock : ∀ j ω, ω ∉ E j → ∀ n, N j ≤ n → n < N (j + 1) →
      |X n ω - X (N j) ω| ≤ ε j * N j) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω / n) atTop (𝓝 c) := by
  filter_upwards [hsparse, ae_eventually_notMem hE] with ω hω hωE
  apply tendsto_normalized_of_sparse_blocks hN hratio hω hε
  exact hωE.mono fun j hj ↦ hblock j ω hj

/-- A countable family of summable exceptional-event bounds gives almost-sure
interpolation from fixed-parameter estimates. -/
theorem ae_tendsto_normalized_of_parameter_bounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {N : ℕ → ℕ} {X : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    {b : ℕ → ℕ → ℝ} {c : ℝ} {E : ℕ → ℕ → Set Ω} (hN : StrictMono N)
    (hratio : Tendsto (fun j ↦ (N (j + 1) : ℝ) / N j) atTop (𝓝 1))
    (hsparse : ∀ᵐ ω ∂μ, Tendsto (fun j ↦ X (N j) ω / N j) atTop (𝓝 c))
    (ha : Tendsto a atTop (𝓝 0)) (hb : ∀ h, Tendsto (b h) atTop (𝓝 0))
    (hE : ∀ h, (∑' j, μ (E h j)) ≠ ∞)
    (hblock : ∀ h j ω, ω ∉ E h j → ∀ n, N j ≤ n → n < N (j + 1) →
      |X n ω - X (N j) ω| / N j ≤ a h + b h j) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω / n) atTop (𝓝 c) := by
  have hEvents : ∀ᵐ ω ∂μ, ∀ h, ∀ᶠ j in atTop, ω ∉ E h j :=
    ae_all_iff.mpr fun h ↦ ae_eventually_notMem (hE h)
  filter_upwards [hsparse, hEvents] with ω hω hωE
  apply tendsto_normalized_of_parameter_bounds hN hratio hω ha hb
  intro h
  exact (hωE h).mono fun j hj ↦ hblock h j ω hj

end Erdos522

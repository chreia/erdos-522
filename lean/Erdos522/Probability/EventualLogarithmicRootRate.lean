/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.RademacherLogarithmicRootRate

/-!
# The logarithmic almost-sure rate as an eventual bound

`Erdos522.ae_rademacher_logarithmic_root_rate` bounds a real `limsup`. Mathlib
assigns the value `0` to the real `limsup` of a sequence that is not bounded
above, so that inequality alone does not exclude an unbounded sequence. The
theorems below state the rate directly: for every constant `c > 2000 log 2`,
eventually `log n * |ν_n(1) / n - 1/2| ≤ c`. In particular the sequence is
eventually bounded above, and its `limsup` in the extended reals is at most
`2000 log 2`.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- A uniform block envelope with logarithmic limit `C` bounds every degree
eventually by any constant larger than `C`. -/
theorem eventually_logarithmic_rate_of_block_bounds {N : ℕ → ℕ} {d e : ℕ → ℝ} {C : ℝ}
    (hN : StrictMono N)
    (hratio : Tendsto (fun j => (N (j + 1) : ℝ) / N j) atTop (𝓝 1))
    (hd : ∀ n, 0 ≤ d n)
    (he : Tendsto (fun j => Real.log (N j) * e j) atTop (𝓝 C))
    (hblock : ∀ᶠ j : ℕ in atTop, ∀ n, N j ≤ n → n < N (j + 1) → d n ≤ e j) :
    ∀ c, C < c → ∀ᶠ n : ℕ in atTop, Real.log n * d n ≤ c := by
  intro c hc
  have hi := tendsto_blockIndex hN
  have ht : Tendsto (fun j => Real.log (N (j + 1)) * e j) atTop (𝓝 C) := by
    have h := (tendsto_log_consecutive_degree_ratio hN hratio).mul he
    simp only [one_mul] at h
    apply h.congr'
    filter_upwards [hN.tendsto_atTop.eventually_ge_atTop 2] with j hj
    have hl : Real.log (N j) ≠ 0 := (Real.log_pos (by exact_mod_cast hj)).ne'
    field_simp
  have hupper : ∀ᶠ n : ℕ in atTop, Real.log n * d n ≤
      Real.log (N (blockIndex N n + 1)) * e (blockIndex N n) := by
    filter_upwards [eventually_blockIndex_bounds hN, hi.eventually hblock] with n hn hb
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.1.trans_le hn.2.1
    have hdn := hb n hn.2.1 hn.2.2
    have hep : 0 ≤ e (blockIndex N n) := (hd n).trans hdn
    calc
      _ ≤ Real.log n * e (blockIndex N n) :=
        mul_le_mul_of_nonneg_left hdn (Real.log_natCast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.log_le_log hnpos (by exact_mod_cast hn.2.2.le)) hep
  filter_upwards [hupper, (ht.comp hi).eventually_le_const hc] with n h1 h2
  exact h1.trans h2

/-- Almost surely, for every `c > 2000 log 2`, the logarithmically scaled deviation
of the unit-disk root fraction from one half is eventually at most `c`. -/
theorem ae_rademacher_logarithmic_root_rate_eventually :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ c : ℝ, 2000 * Real.log 2 < c →
      ∀ᶠ n : ℕ in atTop, Real.log n * |rademacherRadialFraction ω n 1 - 1 / 2| ≤ c := by
  obtain ⟨H, B, _, hB, hbound⟩ := exists_ae_logarithmic_root_rate_envelope
  filter_upwards [hbound] with ω hω
  apply eventually_logarithmic_rate_of_block_bounds
    (strictMono_realPowerDegree (by norm_num : (1 : ℝ) ≤ 8))
    (tendsto_realPowerDegree_ratio (by norm_num : (1 : ℝ) < 8))
    (fun n => abs_nonneg (rademacherRadialFraction ω n 1 - 1 / 2))
    (tendsto_log_mul_logarithmicRootRateEnvelope H hB)
  filter_upwards [hω] with j hj
  intro n hnl hnu
  let m := n - realPowerDegree 8 j
  have hnm : realPowerDegree 8 j + m = n := Nat.add_sub_of_le hnl
  have hm : m ≤ realPowerBlockLength 8 j := by
    have hend := realPowerBlockLength_endpoint (by norm_num : (1 : ℝ) ≤ 8) j
    omega
  simpa only [hnm] using hj m hm

end Erdos522

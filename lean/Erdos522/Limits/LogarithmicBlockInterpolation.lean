/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Limits.LogarithmicAnnularScales
import Erdos522.Limits.SparseToDense
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Logarithmic rates from sparse degree blocks

Consecutive sparse degrees with ratio tending to one have the same
logarithmic normalization. Uniform block bounds therefore preserve a
limiting logarithmic-rate constant without enlargement.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- Consecutive degree logarithms have ratio one whenever the degrees do. -/
theorem tendsto_log_consecutive_degree_ratio {N : ℕ → ℕ} (hN : StrictMono N)
    (hratio : Tendsto (fun j => (N (j + 1) : ℝ) / N j) atTop (𝓝 1)) :
    Tendsto (fun j => Real.log (N (j + 1)) / Real.log (N j)) atTop (𝓝 1) := by
  have ht := hN.tendsto_atTop
  have hlog := Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp ht)
  have hsmall := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  simp only [Real.log_one] at hsmall
  have hlim := (hsmall.mul hlog.inv_tendsto_atTop).const_add 1
  simp only [zero_mul, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [ht.eventually_ge_atTop 2] with j hj
  have hjpos : (0 : ℝ) < N j := by exact_mod_cast (show 0 < N j by omega)
  have hjnext : (0 : ℝ) < N (j + 1) := by
    exact_mod_cast (show 0 < N (j + 1) from (by omega : 0 < N j).trans_le (hN.monotone (Nat.le_succ j)))
  have hlogpos : 0 < Real.log (N j) := Real.log_pos (by exact_mod_cast hj)
  dsimp only [Function.comp_def, Pi.inv_apply]
  rw [Real.log_div hjnext.ne' hjpos.ne']
  field_simp
  ring

/-- A uniform block envelope transfers its logarithmic limit to an all-degree
upper rate with exactly the same constant. -/
theorem limsup_logarithmic_rate_of_block_bounds {N : ℕ → ℕ} {d e : ℕ → ℝ} {C : ℝ}
    (hN : StrictMono N)
    (hratio : Tendsto (fun j => (N (j + 1) : ℝ) / N j) atTop (𝓝 1))
    (hd : ∀ n, 0 ≤ d n)
    (he : Tendsto (fun j => Real.log (N j) * e j) atTop (𝓝 C))
    (hblock : ∀ᶠ j : ℕ in atTop, ∀ n, N j ≤ n → n < N (j + 1) → d n ≤ e j) :
    limsup (fun n : ℕ => Real.log n * d n) atTop ≤ C := by
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
  have hlimit := ht.comp hi
  have hbound : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => Real.log (N (blockIndex N n + 1)) * e (blockIndex N n)) :=
    isBoundedUnder_of_eventually_le (hlimit.eventually_le_const (show C < C + 1 by linarith))
  have hbelow : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => Real.log n * d n) :=
    isCoboundedUnder_le_of_le atTop (fun n => mul_nonneg (Real.log_natCast_nonneg n) (hd n))
  exact (limsup_le_limsup hupper hbelow hbound).trans_eq hlimit.limsup_eq

/-- A logarithmic factor still leaves real-power block lengths negligible. -/
theorem tendsto_log_mul_realPowerBlockLength_div {q : ℝ} (hq : 1 < q) :
    Tendsto (fun j : ℕ => Real.log (realPowerDegree q j) *
      (realPowerBlockLength q j : ℝ) / realPowerDegree q j) atTop (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have ht := tendsto_realPowerDegree hq0
  have hbound := ((tendsto_log_pow_div_nat_rpow 1
    (show 0 < 1 / q by positivity)).const_mul (2 + q * 2 ^ q)).comp ht
  simp only [pow_one, mul_zero, Function.comp_def] at hbound
  apply squeeze_zero (fun j => by positivity) _ hbound
  intro j
  by_cases hj : 2 ≤ j
  · have hn : (0 : ℝ) < realPowerDegree q j := by
      exact_mod_cast (show 0 < realPowerDegree q j from
        (by omega : 0 < j).trans_le ((strictMono_realPowerDegree hq.le).id_le j))
    calc
      _ ≤ Real.log (realPowerDegree q j) *
          ((2 + q * 2 ^ q) * (realPowerDegree q j : ℝ) ^ (1 - 1 / q)) / realPowerDegree q j := by
        gcongr
        exact realPowerBlockLength_le_rpow hq hj
      _ = _ := by
        rw [show Real.log (realPowerDegree q j) *
            ((2 + q * 2 ^ q) * (realPowerDegree q j : ℝ) ^ (1 - 1 / q)) / realPowerDegree q j =
          (2 + q * 2 ^ q) * Real.log (realPowerDegree q j) *
            ((realPowerDegree q j : ℝ) ^ (1 - 1 / q) / realPowerDegree q j) by ring,
          ← Real.rpow_sub_one hn.ne']
        rw [show 1 - 1 / q - 1 = -(1 / q) by ring, Real.rpow_neg hn.le]
        ring
  · interval_cases j <;> simp [realPowerDegree, Real.zero_rpow (by linarith : q ≠ 0)]

end Erdos522

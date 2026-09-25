/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Degree schedules given by real powers

The degrees `⌊j^q⌋` have short consecutive blocks when `q > 1`.
The floor changes each degree by less than one, so summability has the
same threshold as for the corresponding real power.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace Erdos522

/-- The integer degree associated with a real power of the index. -/
def realPowerDegree (q : ℝ) (j : ℕ) : ℕ := ⌊(j : ℝ) ^ q⌋₊

/-- The number of appended coefficients in a consecutive real-power block. -/
def realPowerBlockLength (q : ℝ) (j : ℕ) : ℕ :=
  realPowerDegree q (j + 1) - realPowerDegree q j

theorem realPowerDegree_le (q : ℝ) (j : ℕ) :
    (realPowerDegree q j : ℝ) ≤ (j : ℝ) ^ q :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg j) q)

theorem lt_realPowerDegree_add_one (q : ℝ) (j : ℕ) :
    (j : ℝ) ^ q < realPowerDegree q j + 1 :=
  Nat.lt_floor_add_one _

theorem tendsto_realPowerDegree {q : ℝ} (hq : 0 < q) :
    Tendsto (realPowerDegree q) atTop atTop :=
  tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop hq).comp (tendsto_natCast_atTop_atTop (R := ℝ)))

/-- Flooring preserves the leading asymptotic term of the degree. -/
theorem tendsto_realPowerDegree_div_rpow {q : ℝ} (hq : 0 < q) :
    Tendsto (fun j : ℕ => (realPowerDegree q j : ℝ) / (j : ℝ) ^ q)
      atTop (𝓝 1) :=
  tendsto_nat_floor_div_atTop.comp
    ((tendsto_rpow_atTop hq).comp (tendsto_natCast_atTop_atTop (R := ℝ)))

/-- On a positive unit interval, a power increment is a value of its derivative. -/
theorem exists_real_power_increment {q : ℝ} (hq : 1 ≤ q) {j : ℕ} (_hj : 1 ≤ j) :
    ∃ c ∈ Ioo (j : ℝ) ((j : ℝ) + 1),
      ((j : ℝ) + 1) ^ q - (j : ℝ) ^ q = q * c ^ (q - 1) := by
  have hdiff := Real.differentiable_rpow_const hq
  obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_slope (fun x : ℝ => x ^ q)
    (show (j : ℝ) < (j : ℝ) + 1 by linarith)
    hdiff.continuous.continuousOn hdiff.differentiableOn
  refine ⟨c, hc, ?_⟩
  rw [(Real.hasDerivAt_rpow_const (Or.inr hq)).deriv] at hderiv
  simpa only [add_sub_cancel_left, div_one] using hderiv.symm

/-- For exponents at least one the rounded degrees are strictly increasing. -/
theorem strictMono_realPowerDegree {q : ℝ} (hq : 1 ≤ q) :
    StrictMono (realPowerDegree q) := by
  apply strictMono_nat_of_lt_succ
  intro j
  by_cases hj : j = 0
  · subst j
    simp [realPowerDegree, Real.zero_rpow (by linarith : q ≠ 0)]
  have hj1 : 1 ≤ j := by omega
  obtain ⟨c, hc, hinc⟩ := exists_real_power_increment hq hj1
  have hc1 : 1 ≤ c := (by exact_mod_cast hj1 : (1 : ℝ) ≤ j).trans hc.1.le
  have hp : 1 ≤ c ^ (q - 1) := Real.one_le_rpow hc1 (by linarith)
  have hincrement : (j : ℝ) ^ q + 1 ≤ ((j : ℝ) + 1) ^ q := by
    have : 1 ≤ q * c ^ (q - 1) := by nlinarith
    linarith
  have hfloor := Nat.floor_mono hincrement
  rw [Nat.floor_add_one (Real.rpow_nonneg (Nat.cast_nonneg j) q)] at hfloor
  simpa only [realPowerDegree, Nat.cast_add, Nat.cast_one] using
    (show ⌊(j : ℝ) ^ q⌋₊ < ⌊((j : ℝ) + 1) ^ q⌋₊ by omega)

theorem realPowerBlockLength_pos {q : ℝ} (hq : 1 ≤ q) (j : ℕ) :
    0 < realPowerBlockLength q j :=
  Nat.sub_pos_of_lt (strictMono_realPowerDegree hq (Nat.lt_succ_self j))

theorem realPowerBlockLength_endpoint {q : ℝ} (hq : 1 ≤ q) (j : ℕ) :
    realPowerDegree q j + realPowerBlockLength q j = realPowerDegree q (j + 1) :=
  Nat.add_sub_of_le ((strictMono_realPowerDegree hq).monotone (Nat.le_succ j))

/-- Above degree two, rounding loses at most half the underlying real power. -/
theorem half_rpow_le_realPowerDegree {q : ℝ} (hq : 1 ≤ q) {j : ℕ} (hj : 2 ≤ j) :
    (j : ℝ) ^ q / 2 ≤ realPowerDegree q j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hp : (2 : ℝ) ≤ (j : ℝ) ^ q :=
    (by exact_mod_cast hj : (2 : ℝ) ≤ j).trans
      (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hj1 hq)
  have hf := lt_realPowerDegree_add_one q j
  linarith

/-- A real-power block satisfies the explicit degree bound used by the maximal-tail
estimate. -/
theorem realPowerBlockLength_le_rpow {q : ℝ} (hq : 1 < q) {j : ℕ} (hj : 2 ≤ j) :
    (realPowerBlockLength q j : ℝ) ≤
      (2 + q * 2 ^ q) * (realPowerDegree q j : ℝ) ^ (1 - 1 / q) := by
  have hq0 : 0 < q := by linarith
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hN1 : (1 : ℝ) ≤ realPowerDegree q j := by
    exact_mod_cast (strictMono_realPowerDegree hq.le).id_le j |>.trans' (by omega : 1 ≤ j)
  have hp0 : 0 ≤ 1 - 1 / q := by
    exact sub_nonneg.mpr ((div_le_one hq0).mpr hq.le)
  have hp1 : 1 - 1 / q ≤ 1 := sub_le_self _ (by positivity)
  have hhalf := half_rpow_le_realPowerDegree hq.le hj
  have hpower : (j : ℝ) ^ (q - 1) ≤
      2 ^ (1 - 1 / q) * (realPowerDegree q j : ℝ) ^ (1 - 1 / q) := by
    calc
      _ = ((j : ℝ) ^ q) ^ (1 - 1 / q) := by
        rw [← Real.rpow_mul hj0.le]
        congr 1
        field_simp
      _ ≤ (2 * (realPowerDegree q j : ℝ)) ^ (1 - 1 / q) := by
        apply Real.rpow_le_rpow (Real.rpow_nonneg hj0.le _) _ hp0
        linarith
      _ = _ := Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
  obtain ⟨c, hc, hinc⟩ := exists_real_power_increment hq.le (by omega : 1 ≤ j)
  have hc0 : 0 ≤ c := (hj0.trans hc.1).le
  have hincbound : ((j : ℝ) + 1) ^ q - (j : ℝ) ^ q ≤
      q * 2 ^ q * (realPowerDegree q j : ℝ) ^ (1 - 1 / q) := by
    rw [hinc]
    calc
      q * c ^ (q - 1) ≤ q * (2 * (j : ℝ)) ^ (q - 1) := by
        gcongr
        linarith [hc.2]
      _ = q * (2 ^ (q - 1) * (j : ℝ) ^ (q - 1)) := by
        rw [Real.mul_rpow (by norm_num) hj0.le]
      _ ≤ q * (2 ^ (q - 1) *
          (2 ^ (1 - 1 / q) * (realPowerDegree q j : ℝ) ^ (1 - 1 / q))) := by
        gcongr
      _ = q * 2 ^ ((q - 1) + (1 - 1 / q)) *
          (realPowerDegree q j : ℝ) ^ (1 - 1 / q) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        ring
      _ ≤ _ := by
        gcongr <;> linarith
  have hcast : (realPowerBlockLength q j : ℝ) =
      (realPowerDegree q (j + 1) : ℝ) - realPowerDegree q j := by
    exact Nat.cast_sub ((strictMono_realPowerDegree hq.le).monotone (Nat.le_succ j))
  have hupper := realPowerDegree_le q (j + 1)
  have hlower := lt_realPowerDegree_add_one q j
  have hpow1 := Real.one_le_rpow hN1 hp0
  rw [hcast]
  push_cast at hupper
  nlinarith

/-- The relative block length tends to zero for every real exponent greater than one. -/
theorem tendsto_realPowerBlockLength_div {q : ℝ} (hq : 1 < q) :
    Tendsto (fun j : ℕ => (realPowerBlockLength q j : ℝ) / realPowerDegree q j)
      atTop (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have hN := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_realPowerDegree hq0)
  have hlim := (tendsto_rpow_neg_atTop (show 0 < 1 / q by positivity)).comp hN
  simp only [Function.comp_def, ← neg_div] at hlim
  have hboundlim := hlim.const_mul (2 + q * 2 ^ q)
  simp only [mul_zero] at hboundlim
  apply squeeze_zero' (Eventually.of_forall fun j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    ?_ hboundlim
  filter_upwards [eventually_ge_atTop 2] with j hj
  have hNpos : 0 < realPowerDegree q j :=
    (show 0 < j by omega).trans_le ((strictMono_realPowerDegree hq.le).id_le j)
  have hn : (0 : ℝ) < realPowerDegree q j := by exact_mod_cast hNpos
  calc
    _ ≤ ((2 + q * 2 ^ q) * (realPowerDegree q j : ℝ) ^ (1 - 1 / q)) /
        realPowerDegree q j := div_le_div_of_nonneg_right
          (realPowerBlockLength_le_rpow hq hj) hn.le
    _ = (2 + q * 2 ^ q) * (realPowerDegree q j : ℝ) ^ (-1 / q) := by
      rw [mul_div_assoc]
      nth_rw 2 [← Real.rpow_one (realPowerDegree q j : ℝ)]
      rw [← Real.rpow_sub hn]
      congr 2
      ring

/-- Consecutive rounded real powers have ratio tending to one. -/
theorem tendsto_realPowerDegree_ratio {q : ℝ} (hq : 1 < q) :
    Tendsto (fun j : ℕ => (realPowerDegree q (j + 1) : ℝ) / realPowerDegree q j)
      atTop (𝓝 1) := by
  have hlim := (tendsto_realPowerBlockLength_div hq).const_add 1
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [(tendsto_realPowerDegree (show 0 < q by linarith)).eventually_ge_atTop 1]
    with j hj
  have hn : (realPowerDegree q j : ℝ) ≠ 0 := by exact_mod_cast (show realPowerDegree q j ≠ 0 by omega)
  rw [← realPowerBlockLength_endpoint hq.le j, Nat.cast_add, add_div, div_self hn]

/-- Eventually no block is longer than its lower degree. -/
theorem eventually_realPowerBlockLength_le_degree {q : ℝ} (hq : 1 < q) :
    ∀ᶠ j : ℕ in atTop, realPowerBlockLength q j ≤ realPowerDegree q j := by
  filter_upwards [(tendsto_realPowerBlockLength_div hq).eventually_lt_const
      (show (0 : ℝ) < 1 by norm_num),
    (tendsto_realPowerDegree (show 0 < q by linarith)).eventually_ge_atTop 1] with j hj hN
  have hn : (0 : ℝ) < realPowerDegree q j := by exact_mod_cast (show 0 < realPowerDegree q j by omega)
  exact_mod_cast ((div_lt_one hn).mp hj).le

/-- Every negative degree power with the expected strict exponent is summable. -/
theorem summable_realPowerDegree_rpow {q a : ℝ} (hq : 0 < q) (ha : q * a < -1) :
    Summable (fun j : ℕ => (realPowerDegree q j : ℝ) ^ a) := by
  have ha0 : a < 0 := by nlinarith
  have hratio := (tendsto_realPowerDegree_div_rpow hq).eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  have hsum := (Real.summable_nat_rpow.mpr ha).mul_left ((1 / 2 : ℝ) ^ a)
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [hratio, eventually_ge_atTop 1] with j hj hj1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hp : 0 < (j : ℝ) ^ q := Real.rpow_pos_of_pos hj0 q
  have hhalf : (1 / 2 : ℝ) * (j : ℝ) ^ q ≤ realPowerDegree q j :=
    (le_div_iff₀ hp).mp hj.le
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  calc
    _ ≤ ((1 / 2 : ℝ) * (j : ℝ) ^ q) ^ a :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hhalf ha0.le
    _ = (1 / 2 : ℝ) ^ a * (j : ℝ) ^ (q * a) := by
      rw [Real.mul_rpow (by norm_num) hp.le, ← Real.rpow_mul hj0.le]

/-- Fixed logarithmic factors do not change the strict summability threshold. -/
theorem summable_realPowerDegree_rpow_mul_log_pow {q a : ℝ}
    (hq : 0 < q) (ha : q * a < -1) (k : ℕ) :
    Summable (fun j : ℕ => (realPowerDegree q j : ℝ) ^ a *
      (Real.log (realPowerDegree q j)) ^ k) := by
  let ε := (-1 / q - a) / 2
  have hε : 0 < ε := by
    have : a < -1 / q := (lt_div_iff₀ hq).mpr (by nlinarith [ha])
    dsimp [ε]
    linarith
  have hexponent : q * (a + ε) < -1 := by
    dsimp [ε]
    field_simp
    nlinarith [ha]
  have hsum := summable_realPowerDegree_rpow hq hexponent
  have hlog : Tendsto (fun j : ℕ =>
      (Real.log (realPowerDegree q j)) ^ k / (realPowerDegree q j : ℝ) ^ ε)
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hε).tendsto_div_nhds_zero
    simpa only [Function.comp_def, Real.rpow_natCast] using h.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_realPowerDegree hq))
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [hlog.eventually_lt_const (show (0 : ℝ) < 1 by norm_num),
    (tendsto_realPowerDegree hq).eventually_ge_atTop 1] with j hj hN
  have hn1 : (1 : ℝ) ≤ realPowerDegree q j := by exact_mod_cast hN
  have hn : (0 : ℝ) < realPowerDegree q j := lt_of_lt_of_le zero_lt_one hn1
  have hlognonneg : 0 ≤ Real.log (realPowerDegree q j) := Real.log_nonneg hn1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (realPowerDegree q j : ℝ) ^ a * (realPowerDegree q j : ℝ) ^ ε := by
      apply mul_le_mul_of_nonneg_left ((div_lt_one (Real.rpow_pos_of_pos hn ε)).mp hj).le
        (Real.rpow_nonneg hn.le a)
    _ = _ := (Real.rpow_add hn a ε).symm

end Erdos522

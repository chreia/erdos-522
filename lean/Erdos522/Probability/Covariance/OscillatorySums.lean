/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Oscillatory sums with radial weights

Summation by parts bounds Fourier sums by endpoint values and total variation.
For the covariance kernels of polynomial values and derivatives the weights
are products of two monotone sequences, so their variation is explicit.
-/

noncomputable section
open scoped BigOperators
namespace Erdos522

/-- The elementary summation-by-parts identity for a weighted geometric sum. -/
theorem weighted_geometric_identity (w : ℕ → ℂ) (z : ℂ) (N : ℕ) :
    (1 - z) * (∑ k ∈ Finset.range (N + 1), w k * z ^ k) =
      w 0 - w N * z ^ (N + 1) +
        ∑ k ∈ Finset.range N, (w (k + 1) - w k) * z ^ (k + 1) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ]
    simp only [pow_succ]
    ring

/-- Endpoint values and total variation control a sum on the unit circle. -/
theorem norm_weighted_geometric_sum_le (w : ℕ → ℂ) (z : ℂ)
    (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (N : ℕ) :
    ‖∑ k ∈ Finset.range (N + 1), w k * z ^ k‖ ≤
      (‖w 0‖ + ‖w N‖ + ∑ k ∈ Finset.range N, ‖w (k + 1) - w k‖) / ‖1 - z‖ := by
  have hden : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1.symm)
  apply (le_div_iff₀ hden).mpr
  rw [mul_comm, ← norm_mul, weighted_geometric_identity]
  calc
    _ ≤ ‖w 0‖ + ‖w N * z ^ (N + 1)‖ +
        ‖∑ k ∈ Finset.range N, (w (k + 1) - w k) * z ^ (k + 1)‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ ‖w 0‖ + ‖w N‖ +
        ∑ k ∈ Finset.range N, ‖w (k + 1) - w k‖ := by
      simp only [norm_mul, norm_pow, hz, one_pow, mul_one]
      apply add_le_add_right
      simpa only [norm_mul, norm_pow, hz, one_pow, mul_one] using
        (norm_sum_le (Finset.range N)
          (fun k => (w (k + 1) - w k) * z ^ (k + 1)))

/-- The variation of a monotone sequence is its endpoint increment. -/
theorem sum_abs_sub_of_monotone (f : ℕ → ℝ) (hf : Monotone f) (N : ℕ) :
    (∑ k ∈ Finset.range N, |f (k + 1) - f k|) = f N - f 0 := by
  simp_rw [abs_of_nonneg (sub_nonneg.mpr (hf (Nat.le_succ _)))]
  exact Finset.sum_range_sub f N

/-- The variation of an antitone sequence is its endpoint decrement. -/
theorem sum_abs_sub_of_antitone (f : ℕ → ℝ) (hf : Antitone f) (N : ℕ) :
    (∑ k ∈ Finset.range N, |f (k + 1) - f k|) = f 0 - f N := by
  simp_rw [abs_of_nonpos (sub_nonpos.mpr (hf (Nat.le_succ _))), neg_sub]
  exact Finset.sum_range_sub' f N

/-- Products of a bounded monotone sequence with an increasing unit-bounded
sequence have at most twice the first bound in total variation. -/
theorem sum_abs_sub_mul_le (f g : ℕ → ℝ) (N : ℕ) (A : ℝ)
    (hf : Monotone f ∨ Antitone f) (hg : Monotone g)
    (hf0 : ∀ k ≤ N, 0 ≤ f k) (hfA : ∀ k ≤ N, f k ≤ A)
    (hg0 : ∀ k ≤ N, 0 ≤ g k) (hg1 : ∀ k ≤ N, g k ≤ 1) :
    (∑ k ∈ Finset.range N, |f (k + 1) * g (k + 1) - f k * g k|) ≤ 2 * A := by
  have hA : 0 ≤ A := (hf0 0 (Nat.zero_le N)).trans (hfA 0 (Nat.zero_le N))
  have hvar : (∑ k ∈ Finset.range N, |f (k + 1) - f k|) ≤ A := by
    rcases hf with hf | hf
    · rw [sum_abs_sub_of_monotone f hf N]
      linarith [hfA N le_rfl, hf0 0 (Nat.zero_le N)]
    · rw [sum_abs_sub_of_antitone f hf N]
      linarith [hfA 0 (Nat.zero_le N), hf0 N le_rfl]
  calc
    _ ≤ ∑ k ∈ Finset.range N,
        (A * (g (k + 1) - g k) + |f (k + 1) - f k|) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN : k ≤ N := (Finset.mem_range.mp hk).le
      have hsN : k + 1 ≤ N := Finset.mem_range.mp hk
      have he : f (k + 1) * g (k + 1) - f k * g k =
          f (k + 1) * (g (k + 1) - g k) + (f (k + 1) - f k) * g k := by ring
      rw [he]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (hf0 _ hsN),
        abs_of_nonneg (sub_nonneg.mpr (hg (Nat.le_succ k))), abs_of_nonneg (hg0 _ hkN)]
      exact add_le_add (mul_le_mul_of_nonneg_right (hfA _ hsN)
        (sub_nonneg.mpr (hg (Nat.le_succ k))))
        (by simpa using mul_le_mul_of_nonneg_left (hg1 _ hkN) (abs_nonneg _))
    _ = A * (g N - g 0) + ∑ k ∈ Finset.range N, |f (k + 1) - f k| := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub]
    _ ≤ 2 * A := by
      have : A * (g N - g 0) ≤ A := by
        calc
          A * (g N - g 0) ≤ A * 1 :=
            mul_le_mul_of_nonneg_left (by linarith [hg1 N le_rfl, hg0 0 (Nat.zero_le N)]) hA
          _ = A := mul_one A
      linarith

/-- A product of monotone radial and index weights has an explicit Fourier bound. -/
theorem norm_monotone_weighted_geometric_sum_le (f g : ℕ → ℝ) (N : ℕ) (A : ℝ)
    (hf : Monotone f ∨ Antitone f) (hg : Monotone g)
    (hf0 : ∀ k ≤ N, 0 ≤ f k) (hfA : ∀ k ≤ N, f k ≤ A)
    (hg0 : ∀ k ≤ N, 0 ≤ g k) (hg1 : ∀ k ≤ N, g k ≤ 1)
    (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ‖∑ k ∈ Finset.range (N + 1), (f k * g k : ℝ) * z ^ k‖ ≤ 4 * A / ‖1 - z‖ := by
  have hA : 0 ≤ A := (hf0 0 (Nat.zero_le N)).trans (hfA 0 (Nat.zero_le N))
  have hend (k : ℕ) (hk : k ≤ N) : |f k * g k| ≤ A := by
    rw [abs_of_nonneg (mul_nonneg (hf0 k hk) (hg0 k hk))]
    exact (mul_le_mul_of_nonneg_left (hg1 k hk) (hf0 k hk)).trans (by simpa using hfA k hk)
  refine (norm_weighted_geometric_sum_le (fun k => (f k * g k : ℝ)) z hz hz1 N).trans ?_
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  simp only [Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_sub]
  linarith [hend 0 (Nat.zero_le N), hend N le_rfl, sum_abs_sub_mul_le f g N A hf hg hf0 hfA hg0 hg1]

/-- Powers at distance at most `K/N` outside the circle are bounded by `exp K`. -/
theorem radial_power_upper (N k : ℕ) (hN : 0 < N) (hk : k ≤ N)
    (K r : ℝ) (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hr : r ≤ 1 + K / N) :
    r ^ k ≤ Real.exp K := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr' : r ≤ Real.exp (K / N) := hr.trans (by linarith [Real.add_one_le_exp (K / N)])
  calc
    r ^ k ≤ Real.exp (K / N) ^ k := pow_le_pow_left₀ hr0 hr' k
    _ = Real.exp ((k : ℝ) * (K / N)) := (Real.exp_nat_mul _ k).symm
    _ ≤ Real.exp K := by
      apply Real.exp_le_exp.mpr
      calc
        (k : ℝ) * (K / N) ≤ (N : ℝ) * (K / N) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
        _ = K := by field_simp

/-- Geometric radial weights are monotone in one of the two directions. -/
theorem monotone_or_antitone_geometric (q : ℝ) (hq : 0 ≤ q) :
    Monotone (fun k : ℕ => q ^ k) ∨ Antitone (fun k : ℕ => q ^ k) := by
  rcases le_total 1 q with hq1 | hq1
  · exact Or.inl (fun _ _ h => pow_le_pow_right₀ hq1 h)
  · exact Or.inr (fun _ _ h => pow_le_pow_of_le_one hq hq1 h)

/-- The radial-index kernel bound before converting chord length to angle. -/
theorem norm_radial_index_sum_le (N j : ℕ) (hN : 0 < N)
    (K r s : ℝ) (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hr : r ≤ 1 + K / N) (hs : s ≤ 1 + K / N)
    (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ‖∑ k ∈ Finset.range (N + 1),
      ((r * s) ^ k * ((k : ℝ) / N) ^ j : ℝ) * z ^ k‖ ≤
      4 * Real.exp (2 * K) / ‖1 - z‖ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  apply norm_monotone_weighted_geometric_sum_le
      (fun k => (r * s) ^ k) (fun k => ((k : ℝ) / N) ^ j) N (Real.exp (2 * K))
      (monotone_or_antitone_geometric _ (mul_nonneg hr0 hs0))
  · intro k l hkl
    exact pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_right (by exact_mod_cast hkl) hn.le) j
  · intro k _; positivity
  · intro k hk
    rw [mul_pow]
    calc
      r ^ k * s ^ k ≤ Real.exp K * Real.exp K :=
        mul_le_mul (radial_power_upper N k hN hk K r hK hr0 hr)
          (radial_power_upper N k hN hk K s hK hs0 hs) (pow_nonneg hs0 k) (Real.exp_nonneg K)
      _ = Real.exp (2 * K) := by rw [← Real.exp_add]; congr 1; ring
  · intro k _; positivity
  · intro k hk
    exact pow_le_one₀ (by positivity) ((div_le_one hn).mpr (by exact_mod_cast hk))
  · exact hz
  · exact hz1

/-- Chord length controls the absolute principal angle. -/
theorem angle_le_chord (t : ℝ) (ht : |t| ≤ Real.pi) :
    2 / Real.pi * |t| ≤ ‖1 - Complex.exp (Complex.I * t)‖ := by
  rw [norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := Real.mul_abs_le_abs_sin (x := t / 2)
    (by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  nlinarith

/-- Abel's estimate for every index power, at a nonzero principal angle.
For values and first derivatives only powers zero, one, and two occur. -/
theorem normalized_radial_index_sum_le (N j : ℕ) (hN : 0 < N)
    (K r s t : ℝ) (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hr : r ≤ 1 + K / N) (hs : s ≤ 1 + K / N)
    (ht : |t| ≤ Real.pi) (ht0 : t ≠ 0) :
    ‖(1 / (N : ℂ)) * ∑ k ∈ Finset.range (N + 1),
      ((r * s) ^ k * ((k : ℝ) / N) ^ j : ℝ) *
        Complex.exp (Complex.I * t) ^ k‖ ≤
      10 * Real.exp (4 * K) / ((N : ℝ) * |t|) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have htpos : 0 < |t| := abs_pos.mpr ht0
  have hc := angle_le_chord t ht
  have hchord : 0 < ‖1 - Complex.exp (Complex.I * t)‖ :=
    lt_of_lt_of_le (by positivity) hc
  have hz1 : Complex.exp (Complex.I * t) ≠ 1 := by
    intro he
    simp [he] at hchord
  have hsum := norm_radial_index_sum_le N j hN K r s hK hr0 hs0 hr hs
    (Complex.exp (Complex.I * t)) (Complex.norm_exp_I_mul_ofReal t) hz1
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  calc
    _ ≤ (1 / (N : ℝ)) * (4 * Real.exp (2 * K) / ‖1 - Complex.exp (Complex.I * t)‖) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (1 / (N : ℝ)) * (4 * Real.exp (2 * K) / (2 / Real.pi * |t|)) := by
      gcongr
    _ = (2 * Real.pi) * Real.exp (2 * K) / ((N : ℝ) * |t|) := by field_simp; ring
    _ ≤ 10 * Real.exp (4 * K) / ((N : ℝ) * |t|) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul (by linarith [Real.pi_lt_four])
        (Real.exp_le_exp.mpr (by linarith)) (Real.exp_nonneg _) (by norm_num)

/-- The quotient-circle norm is the absolute value of the principal angle. -/
theorem angle_norm_eq_abs_toReal (θ : Real.Angle) : ‖θ‖ = |θ.toReal| := by
  conv_lhs => rw [← Real.Angle.coe_toReal θ]
  apply (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (by positivity)).mpr
  simpa only [abs_of_pos Real.two_pi_pos, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    using Real.Angle.abs_toReal_le_pi θ

/-- Replacing a real angle by its principal representative leaves its phase unchanged. -/
theorem exp_principal_angle (t : ℝ) :
    Complex.exp (Complex.I * ((t : Real.Angle).toReal : ℝ)) =
      Complex.exp (Complex.I * t) := by
  rw [mul_comm Complex.I, mul_comm Complex.I, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [Real.Angle.cos_toReal, Real.Angle.sin_toReal,
    Real.Angle.cos_coe, Real.Angle.sin_coe]

/-- The periodic Abel estimate, with distance measured on `ℝ / 2πℤ`. -/
theorem normalized_radial_index_sum_le_angle_norm (N j : ℕ) (hN : 0 < N)
    (K r s t : ℝ) (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hr : r ≤ 1 + K / N) (hs : s ≤ 1 + K / N)
    (ht : (t : Real.Angle) ≠ 0) :
    ‖(1 / (N : ℂ)) * ∑ k ∈ Finset.range (N + 1),
      ((r * s) ^ k * ((k : ℝ) / N) ^ j : ℝ) *
        Complex.exp (Complex.I * t) ^ k‖ ≤
      10 * Real.exp (4 * K) / ((N : ℝ) * ‖(t : Real.Angle)‖) := by
  have ht0 : (t : Real.Angle).toReal ≠ 0 := by
    intro he
    apply ht
    rw [← Real.Angle.coe_toReal (t : Real.Angle), he]
    rfl
  simpa only [exp_principal_angle, angle_norm_eq_abs_toReal] using
    normalized_radial_index_sum_le N j hN K r s (t : Real.Angle).toReal hK hr0 hs0 hr hs
      (Real.Angle.abs_toReal_le_pi _) ht0

/-- Inside the `K/N` annulus every radial power has a fixed positive lower bound. -/
theorem radial_power_lower (N k : ℕ) (hN : 0 < N) (hk : k ≤ N)
    (K r : ℝ) (hK : 0 ≤ K) (hNK : 2 * K ≤ N) (hr : 1 - K / N ≤ r) :
    Real.exp (-2 * K) ≤ r ^ k := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hu0 : 0 ≤ K / (N : ℝ) := by positivity
  have hu : K / (N : ℝ) ≤ 1 / 2 := (div_le_iff₀ hn).mpr (by linarith)
  have hx : 0 < 1 - K / (N : ℝ) := by linarith
  have hinv : (1 - K / (N : ℝ))⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ hx).mpr (by linarith)
  have hlog : -2 * (K / (N : ℝ)) ≤ Real.log (1 - K / (N : ℝ)) := by
    have he : 1 - (1 - K / (N : ℝ))⁻¹ =
        -(K / (N : ℝ)) * (1 - K / (N : ℝ))⁻¹ := by
      have hcancel := mul_inv_cancel₀ hx.ne'
      nlinarith
    have hi := Real.one_sub_inv_le_log_of_pos hx
    rw [he] at hi
    nlinarith [mul_le_mul_of_nonneg_left hinv hu0]
  have hbase : Real.exp (-2 * (K / (N : ℝ))) ≤ r := by
    calc
      _ ≤ Real.exp (Real.log (1 - K / (N : ℝ))) := Real.exp_le_exp.mpr hlog
      _ = 1 - K / (N : ℝ) := Real.exp_log hx
      _ ≤ r := hr
  calc
    Real.exp (-2 * K) ≤ Real.exp ((k : ℝ) * (-2 * (K / (N : ℝ)))) := by
      apply Real.exp_le_exp.mpr
      have hkn : (k : ℝ) ≤ N := by exact_mod_cast hk
      have he : (N : ℝ) * (-2 * (K / (N : ℝ))) = -2 * K := by field_simp
      rw [← he]
      exact mul_le_mul_of_nonpos_right hkn
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hu0)
    _ = Real.exp (-2 * (K / (N : ℝ))) ^ k := Real.exp_nat_mul _ k
    _ ≤ r ^ k := pow_le_pow_left₀ (Real.exp_nonneg _) hbase k

/-- The deterministic variance normalization in the `K/N` annulus. -/
theorem radial_variance_bounds (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N) :
    (N : ℝ) * Real.exp (-4 * K) ≤ ∑ k ∈ Finset.range (N + 1), r ^ (2 * k) ∧
      (∑ k ∈ Finset.range (N + 1), r ^ (2 * k)) ≤ 2 * N * Real.exp (2 * K) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hnone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hu : K / (N : ℝ) ≤ 1 / 2 := (div_le_iff₀ hn).mpr (by linarith)
  have hr0 : 0 ≤ r := by linarith
  have hlow (k : ℕ) (hk : k ≤ N) : Real.exp (-4 * K) ≤ r ^ (2 * k) := by
    have h := radial_power_lower N k hN hk K r hK hNK hrl
    calc
      Real.exp (-4 * K) = Real.exp (-2 * K) * Real.exp (-2 * K) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ r ^ k * r ^ k := mul_le_mul h h (Real.exp_nonneg _) (pow_nonneg hr0 k)
      _ = r ^ (2 * k) := by rw [← pow_add]; congr 1; omega
  have hupp (k : ℕ) (hk : k ≤ N) : r ^ (2 * k) ≤ Real.exp (2 * K) := by
    have h := radial_power_upper N k hN hk K r hK hr0 hru
    calc
      r ^ (2 * k) = r ^ k * r ^ k := by rw [← pow_add]; congr 1; omega
      _ ≤ Real.exp K * Real.exp K := mul_le_mul h h (pow_nonneg hr0 k) (Real.exp_nonneg _)
      _ = Real.exp (2 * K) := by rw [← Real.exp_add]; congr 1; ring
  constructor
  · calc
      (N : ℝ) * Real.exp (-4 * K) ≤ ((N : ℝ) + 1) * Real.exp (-4 * K) := by gcongr; linarith
      _ = ∑ k ∈ Finset.range (N + 1), Real.exp (-4 * K) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun k hk => hlow k (by simpa using hk))
  · calc
      _ ≤ ∑ k ∈ Finset.range (N + 1), Real.exp (2 * K) :=
        Finset.sum_le_sum (fun k hk => hupp k (by simpa using hk))
      _ = ((N : ℝ) + 1) * Real.exp (2 * K) := by simp
      _ ≤ 2 * N * Real.exp (2 * K) := by gcongr; linarith

end Erdos522

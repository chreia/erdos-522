/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.RademacherSequence
import Erdos522.Probability.AnnularSmallDerivativeSummability

/-!
# Almost-sure annular derivative nondegeneracy

The finite-degree estimates apply to the prefixes of one infinite coin
sequence. Borel–Cantelli gives the quantitative count bound along `j^8`.
Monotonicity in the annular width extends the countable intersection over
integer widths to every fixed real width on the same probability-one event.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- Enlarging the annulus can only increase its small-derivative zero count. -/
theorem annularSmallDerivativeZeroCount_mono (P : Polynomial ℂ) (N : ℕ) (L : ℝ)
    {K K' : ℝ} (hK : K ≤ K') :
    annularSmallDerivativeZeroCount P N K L ≤ annularSmallDerivativeZeroCount P N K' L := by
  apply zeroCountIn_mono P
  intro α hα
  exact ⟨hα.1.trans (div_le_div_of_nonneg_right hK (Nat.cast_nonneg N)), hα.2⟩

/-- At a fixed width, almost every shared coin sequence eventually satisfies the annular count bound. -/
theorem ae_eventually_annular_small_derivative_count (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      (annularSmallDerivativeZeroCount
        (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω)) (j ^ 8) K
        (((j ^ 8 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) : ℝ) ≤
          ((j ^ 8 : ℕ) : ℝ) ^ (31 / 32 : ℝ) := by
  have h := ae_eventually_rademacherPrefix_notMem (fun j => j ^ 8)
    (fun N => {v | (N : ℝ) ^ (31 / 32 : ℝ) <
      (annularSmallDerivativeZeroCount (rademacherPolynomial N v) N K
        ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)}) (summable_annular_small_derivative_failures K hK)
  filter_upwards [h] with ω hω
  exact hω.mono (fun j hj => le_of_not_gt hj)

/-- A single probability-one event supplies eventual annular nondegeneracy for every real width. -/
theorem ae_forall_annular_small_derivative_count :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ K : ℝ, ∀ᶠ j : ℕ in atTop,
      (annularSmallDerivativeZeroCount
        (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω)) (j ^ 8) K
        (((j ^ 8 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) : ℝ) ≤
          ((j ^ 8 : ℕ) : ℝ) ^ (31 / 32 : ℝ) := by
  have hnat : ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ k : ℕ, ∀ᶠ j : ℕ in atTop,
      (annularSmallDerivativeZeroCount
        (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω)) (j ^ 8) k
        (((j ^ 8 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) : ℝ) ≤
          ((j ^ 8 : ℕ) : ℝ) ^ (31 / 32 : ℝ) := by
    apply ae_all_iff.mpr
    intro k
    exact ae_eventually_annular_small_derivative_count k (Nat.cast_nonneg k)
  filter_upwards [hnat] with ω hω
  intro K
  filter_upwards [hω ⌈K⌉₊] with j hj
  have hmono := annularSmallDerivativeZeroCount_mono
    (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω)) (j ^ 8)
      (((j ^ 8 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) (Nat.le_ceil K)
  exact le_trans (by exact_mod_cast hmono) hj

/-- The fraction of annular derivative-small zeros tends to zero along the sparse degrees,
    simultaneously for every real annular width on the shared coin space. -/
theorem ae_annular_small_derivative_fraction_tendsto :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ K : ℝ,
      Tendsto (fun j : ℕ =>
        (annularSmallDerivativeZeroCount
          (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω)) (j ^ 8) K
          (((j ^ 8 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) : ℝ) / ((j ^ 8 : ℕ) : ℝ)) atTop (𝓝 0) := by
  filter_upwards [ae_forall_annular_small_derivative_count] with ω hω
  intro K
  have hlimit := (tendsto_nat_rpow_neg (by norm_num : (0 : ℝ) < 1 / 32)).comp
    (tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num))
  apply squeeze_zero' (Eventually.of_forall fun j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    ?_ hlimit
  filter_upwards [hω K, eventually_ge_atTop 1] with j hj hj1
  have hN : (0 : ℝ) < ((j ^ 8 : ℕ) : ℝ) := by exact_mod_cast (pow_pos (show 0 < j by omega) 8)
  have hquot : (((j ^ 8 : ℕ) : ℝ) ^ (31 / 32 : ℝ)) / ((j ^ 8 : ℕ) : ℝ) =
      ((j ^ 8 : ℕ) : ℝ) ^ (-(1 / 32 : ℝ)) := by
    nth_rw 2 [← Real.rpow_one ((j ^ 8 : ℕ) : ℝ)]
    rw [← Real.rpow_sub hN]
    congr 1
    norm_num
  exact (div_le_div_of_nonneg_right hj hN.le).trans_eq hquot

end Erdos522

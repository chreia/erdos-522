/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Basic.PolynomialPrefixes
import Erdos522.Probability.RademacherLogMoments
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.PSeries

/-!
# Zero runs and actual polynomial degree

An atom at zero produces initial and trailing zero runs with geometric
probabilities. A short trailing run bounds the difference between the nominal
degree and the actual degree, including the degree increase across a block.
-/

noncomputable section
open MeasureTheory Polynomial Set
open scoped BigOperators ENNReal
namespace Erdos522

/-- A coefficient law with second absolute moment one has zero-atom mass
strictly less than one. -/
theorem zero_atom_lt_one_of_second_moment_one (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hmean : (∫ z, ‖z‖ ^ 2 ∂μ) = 1) : μ.real {0} < 1 := by
  by_contra h
  have heq : μ.real {0} = 1 := le_antisymm measureReal_le_one (le_of_not_gt h)
  have hprob : μ ({0} : Set ℂ) = 1 := (ENNReal.toReal_eq_one_iff _).mp heq
  have hae : ∀ᵐ z : ℂ ∂μ, z = 0 := by
    have hmem : ∀ᵐ z : ℂ ∂μ, z ∈ ({0} : Set ℂ) :=
      (mem_ae_iff_prob_eq_one (measurableSet_singleton (0 : ℂ))).mpr hprob
    exact hmem.mono (fun _ hz => Set.mem_singleton_iff.mp hz)
  have hi : (∫ z, ‖z‖ ^ 2 ∂μ) = 0 := by
    calc
      _ = ∫ _z : ℂ, (0 : ℝ) ∂μ := integral_congr_ae (hae.mono (fun z hz => by simp [hz]))
      _ = 0 := integral_zero _ _
  linarith

/-- The event that a prescribed finite set of coefficients vanishes. -/
def zeroCoordinates {ι : Type*} (s : Finset ι) : Set (ι → ℂ) :=
  {a | ∀ k ∈ s, a k = 0}

theorem measurableSet_zeroCoordinates {ι : Type*} (s : Finset ι) :
    MeasurableSet (zeroCoordinates s) := by
  classical
  simpa only [zeroCoordinates, Set.ofPred_forall, Finset.mem_coe] using
    s.finite_toSet.measurableSet_biInter (fun k _ =>
      measurableSet_eq_fun (measurable_pi_apply k) (measurable_const (a := (0 : ℂ))))

/-- Independent coefficient laws give an exact product for a prescribed zero run. -/
theorem measure_zeroCoordinates {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)] (s : Finset ι) :
    Measure.pi μ (zeroCoordinates s) = ∏ k ∈ s, μ k {0} := by
  have heq : zeroCoordinates s = (s : Set ι).pi (fun _ => ({0} : Set ℂ)) := by
    ext a
    simp [zeroCoordinates, Set.mem_pi]
  rw [heq, Measure.pi_pi_finset]

/-- For identically distributed coefficients the zero-run probability is geometric. -/
theorem measureReal_zeroCoordinates {ι : Type*} [Fintype ι]
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (s : Finset ι) :
    (Measure.pi (fun _ : ι => μ)).real (zeroCoordinates s) = (μ.real {0}) ^ s.card := by
  rw [measureReal_def, measure_zeroCoordinates]
  simp only [Finset.prod_const, ENNReal.toReal_pow, measureReal_def]

/-- A vector polynomial is zero precisely when all of its coefficients vanish. -/
theorem ofFn_eq_zero_iff_zeroCoordinates (n : ℕ) (a : Fin n → ℂ) :
    Polynomial.ofFn n a = 0 ↔ a ∈ zeroCoordinates Finset.univ := by
  constructor
  · intro h k _
    have hk := congrArg (fun P : ℂ[X] => P.coeff k.val) h
    simpa only [Polynomial.ofFn_coeff_eq_val_of_lt a k.isLt, Polynomial.coeff_zero] using hk
  · intro h
    have ha : a = 0 := funext (fun k => h k (Finset.mem_univ _))
    rw [ha, map_zero]

/-- The zero-polynomial event has exactly the probability of a full zero run. -/
theorem measureReal_ofFn_eq_zero (μ : Measure ℂ) [IsProbabilityMeasure μ] (n : ℕ) :
    (Measure.pi (fun _ : Fin n => μ)).real {a | Polynomial.ofFn n a = 0} = (μ.real {0}) ^ n := by
  have heq : {a | Polynomial.ofFn n a = 0} = zeroCoordinates (Finset.univ : Finset (Fin n)) := by
    ext a
    exact ofFn_eq_zero_iff_zeroCoordinates n a
  rw [heq, measureReal_zeroCoordinates]
  simp

/-- A degree deficit of at least `ℓ` forces the last `ℓ` coefficients to vanish. -/
theorem natDegree_add_le_mem_zeroCoordinates {N ℓ : ℕ} (hℓ : ℓ ≤ N)
    (a : Fin (N + 1) → ℂ) (hdeg : (Polynomial.ofFn (N + 1) a).natDegree + ℓ ≤ N) :
    a ∈ zeroCoordinates (Finset.Ioi (⟨N - ℓ, by omega⟩ : Fin (N + 1))) := by
  intro k hk
  have hk' : (⟨N - ℓ, by omega⟩ : Fin (N + 1)) < k := Finset.mem_Ioi.mp hk
  change N - ℓ < k.val at hk'
  have hc := Polynomial.coeff_eq_zero_of_natDegree_lt (p := Polynomial.ofFn (N + 1) a)
    (by omega : (Polynomial.ofFn (N + 1) a).natDegree < k.val)
  simpa only [Polynomial.ofFn_coeff_eq_val_of_lt a k.isLt] using hc

/-- The actual-degree deficit has the same geometric upper tail as a
trailing zero run. -/
theorem measureReal_natDegree_deficit_le (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (N ℓ : ℕ) (hℓ : ℓ ≤ N) :
    (Measure.pi (fun _ : Fin (N + 1) => μ)).real
      {a | (Polynomial.ofFn (N + 1) a).natDegree + ℓ ≤ N} ≤ (μ.real {0}) ^ ℓ := by
  have hsub : {a : Fin (N + 1) → ℂ | (Polynomial.ofFn (N + 1) a).natDegree + ℓ ≤ N} ⊆
      zeroCoordinates (Finset.Ioi (⟨N - ℓ, by omega⟩ : Fin (N + 1))) :=
    fun a ha => natDegree_add_le_mem_zeroCoordinates hℓ a ha
  have h := measureReal_mono (μ := Measure.pi (fun _ : Fin (N + 1) => μ)) hsub
  rw [measureReal_zeroCoordinates, Fin.card_Ioi] at h
  convert h using 1
  congr 1
  change ℓ = N + 1 - 1 - (N - ℓ)
  omega

/-- A short initial zero run has its exact geometric probability. -/
theorem measureReal_initial_zero_run (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (N ℓ : ℕ) (hℓ : ℓ ≤ N) :
    (Measure.pi (fun _ : Fin (N + 1) => μ)).real
      (zeroCoordinates (Finset.Iio (⟨ℓ, by omega⟩ : Fin (N + 1)))) = (μ.real {0}) ^ ℓ := by
  rw [measureReal_zeroCoordinates, Fin.card_Iio]

/-- Polynomial-prefix degrees are nondecreasing even when coefficients vanish. -/
theorem polynomialPrefix_natDegree_mono (ξ c : ℕ → ℂ) :
    Monotone (fun N => (polynomialPrefix ξ c N).natDegree) := by
  intro N n hNn
  by_cases hzero : polynomialPrefix ξ c N = 0
  · simp [hzero]
  have hk := polynomialPrefix_natDegree_le ξ c N
  apply Polynomial.le_natDegree_of_ne_zero
  rw [polynomialPrefix_coeff, ite_eq_left (hk.trans hNn)]
  have hcoeff : (polynomialPrefix ξ c N).coeff (polynomialPrefix ξ c N).natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hzero
  rw [polynomialPrefix_coeff, ite_eq_left hk] at hcoeff
  exact hcoeff

/-- If a prefix loses at most `L` nominal degrees, its actual degree can
increase across a block by at most the block length plus `L`. -/
theorem polynomialPrefix_degree_increase_le (ξ c : ℕ → ℂ) {N m L : ℕ}
    (hdegree : N ≤ (polynomialPrefix ξ c N).natDegree + L) :
    (polynomialPrefix ξ c (N + m)).natDegree - (polynomialPrefix ξ c N).natDegree ≤ m + L := by
  have hupper := polynomialPrefix_natDegree_le ξ c (N + m)
  omega

/-- A logarithmic run cutoff turns the geometric probability into a fourth
inverse power whenever `D*(-log q)≥4`. -/
theorem geometric_logarithmic_cutoff_le {q D x : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hD : 4 ≤ -D * Real.log q) (hx : 1 ≤ x) :
    q ^ ⌈D * Real.log x⌉₊ ≤ x ^ (-(4 : ℝ)) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlogq : Real.log q ≤ 0 := (Real.log_neg hq hq1).le
  have hceil := mul_le_mul_of_nonpos_left (Nat.le_ceil (D * Real.log x)) hlogq
  have hscale := mul_le_mul_of_nonneg_right hD (Real.log_nonneg hx)
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hq, Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Logarithmic zero-run probabilities are summable over all positive
degrees, hence also along every strictly increasing sparse subsequence. -/
theorem summable_geometric_logarithmic_cutoff {q D : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hD : 4 ≤ -D * Real.log q) :
    Summable (fun n : ℕ => q ^ ⌈D * Real.log (n + 1 : ℕ)⌉₊) := by
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-(4 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hs : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(4 : ℝ))) :=
    (summable_nat_add_iff 1).mpr hp
  apply hs.of_nonneg_of_le (fun _ => pow_nonneg hq.le _)
  intro n
  exact geometric_logarithmic_cutoff_le hq hq1 hD (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

end Erdos522

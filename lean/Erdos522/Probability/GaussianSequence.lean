/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianFourierLogarithmicMoments
import Erdos522.Basic.PolynomialPrefixes
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# A shared infinite Gaussian coefficient sequence

Finite restrictions have the standard Gaussian product law. Summable finite
exceptions pull back to this one sequence, and every coefficient is nonzero
on a single event of probability one.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped ENNReal
namespace Erdos522

/-- The law of one infinite sequence of independent standard real Gaussians. -/
def gaussianSequenceMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance : IsProbabilityMeasure gaussianSequenceMeasure := by
  unfold gaussianSequenceMeasure
  infer_instance

/-- The first `N + 1` entries of a real coefficient sequence. -/
def gaussianPrefix (N : ℕ) (ω : ℕ → ℝ) : Fin (N + 1) → ℝ := fun k => ω k.val

@[fun_prop]
theorem measurable_gaussianPrefix (N : ℕ) : Measurable (gaussianPrefix N) := by
  unfold gaussianPrefix
  fun_prop

theorem map_gaussianPrefix (N : ℕ) :
    gaussianSequenceMeasure.map (gaussianPrefix N) = gaussianCoefficientMeasure (N + 1) := by
  unfold gaussianSequenceMeasure gaussianPrefix gaussianCoefficientMeasure
  rw [Measure.map_infinitePi_infinitePi_of_inj (fun i j h => Fin.ext h),
    Measure.infinitePi_eq_pi]

theorem measurePreserving_gaussianPrefix (N : ℕ) :
    MeasurePreserving (gaussianPrefix N) gaussianSequenceMeasure (gaussianCoefficientMeasure (N + 1)) :=
  ⟨measurable_gaussianPrefix N, map_gaussianPrefix N⟩

/-- Arbitrary finite exceptions pull back with no increase in outer probability. -/
theorem measure_gaussianPrefix_preimage_le (N : ℕ) (E : Set (Fin (N + 1) → ℝ)) :
    gaussianSequenceMeasure ((gaussianPrefix N) ⁻¹' E) ≤ gaussianCoefficientMeasure (N + 1) E := by
  rw [← map_gaussianPrefix N]
  exact Measure.le_map_apply (measurable_gaussianPrefix N).aemeasurable E

theorem measureReal_gaussianPrefix_preimage_le (N : ℕ) (E : Set (Fin (N + 1) → ℝ)) :
    gaussianSequenceMeasure.real ((gaussianPrefix N) ⁻¹' E) ≤
      (gaussianCoefficientMeasure (N + 1)).real E :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_gaussianPrefix_preimage_le N E)

/-- The finite Gaussian polynomial is a prefix of the shared real sequence. -/
theorem gaussianPrefix_polynomial (N : ℕ) (ω : ℕ → ℝ) :
    gaussianPolynomial N (gaussianPrefix N ω) =
      polynomialPrefix (fun k => (ω k : ℂ)) (fun _ => 1) N := by
  simp only [gaussianPolynomial, gaussianPrefix, polynomialPrefix, mul_one,
    C_mul_X_pow_eq_monomial]
  exact Fin.sum_univ_eq_sum_range (fun k => monomial k (ω k : ℂ)) (N + 1)

/-- Borel–Cantelli for arbitrary indexed finite Gaussian exceptions. -/
theorem ae_eventually_indexed_gaussianPrefix_notMem (n : ℕ → ℕ)
    (E : ∀ j, Set (Fin (n j + 1) → ℝ))
    (hs : Summable (fun j => (gaussianCoefficientMeasure (n j + 1)).real (E j))) :
    ∀ᵐ ω ∂gaussianSequenceMeasure, ∀ᶠ j in atTop, gaussianPrefix (n j) ω ∉ E j := by
  have hsum : Summable (fun j =>
      gaussianSequenceMeasure.real ((gaussianPrefix (n j)) ⁻¹' E j)) :=
    Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) (fun j =>
      measureReal_gaussianPrefix_preimage_le (n j) (E j)) hs
  have hfinite : (∑' j, gaussianSequenceMeasure ((gaussianPrefix (n j)) ⁻¹' E j)) ≠ ∞ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      hsum.tsum_ofReal_ne_top
  exact ae_eventually_notMem hfinite

/-- All coordinates are simultaneously nonzero almost surely. -/
theorem ae_gaussianSequence_nonzero :
    ∀ᵐ ω ∂gaussianSequenceMeasure, ∀ k, ω k ≠ 0 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  apply ae_all_iff.mpr
  intro k
  have hm : MeasurePreserving (fun ω : ℕ → ℝ => ω k) gaussianSequenceMeasure
      (gaussianReal 0 1) := measurePreserving_eval_infinitePi _ k
  exact hm.quasiMeasurePreserving.ae ((gaussianReal 0 1).ae_ne 0)

/-- Every finite Gaussian prefix has its nominal degree on one event. -/
theorem ae_gaussianPrefix_natDegree :
    ∀ᵐ ω ∂gaussianSequenceMeasure, ∀ N,
      (gaussianPolynomial N (gaussianPrefix N ω)).natDegree = N := by
  filter_upwards [ae_gaussianSequence_nonzero] with ω hω
  intro N
  rw [gaussianPrefix_polynomial]
  apply polynomialPrefix_natDegree
  simpa using hω N

/-- The constant coefficient is nonzero for every prefix on one event. -/
theorem ae_gaussianPrefix_constant_nonzero :
    ∀ᵐ ω ∂gaussianSequenceMeasure, ∀ N,
      (gaussianPolynomial N (gaussianPrefix N ω)).coeff 0 ≠ 0 := by
  filter_upwards [ae_gaussianSequence_nonzero] with ω hω
  intro N
  rw [gaussianPrefix_polynomial, polynomialPrefix_coeff]
  simpa using hω 0

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.PairBessel
import Erdos522.Probability.LogMoments.RestrictedPairMatrix

/-!
# Centered Bessel bounds for restricted Fourier energy

Subtracting the event probability from its indicator preserves every off-diagonal
Fourier coefficient and reduces the squared norm to its Bernoulli variance.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Erdos522.LogMoments

lemma integral_pairMode_eq_zero {N : ℕ} (i j : Fin (N + 1)) (hij : i ≠ j) :
    (∫ q, pairMode i j q ∂fourierMeasure N) = 0 := by
  have heq (q : SignVector N × AddCircle (1 : ℝ)) : pairMode i j q =
      Complex.ofReal (realSign (q.1 i) * realSign (q.1 j)) *
        fourier ((i : ℤ) - (j : ℤ)) q.2 := by
    simp only [pairMode, Complex.ofReal_mul, ofReal_realSign]
  simp_rw [heq]
  rw [fourierMeasure]
  calc
    _ = (∫ ω : SignVector N, Complex.ofReal (realSign (ω i) * realSign (ω j))
        ∂signMeasure N) * (∫ θ : AddCircle (1 : ℝ),
          fourier ((i : ℤ) - (j : ℤ)) θ ∂AddCircle.haarAddCircle) :=
      integral_prod_mul _ _
    _ = 0 := by rw [integral_complex_ofReal, integral_mul_realSign_coordinates]; simp [hij]

/-- The centered complex indicator of an event. -/
def centeredEventIndicator {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ)))
    (q : SignVector N × AddCircle (1 : ℝ)) : ℂ :=
  E.indicator (fun _ => (1 : ℂ)) q - ((fourierMeasure N).real E : ℂ)

lemma memLp_centeredEventIndicator {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E) :
    MemLp (centeredEventIndicator E) 2 (fourierMeasure N) :=
  ((memLp_const (1 : ℂ)).indicator hE).sub (memLp_const _)

/-- The centered event indicator as a vector in `L²`. -/
def centeredEventLp {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E) :
    Lp ℂ 2 (fourierMeasure N) :=
  (memLp_centeredEventIndicator E hE).toLp (centeredEventIndicator E)

lemma centeredEventLp_ae_eq {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E) :
    centeredEventLp E hE =ᵐ[fourierMeasure N] centeredEventIndicator E :=
  (memLp_centeredEventIndicator E hE).coeFn_toLp

lemma norm_sq_centeredEventIndicator {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ)))
    (q : SignVector N × AddCircle (1 : ℝ)) :
    ‖centeredEventIndicator E q‖ ^ 2 =
      E.indicator (fun _ => 1 - 2 * (fourierMeasure N).real E) q +
        (fourierMeasure N).real E ^ 2 := by
  by_cases hq : q ∈ E
  · simp only [centeredEventIndicator, Set.indicator_of_mem hq]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    ring
  · simp [centeredEventIndicator, hq, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Centered event indicators have squared `L²` norm `δ(1-δ)`. -/
theorem norm_centeredEventLp_sq {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E) :
    ‖centeredEventLp E hE‖ ^ 2 =
      (fourierMeasure N).real E * (1 - (fourierMeasure N).real E) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have heq : (fun q => inner ℝ (centeredEventLp E hE q) (centeredEventLp E hE q))
      =ᵐ[fourierMeasure N] (fun q => ‖centeredEventIndicator E q‖ ^ 2) := by
    filter_upwards [centeredEventLp_ae_eq E hE] with q hq
    rw [hq, real_inner_self_eq_norm_sq]
  rw [integral_congr_ae heq]
  simp_rw [norm_sq_centeredEventIndicator]
  rw [integral_add ((integrable_const _).indicator hE) (integrable_const _),
    integral_indicator hE, setIntegral_const, integral_const]
  simp only [smul_eq_mul, probReal_univ, one_mul]
  ring

/-- Centering does not change coefficients of off-diagonal modes. -/
theorem inner_pairModeLp_centeredEvent {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (p : OffDiagonalPair N) :
    inner ℂ (pairModeLp p) (centeredEventLp E hE) =
      conj (restrictedPairCoefficient E p) := by
  rw [L2.inner_def]
  have heq : (fun q => inner ℂ (pairModeLp p q) (centeredEventLp E hE q))
      =ᵐ[fourierMeasure N] (fun q =>
        E.indicator (fun q => conj (pairMode p.1.1 p.1.2 q)) q -
        ((fourierMeasure N).real E : ℂ) * conj (pairMode p.1.1 p.1.2 q)) := by
    filter_upwards [pairModeLp_ae_eq p, centeredEventLp_ae_eq E hE] with q hp hq
    rw [hp, hq]
    by_cases hqE : q ∈ E <;> simp [centeredEventIndicator, hqE, RCLike.inner_apply, sub_mul]
  rw [integral_congr_ae heq]
  have hint : Integrable (fun q => conj (pairMode p.1.1 p.1.2 q)) (fourierMeasure N) := by
    simpa only [conjugate_pairMode] using integrable_pairMode p.1.2 p.1.1
  rw [integral_sub (hint.indicator hE) (hint.const_mul _), integral_indicator hE,
    integral_const_mul, integral_conj, integral_conj, integral_pairMode_eq_zero _ _ p.2]
  simp only [map_zero, mul_zero, sub_zero]
  rfl

/-- The centered Bessel estimate is independent of the number of coefficients. -/
theorem sum_sq_restrictedPairCoefficient_le_variance {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E) :
    ∑ p : OffDiagonalPair N, ‖restrictedPairCoefficient E p‖ ^ 2 ≤
      (fourierMeasure N).real E * (1 - (fourierMeasure N).real E) := by
  have h := (orthonormal_pairModeLp N).sum_inner_products_le
    (s := Finset.univ) (centeredEventLp E hE)
  simpa only [inner_pairModeLp_centeredEvent, Complex.norm_conj, norm_centeredEventLp_sq] using h

lemma sum_sq_restrictedPairMatrix_eq_coefficients {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) :
    (∑ i, ∑ j, ‖restrictedPairMatrix E i j‖ ^ 2) =
      ∑ p : OffDiagonalPair N, ‖restrictedPairCoefficient E p‖ ^ 2 := by
  let f : Fin (N + 1) × Fin (N + 1) → ℝ :=
    fun p => ‖∫ q in E, pairMode p.1 p.2 q ∂fourierMeasure N‖ ^ 2
  have hsub := Finset.sum_subtype (p := fun p : Fin (N + 1) × Fin (N + 1) => p.1 ≠ p.2) (F := inferInstance)
    (Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) => p.1 ≠ p.2))
    (by intro p; simp) f
  change _ = ∑ p : OffDiagonalPair N, f p.1
  rw [← hsub, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j; simp
  · simp [restrictedPairMatrix, hij, Ne.symm hij, f]

/-- The restricted off-diagonal matrix has squared Hilbert--Schmidt norm at most
`δ(1-δ)`, where `δ` is the event probability. -/
theorem restrictedPairMatrix_hilbertSchmidt_sq_le_variance {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E) :
    (∑ i, ∑ j, ‖restrictedPairMatrix E i j‖ ^ 2) ≤
      (fourierMeasure N).real E * (1 - (fourierMeasure N).real E) := by
  rw [sum_sq_restrictedPairMatrix_eq_coefficients]
  exact sum_sq_restrictedPairCoefficient_le_variance E hE

end Erdos522.LogMoments

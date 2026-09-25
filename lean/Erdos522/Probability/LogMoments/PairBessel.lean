/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.PairOrthogonality

/-!
# Bessel's inequality for ordered Fourier pairs

Restricted Fourier coefficients of an event inherit the Hilbert-space energy bound
from the orthonormal family of ordered off-diagonal modes.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Erdos522.LogMoments

/-- Ordered pairs of distinct coefficient indices. -/
abbrev OffDiagonalPair (N : ℕ) :=
  {p : Fin (N + 1) × Fin (N + 1) // p.1 ≠ p.2}

lemma memLp_pairMode {N : ℕ} (i j : Fin (N + 1)) :
    MemLp (pairMode i j) 2 (fourierMeasure N) :=
  MemLp.of_bound (measurable_pairMode i j).aestronglyMeasurable 1
    (ae_of_all _ (fun q => by simp))

/-- The off-diagonal mode as a vector in the native joint-law `L²` space. -/
def pairModeLp {N : ℕ} (p : OffDiagonalPair N) :
    Lp ℂ 2 (fourierMeasure N) :=
  (memLp_pairMode p.1.1 p.1.2).toLp (pairMode p.1.1 p.1.2)

lemma pairModeLp_ae_eq {N : ℕ} (p : OffDiagonalPair N) :
    pairModeLp p =ᵐ[fourierMeasure N] pairMode p.1.1 p.1.2 :=
  (memLp_pairMode p.1.1 p.1.2).coeFn_toLp

/-- The ordered-pair modes form an orthonormal family in `L²`. -/
theorem orthonormal_pairModeLp (N : ℕ) :
    Orthonormal ℂ (pairModeLp (N := N)) := by
  rw [orthonormal_iff_ite]
  intro p q
  rw [L2.inner_def]
  have heq : (fun z => inner ℂ (pairModeLp p z) (pairModeLp q z)) =ᵐ[fourierMeasure N]
      fun z => inner ℂ (pairMode p.1.1 p.1.2 z) (pairMode q.1.1 q.1.2 z) := by
    filter_upwards [pairModeLp_ae_eq p, pairModeLp_ae_eq q] with z hp hq
    rw [hp, hq]
  rw [integral_congr_ae heq, integral_inner_pairMode _ _ _ _ p.2 q.2]
  congr 1
  exact propext (by simp only [Subtype.ext_iff, Prod.ext_iff])

/-- The coefficient of an event against an ordered Fourier pair. -/
def restrictedPairCoefficient {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (p : OffDiagonalPair N) : ℂ :=
  ∫ q in E, pairMode p.1.1 p.1.2 q ∂fourierMeasure N

private def eventIndicatorLp {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E) :
    Lp ℂ 2 (fourierMeasure N) :=
  ((memLp_const (1 : ℂ)).indicator hE).toLp (E.indicator (fun _ => (1 : ℂ)))

private lemma eventIndicatorLp_ae_eq {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E) :
    eventIndicatorLp E hE =ᵐ[fourierMeasure N] E.indicator (fun _ => (1 : ℂ)) :=
  ((memLp_const (1 : ℂ)).indicator hE).coeFn_toLp

private lemma inner_pairModeLp_eventIndicator {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (p : OffDiagonalPair N) :
    inner ℂ (pairModeLp p) (eventIndicatorLp E hE) = conj (restrictedPairCoefficient E p) := by
  rw [L2.inner_def]
  have heq : (fun q => inner ℂ (pairModeLp p q) (eventIndicatorLp E hE q))
      =ᵐ[fourierMeasure N] E.indicator (fun q => conj (pairMode p.1.1 p.1.2 q)) := by
    filter_upwards [pairModeLp_ae_eq p, eventIndicatorLp_ae_eq E hE] with q hp hq
    rw [hp, hq]
    by_cases hqE : q ∈ E <;> simp [hqE, RCLike.inner_apply]
  rw [integral_congr_ae heq, integral_indicator hE, integral_conj]
  rfl

private lemma norm_eventIndicatorLp_sq {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E) :
    ‖eventIndicatorLp E hE‖ ^ 2 = (fourierMeasure N).real E := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ, L2.inner_def]
  have heq : (fun q => inner ℂ (eventIndicatorLp E hE q) (eventIndicatorLp E hE q))
      =ᵐ[fourierMeasure N] E.indicator (fun _ => (1 : ℂ)) := by
    filter_upwards [eventIndicatorLp_ae_eq E hE] with q hq
    rw [hq]
    by_cases hqE : q ∈ E <;> simp [hqE]
  rw [integral_congr_ae heq, integral_indicator hE, setIntegral_const]
  simp

/-- Bessel's inequality bounds the total squared restricted coefficient mass
by the probability of the restricting event. -/
theorem sum_sq_restrictedPairCoefficient_le {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E) :
    ∑ p : OffDiagonalPair N, ‖restrictedPairCoefficient E p‖ ^ 2 ≤
      (fourierMeasure N).real E := by
  have h := (orthonormal_pairModeLp N).sum_inner_products_le
    (s := Finset.univ) (eventIndicatorLp E hE)
  simpa only [inner_pairModeLp_eventIndicator, Complex.norm_conj, norm_eventIndicatorLp_sq] using h

end Erdos522.LogMoments

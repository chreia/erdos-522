/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianCoefficients
import Erdos522.Probability.GaussianCoefficients

/-!
# Real-coordinate representation of circular Gaussian coefficients

A circular coefficient is the sum of two independent real standard Gaussians,
with the imaginary coordinate multiplied by `I` and both scaled by `1 / √2`.
The representation is a measurable equivalence, so it also transports outer
probabilities of events without a measurability assumption on those events.
-/

noncomputable section
open MeasureTheory ProbabilityTheory WithLp
open scoped RealInnerProductSpace NNReal
namespace Erdos522

/-- The normalized real and imaginary coordinates of a complex coefficient. -/
def circularGaussianCoordinateEquiv : (ℝ × ℝ) ≃ᵐ ℂ where
  toFun p := ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ)
  invFun z := (Real.sqrt 2 * z.re, Real.sqrt 2 * z.im)
  left_inv p := by
    have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    ext <;> simp only [Complex.div_ofReal_re, Complex.div_ofReal_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> field_simp <;> ring
  right_inv z := by
    have hs : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (by norm_num)).ne'
    apply (div_eq_iff hs).mpr
    apply Complex.ext <;> simp <;> ring
  measurable_toFun := by
    change Measurable (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ℂ => (Real.sqrt 2 * z.re, Real.sqrt 2 * z.im))
    fun_prop

@[simp]
theorem circularGaussianCoordinateEquiv_apply (p : ℝ × ℝ) :
    circularGaussianCoordinateEquiv p =
      ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ) := rfl

/-- The real projections of normalized Gaussian coordinates have variance `‖z‖² / 2`. -/
theorem circularGaussian_projection_variance (z : ℂ) :
    (∑ k : Fin 2, (![z.re / Real.sqrt 2, z.im / Real.sqrt 2] k) ^ 2) = ‖z‖ ^ 2 / 2 := by
  rw [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, div_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- A pair of independent real Gaussians gives the circular complex law. -/
theorem map_circularGaussianCoordinates :
    (gaussianCoefficientMeasure 2).map
      (fun g => circularGaussianCoordinateEquiv (g 0, g 1)) = circularComplexGaussian := by
  apply Measure.ext_of_charFun
  ext z
  rw [charFun_map_eq_charFun_map_inner_one (by fun_prop)]
  have he : (fun g : Fin 2 → ℝ => inner ℝ (circularGaussianCoordinateEquiv (g 0, g 1)) z) =
      realGaussianSum ![z.re / Real.sqrt 2, z.im / Real.sqrt 2] := by
    funext g
    simp [circularGaussianCoordinateEquiv, realGaussianSum, Fin.sum_univ_two,
      Complex.div_ofReal_re, Complex.div_ofReal_im]
    ring
  rw [he, map_realGaussianSum, circularGaussian_projection_variance, charFun_gaussianReal,
    charFun_circularComplexGaussian]
  rw [Real.coe_toNNReal _ (by positivity)]
  congr 1
  push_cast
  ring

/-- Normalized real-coordinate assembly preserves the Gaussian probability law. -/
theorem measurePreserving_circularGaussianCoordinateEquiv :
    MeasurePreserving circularGaussianCoordinateEquiv
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) circularComplexGaussian := by
  refine ⟨circularGaussianCoordinateEquiv.measurable, ?_⟩
  have h := measurePreserving_finTwoArrow (gaussianReal 0 1)
  rw [← h.map_eq, Measure.map_map circularGaussianCoordinateEquiv.measurable h.measurable]
  exact map_circularGaussianCoordinates

/-- The circular law as a normalized complex linear combination of two real Gaussians. -/
theorem map_complexGaussianSum_circular :
    (gaussianCoefficientMeasure 2).map
      (complexGaussianSum ![(1 : ℂ) / (Real.sqrt 2 : ℂ),
        Complex.I / (Real.sqrt 2 : ℂ)]) = circularComplexGaussian := by
  convert map_circularGaussianCoordinates using 1
  congr 1
  funext g
  simp only [complexGaussianSum, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, circularGaussianCoordinateEquiv_apply]
  ring

/-- Coefficientwise assembly of independent Gaussian coordinate pairs. -/
def circularGaussianCoefficientPairEquiv (n : ℕ) : (Fin n → ℝ × ℝ) ≃ᵐ (Fin n → ℂ) :=
  MeasurableEquiv.piCongrRight (fun _ => circularGaussianCoordinateEquiv)

theorem measurePreserving_circularGaussianCoefficientPairs (n : ℕ) :
    MeasurePreserving (circularGaussianCoefficientPairEquiv n)
      (Measure.pi (fun _ : Fin n => (gaussianReal 0 1).prod (gaussianReal 0 1)))
      (Measure.pi (fun _ : Fin n => circularComplexGaussian)) :=
  measurePreserving_pi _ _ (fun _ => measurePreserving_circularGaussianCoordinateEquiv)

/-- Splitting a real Gaussian vector into its real and imaginary coefficient arrays. -/
def circularGaussianCoefficientVectorEquiv (n : ℕ) :
    ((Fin n → ℝ) × (Fin n → ℝ)) ≃ᵐ (Fin n → ℂ) :=
  (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm.trans
    (circularGaussianCoefficientPairEquiv n)

@[simp]
theorem circularGaussianCoefficientVectorEquiv_apply (n : ℕ)
    (g : (Fin n → ℝ) × (Fin n → ℝ)) (k : Fin n) :
    circularGaussianCoefficientVectorEquiv n g k =
      ((g.1 k : ℂ) + (g.2 k : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ) := rfl

theorem measurePreserving_circularGaussianCoefficientVectors (n : ℕ) :
    MeasurePreserving (circularGaussianCoefficientVectorEquiv n)
      ((gaussianCoefficientMeasure n).prod (gaussianCoefficientMeasure n))
      (Measure.pi (fun _ : Fin n => circularComplexGaussian)) := by
  have h := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)
  exact (measurePreserving_circularGaussianCoefficientPairs n).comp h.symm

/-- Any complex coefficient event contained in two real-coordinate exceptions
has outer probability bounded by the sum of their probabilities. -/
theorem circularGaussian_coefficient_event_le (n : ℕ) (E : Set (Fin n → ℂ))
    (A B : Set (Fin n → ℝ))
    (hE : ∀ g, circularGaussianCoefficientVectorEquiv n g ∈ E → g.1 ∈ A ∨ g.2 ∈ B) :
    (Measure.pi (fun _ : Fin n => circularComplexGaussian)).real E ≤
      (gaussianCoefficientMeasure n).real A + (gaussianCoefficientMeasure n).real B := by
  have hm := measurePreserving_circularGaussianCoefficientVectors n
  rw [← hm.map_eq, measureReal_def, (circularGaussianCoefficientVectorEquiv n).map_apply]
  have hs : circularGaussianCoefficientVectorEquiv n ⁻¹' E ⊆
      (A ×ˢ Set.univ) ∪ (Set.univ ×ˢ B) := by
    intro g hg
    rcases hE g hg with hA | hB
    · exact Or.inl ⟨hA, Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _, hB⟩
  have h := measure_union_le (μ := (gaussianCoefficientMeasure n).prod
    (gaussianCoefficientMeasure n)) (A ×ˢ Set.univ) (Set.univ ×ˢ B)
  have hb := (measure_mono hs).trans h
  rw [Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one, one_mul] at hb
  exact (ENNReal.toReal_mono (by finiteness) hb).trans_eq
    (ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _))

end Erdos522

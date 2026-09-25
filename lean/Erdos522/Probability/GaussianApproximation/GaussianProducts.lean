/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.JetSmallBall
import Erdos522.Probability.GaussianApproximation.CovarianceComparison

/-!
# Products of Gaussian vectors

Independent Gaussian vectors correspond to a block diagonal covariance after
concatenating their Euclidean coordinates.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal NNReal MatrixOrder RealInnerProductSpace

namespace Erdos522

/-- The covariance matrix of two independent vectors in consecutive coordinate blocks. -/
def gaussianBlockCovariance {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) ℝ) (T : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
  (Matrix.fromBlocks S 0 0 T).reindex finSumFinEquiv finSumFinEquiv

/-- The quadratic form of a block covariance is the sum of the marginal forms. -/
theorem quadratic_gaussianBlockCovariance {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) ℝ) (T : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin (m + n))) :
    x.ofLp ⬝ᵥ gaussianBlockCovariance S T *ᵥ x.ofLp =
      (EuclideanSpace.finAddEquivProd x).1.ofLp ⬝ᵥ S *ᵥ (EuclideanSpace.finAddEquivProd x).1.ofLp +
      (EuclideanSpace.finAddEquivProd x).2.ofLp ⬝ᵥ T *ᵥ (EuclideanSpace.finAddEquivProd x).2.ofLp := by
  change x.ofLp ⬝ᵥ (Matrix.fromBlocks S 0 0 T).submatrix finSumFinEquiv.symm finSumFinEquiv.symm *ᵥ x.ofLp = _
  rw [Matrix.submatrix_mulVec_equiv, dotProduct_comp_equiv_symm]
  simp only [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
  simp [dotProduct, Fintype.sum_sum_type, Function.comp_def, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd]

/-- Splitting consecutive Euclidean coordinates splits the squared norm additively. -/
theorem norm_sq_finAddEquivProd {m n : ℕ} (x : EuclideanSpace ℝ (Fin (m + n))) :
    ‖x‖ ^ 2 = ‖(EuclideanSpace.finAddEquivProd x).1‖ ^ 2 +
      ‖(EuclideanSpace.finAddEquivProd x).2‖ ^ 2 := by
  simpa [EuclideanSpace.norm_sq_eq, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd] using
    (Fin.sum_univ_add (fun i : Fin (m + n) => (x i) ^ 2))

/-- A positive lower bound for each marginal covariance is inherited by their block sum. -/
theorem gaussianBlockCovariance_lower {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) ℝ) (T : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hS : ∀ x : EuclideanSpace ℝ (Fin m), c * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S *ᵥ x.ofLp)
    (hT : ∀ y : EuclideanSpace ℝ (Fin n), c * ‖y‖ ^ 2 ≤ y.ofLp ⬝ᵥ T *ᵥ y.ofLp)
    (x : EuclideanSpace ℝ (Fin (m + n))) :
    c * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ gaussianBlockCovariance S T *ᵥ x.ofLp := by
  rw [quadratic_gaussianBlockCovariance, norm_sq_finAddEquivProd, mul_add]
  exact add_le_add (hS _) (hT _)

/-- The block covariance is positive semidefinite when both marginals are. -/
theorem gaussianBlockCovariance_posSemidef {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) ℝ) (T : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosSemidef) (hT : T.PosSemidef) :
    (gaussianBlockCovariance S T).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (Matrix.IsHermitian.fromBlocks hS.isHermitian (by simp) hT.isHermitian).submatrix _
  intro x
  have h := quadratic_gaussianBlockCovariance S T (toLp 2 x)
  simp only [star_trivial]
  rw [h]
  exact add_nonneg (hS.dotProduct_mulVec_nonneg _) (hT.dotProduct_mulVec_nonneg _)

/-- Concatenating coordinates splits the Euclidean inner product. -/
theorem inner_finAddEquivProd_symm {m n : ℕ}
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin (m + n))) :
    ⟪EuclideanSpace.finAddEquivProd.symm p, x⟫ =
      ⟪p.1, (EuclideanSpace.finAddEquivProd x).1⟫ +
      ⟪p.2, (EuclideanSpace.finAddEquivProd x).2⟫ := by
  simp [PiLp.inner_apply, Fin.sum_univ_add, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd]

/-- Independent Gaussian vectors concatenate to the Gaussian with block covariance. -/
theorem map_prod_multivariateGaussian {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) ℝ) (T : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosSemidef) (hT : T.PosSemidef) :
    ((multivariateGaussian 0 S).prod (multivariateGaussian 0 T)).map
      EuclideanSpace.finAddEquivProd.symm = multivariateGaussian 0 (gaussianBlockCovariance S T) := by
  apply Measure.ext_of_charFun (E := EuclideanSpace ℝ (Fin (m + n)))
  ext x
  have hi : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin (m + n)) =>
      Complex.exp ((⟪y, x⟫ : ℝ) * Complex.I))
      (((multivariateGaussian 0 S).prod (multivariateGaussian 0 T)).map
        EuclideanSpace.finAddEquivProd.symm) := by fun_prop
  rw [charFun, integral_map (by fun_prop) hi]
  simp_rw [inner_finAddEquivProd_symm, Complex.ofReal_add, add_mul, Complex.exp_add]
  rw [integral_prod_mul
    (fun y : EuclideanSpace ℝ (Fin m) =>
      Complex.exp ((⟪y, (EuclideanSpace.finAddEquivProd x).1⟫ : ℝ) * Complex.I))
    (fun y : EuclideanSpace ℝ (Fin n) =>
      Complex.exp ((⟪y, (EuclideanSpace.finAddEquivProd x).2⟫ : ℝ) * Complex.I))]
  change charFun (multivariateGaussian 0 S) _ * charFun (multivariateGaussian 0 T) _ = _
  rw [charFun_multivariateGaussian hS, charFun_multivariateGaussian hT,
    charFun_multivariateGaussian (gaussianBlockCovariance_posSemidef S T hS hT)]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, ← Complex.exp_add]
  congr 1
  rw [quadratic_gaussianBlockCovariance]
  push_cast
  ring

/-- Strict marginal quadratic lower bounds make the block covariance positive definite. -/
theorem gaussianBlockCovariance_posDef_of_lower {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) ℝ) (T : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosSemidef) (hT : T.PosSemidef) (c : ℝ) (hc : 0 < c)
    (hlS : ∀ x : EuclideanSpace ℝ (Fin m), c * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S *ᵥ x.ofLp)
    (hlT : ∀ y : EuclideanSpace ℝ (Fin n), c * ‖y‖ ^ 2 ≤ y.ofLp ⬝ᵥ T *ᵥ y.ofLp) :
    (gaussianBlockCovariance S T).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (gaussianBlockCovariance_posSemidef S T hS hT).isHermitian
  intro x hx
  have hx' : (toLp 2 x : EuclideanSpace ℝ (Fin (m + n))) ≠ 0 := by
    simpa only [ne_eq, WithLp.toLp_eq_zero] using hx
  have h := gaussianBlockCovariance_lower S T c hlS hlT (toLp 2 x)
  simp only [star_trivial]
  exact lt_of_lt_of_le (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hx'))) h

/-- Rectangular events factor exactly for the block Gaussian. -/
theorem gaussianBlockCovariance_measureReal_prod {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) ℝ) (T : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosSemidef) (hT : T.PosSemidef)
    (A : Set (EuclideanSpace ℝ (Fin m))) (B : Set (EuclideanSpace ℝ (Fin n)))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (multivariateGaussian 0 (gaussianBlockCovariance S T)).real
      (EuclideanSpace.finAddEquivProd ⁻¹' (A ×ˢ B)) =
      (multivariateGaussian 0 S).real A * (multivariateGaussian 0 T).real B := by
  rw [← map_prod_multivariateGaussian S T hS hT, measureReal_def,
    Measure.map_apply (by fun_prop) ((hA.prod hB).preimage (by fun_prop))]
  have he : EuclideanSpace.finAddEquivProd.symm ⁻¹'
      (EuclideanSpace.finAddEquivProd ⁻¹' (A ×ˢ B)) = A ×ˢ B := by
    ext p
    simp
  rw [he, Measure.prod_prod, ENNReal.toReal_mul]
  rfl

end Erdos522

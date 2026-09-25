/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.RadialProjection
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Radial projection of polynomial roots

Projecting every root onto the unit circle gives a monic polynomial of the
same degree. A value of modulus at least one on the unit circle controls the
projected polynomial by the original polynomial, including all multiplicities.
-/

noncomputable section
open Polynomial
open scoped BigOperators
namespace Erdos522

/-- Radial projection onto the unit circle, with the origin assigned to one. -/
def unitCircleProjection (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

@[simp] theorem norm_unitCircleProjection (z : ℂ) : ‖unitCircleProjection z‖ = 1 := by
  by_cases hz : z = 0
  · simp [unitCircleProjection, hz]
  · simp [unitCircleProjection, hz, norm_ne_zero_iff.mpr hz]

/-- The norm and projected direction recover the original complex number. -/
theorem norm_mul_unitCircleProjection (z : ℂ) :
    (‖z‖ : ℂ) * unitCircleProjection z = z := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    simp only [unitCircleProjection, ite_eq_right_iff.mpr (fun h => (hz h).elim)]
    field_simp [hn]

/-- The monic polynomial obtained by radially projecting the root multiset. -/
def projectedRootPolynomial (P : Polynomial ℂ) : Polynomial ℂ :=
  (P.roots.map (fun z => X - C (unitCircleProjection z))).prod

theorem projectedRootPolynomial_monic (P : Polynomial ℂ) :
    (projectedRootPolynomial P).Monic := by
  apply monic_multiset_prod_of_monic
  intro Q hQ
  exact monic_X_sub_C _

theorem projectedRootPolynomial_natDegree (P : Polynomial ℂ) :
    (projectedRootPolynomial P).natDegree = P.natDegree := by
  have heq : projectedRootPolynomial P =
      ((P.roots.map unitCircleProjection).map (fun z => X - C z)).prod := by
    simp only [projectedRootPolynomial, Multiset.map_map, Function.comp_def]
  rw [heq]
  rw [natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]
  exact (IsAlgClosed.splits P).natDegree_eq_card_roots.symm

/-- On the unit circle, projecting all roots costs at most `2^degree`. -/
theorem norm_projectedRootPolynomial_le (P : Polynomial ℂ) {z₀ z : ℂ}
    (hz₀ : ‖z₀‖ = 1) (hz : ‖z‖ = 1) (hlarge : 1 ≤ ‖P.eval z₀‖) :
    ‖(projectedRootPolynomial P).eval z‖ ≤
      (2 : ℝ) ^ P.natDegree * ‖P.eval z‖ := by
  let l := P.roots.toList
  have hprod (F : ℂ → ℂ) : (∏ i : Fin l.length, F l[i.val]) = (P.roots.map F).prod := by
    rw [Fin.prod_univ_fun_getElem]
    change ((l.map F : List ℂ) : Multiset ℂ).prod = _
    simp [l]
  have heval (w : ℂ) : P.leadingCoeff *
      (∏ i : Fin l.length, (w - (‖l[i.val]‖ : ℂ) * unitCircleProjection l[i.val])) = P.eval w := by
    simp only [norm_mul_unitCircleProjection]
    rw [hprod]
    exact (IsAlgClosed.splits P).eval_eq_prod_roots w |>.symm
  have h := norm_projected_product_le P.leadingCoeff
    (fun i : Fin l.length => unitCircleProjection l[i.val])
    (fun i : Fin l.length => ‖l[i.val]‖)
    (fun _ => norm_unitCircleProjection _) (fun _ => norm_nonneg _) hz₀ hz (by simpa only [heval] using hlarge)
  rw [heval, hprod (fun w => z - unitCircleProjection w)] at h
  have hlength : l.length = P.natDegree := by
    simp only [l, Multiset.length_toList]
    exact (IsAlgClosed.splits P).natDegree_eq_card_roots.symm
  simpa only [projectedRootPolynomial, eval_multiset_prod, Multiset.map_map,
    Function.comp_def, eval_sub, eval_X, eval_C, Fintype.card_fin, hlength] using h

end Erdos522

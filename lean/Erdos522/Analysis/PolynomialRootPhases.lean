/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.PolynomialProjection
import Erdos522.Analysis.ProgressionSeparation

/-!
# Polynomial root phases and clipped frequency distances

Representatives of the projected root phases turn polynomial values into
products of angular factors. Separating the nonzero period translates gives
a quantitative lower bound in terms of clipped distances to these representatives.
-/

noncomputable section
open Polynomial
open scoped BigOperators
namespace Erdos522

/-- Radial projection is the exponential of the argument, including the origin. -/
theorem unitCircleProjection_eq_exp_arg (z : ℂ) :
    unitCircleProjection z = Complex.exp (Complex.I * z.arg) := by
  by_cases hz : z = 0
  · simp [hz, unitCircleProjection]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    apply mul_left_cancel₀ hn
    rw [norm_mul_unitCircleProjection, mul_comm Complex.I]
    exact (Complex.norm_mul_exp_arg_mul_I z).symm

/-- The canonical normalized argument represents every projected root phase. -/
theorem unitCircleProjection_eq_angularCharacter (z : ℂ) :
    unitCircleProjection z = angularCharacter (z.arg / (2 * Real.pi)) := by
  rw [unitCircleProjection_eq_exp_arg, angularCharacter_eq, unitCirclePoint]
  congr 1
  push_cast
  field_simp

/-- Any representatives of the root phases give the same product of angular distances. -/
theorem norm_projectedRootPolynomial_eq_phase_product (P : Polynomial ℂ)
    (ξ : ℂ → ℝ) (t x : ℝ)
    (hphase : ∀ z ∈ P.roots, unitCircleProjection z = angularCharacter (t * ξ z)) :
    ‖(projectedRootPolynomial P).eval (angularCharacter (t * x))‖ =
      (P.roots.map fun z => ‖angularCharacter (t * (x - ξ z)) - 1‖).prod := by
  simp only [projectedRootPolynomial, eval_multiset_prod, Multiset.map_map,
    Function.comp_def, eval_sub, eval_X, eval_C]
  change (normHom : ℂ →*₀ ℝ) _ = _
  rw [map_multiset_prod (normHom : ℂ →*₀ ℝ)]
  simp only [Multiset.map_map, Function.comp_def, normHom_apply]
  congr 1
  apply Multiset.map_congr rfl
  intro z hz
  rw [hphase z hz, norm_angularCharacter_sub, ← mul_sub]

/-- Isolating the nonzero period translates of every root bounds the product of
clipped distances by the original polynomial value. Root multiplicities remain in the product. -/
theorem polynomial_weighted_distance_lower_bound (P : Polynomial ℂ)
    (ξ : ℂ → ℝ) {τ t δ x : ℝ} (hτ : 0 < τ) (ht : τ / 2 ≤ t)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hphase : ∀ z ∈ P.roots, unitCircleProjection z = angularCharacter (t * ξ z))
    (hsep : ∀ z ∈ P.roots, ∀ k : ℤ, k ≠ 0 → δ / τ ≤ |x - (ξ z + k / t)|)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) (hlarge : 1 ≤ ‖P.eval z₀‖) :
    δ ^ P.natDegree * (P.roots.map fun z => min 1 (τ * |x - ξ z|)).prod ≤
      ‖P.eval (angularCharacter (t * x))‖ := by
  have hproduct := Multiset.prod_map_le_prod_map₀
    (s := P.roots) (fun z => 2 * δ * min 1 (τ * |x - ξ z|))
    (fun z => ‖angularCharacter (t * (x - ξ z)) - 1‖)
    (fun _ _ => mul_nonneg (by positivity) (le_min (by norm_num) (by positivity)))
    (fun z hz => chord_lower_bound_of_progression_separation hτ ht hδ hδ1 (hsep z hz))
  rw [← norm_projectedRootPolynomial_eq_phase_product P ξ t x hphase] at hproduct
  have hprojection := norm_projectedRootPolynomial_le P (z := angularCharacter (t * x)) hz₀
    (by simp only [angularCharacter, fourier_apply, Circle.norm_coe]) hlarge
  have hcard := (IsAlgClosed.splits P).natDegree_eq_card_roots.symm
  have hbound := hproduct.trans hprojection
  rw [Multiset.prod_map_mul] at hbound
  have hconst : (P.roots.map fun _ => (2 * δ)).prod = (2 * δ) ^ P.natDegree := by
    simp only [Multiset.map_const', Multiset.prod_replicate, hcard]
  rw [hconst, mul_pow] at hbound
  have htwo : (0 : ℝ) < 2 ^ P.natDegree := by positivity
  nlinarith

end Erdos522

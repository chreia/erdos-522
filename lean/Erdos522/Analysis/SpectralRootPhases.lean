/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.PhaseRepresentatives
import Erdos522.Analysis.PolynomialRootPhases

/-!
# Root phases on separated spectral intervals

Selecting representatives of the root phases near a separated interval union
turns polynomial values into a lower bound for clipped frequency distances.
The root multiset retains every multiplicity.
-/

noncomputable section
open Polynomial
open scoped BigOperators
namespace Erdos522

/-- A separated interval union admits root-phase representatives with a uniform
weighted lower bound throughout the union. -/
theorem exists_root_phases_on_intervals (P : Polynomial ℂ) (T : Finset ℝ)
    {τ t δ : ℝ} (hτ : 0 < τ) (ht : τ / 2 ≤ t)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ u ∈ finiteIntervalUnion T (2 * (δ / τ)),
      ∀ v ∈ finiteIntervalUnion T (2 * (δ / τ)),
        ∀ k : ℤ, k ≠ 0 → u - v ≠ (k : ℝ) / t)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) (hlarge : 1 ≤ ‖P.eval z₀‖) :
    ∃ ξ : ℂ → ℝ, ∀ x ∈ finiteIntervalUnion T (δ / τ),
      δ ^ P.natDegree * (P.roots.map fun z => min 1 (τ * |x - ξ z|)).prod ≤
        ‖P.eval (angularCharacter (t * x))‖ := by
  have htpos : 0 < t := lt_of_lt_of_le (half_pos hτ) ht
  have hex (z : ℂ) := exists_phase_representative T (δ / τ) t
    (div_nonneg hδ hτ.le) htpos hsep (z.arg / (2 * Real.pi) / t)
  choose ξ _ hphase hgap using hex
  refine ⟨ξ, fun x hx => polynomial_weighted_distance_lower_bound P ξ hτ ht hδ hδ1 ?_ ?_ hz₀ hlarge⟩
  · intro z _
    rw [hphase z, mul_div_cancel₀ _ htpos.ne']
    exact unitCircleProjection_eq_angularCharacter z
  · intro z _ k hk
    exact hgap z x hx k hk

end Erdos522

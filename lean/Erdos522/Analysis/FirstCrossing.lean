/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# The first crossing of a continuous real function

Before a continuous function first attains a level above its initial value,
all its values stay strictly below that level.
-/

namespace Erdos522
open Set

/-- A continuous function reaching a higher level has a first positive
crossing, with strict control at every preceding nonnegative time. -/
theorem exists_first_crossing {f : ℝ → ℝ} (hf : Continuous f)
    {c T : ℝ} (hT : 0 ≤ T) (hzero : f 0 < c) (hend : c ≤ f T) :
    ∃ t ∈ Ioc (0 : ℝ) T, f t = c ∧ ∀ s ∈ Ico (0 : ℝ) t, f s < c := by
  let S := Icc (0 : ℝ) T ∩ f ⁻¹' {c}
  have hSne : S.Nonempty := by
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hT hf.continuousOn ⟨hzero.le, hend⟩
    exact ⟨x, hx, hfx⟩
  have hcompact : IsCompact S := isCompact_Icc.inter_right (isClosed_singleton.preimage hf)
  obtain ⟨t, ht, hleast⟩ := hcompact.exists_isLeast hSne
  have htc : f t = c := ht.2
  have htpos : 0 < t := by
    have := ht.1.1
    by_contra hn
    have hz : t = 0 := le_antisymm (le_of_not_gt hn) this
    rw [hz] at htc
    linarith
  refine ⟨t, ⟨htpos, ht.1.2⟩, htc, ?_⟩
  intro s hs
  by_contra hn
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hs.1 hf.continuousOn ⟨hzero.le, le_of_not_gt hn⟩
  have hxS : x ∈ S := ⟨⟨hx.1, hx.2.trans (hs.2.le.trans ht.1.2)⟩, hfx⟩
  exact (not_lt_of_ge (hleast hxS)) (hx.2.trans_lt hs.2)

end Erdos522

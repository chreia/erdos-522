/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Basic.RademacherPolynomial
import Erdos522.Probability.RademacherLogMoments
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# One infinite Rademacher sequence and its finite prefixes

The infinite product probability measure uses one coin at each natural index.
Restriction to the first `N + 1` coins has exactly the finite sign law used in
the polynomial estimates. Summable finite-prefix events therefore satisfy
Borel–Cantelli on this single shared probability space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Erdos522

/-- The sample space of one infinite sequence of fair coins. -/
abbrev RademacherSequence := ℕ → Bool

/-- The product law of one infinite fair-coin sequence. -/
def rademacherSequenceMeasure : Measure RademacherSequence :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

instance : IsProbabilityMeasure rademacherSequenceMeasure := by
  unfold rademacherSequenceMeasure
  infer_instance

/-- The first `N + 1` coordinates of an infinite sequence. -/
def rademacherPrefix (N : ℕ) (ω : RademacherSequence) : LogMoments.SignVector N :=
  fun k => ω k.val

/-- Restriction to a finite prefix is measurable. -/
theorem measurable_rademacherPrefix (N : ℕ) : Measurable (rademacherPrefix N) := by
  unfold rademacherPrefix
  fun_prop

/-- Every finite prefix has the exact product sign law. -/
theorem map_rademacherPrefix (N : ℕ) :
    rademacherSequenceMeasure.map (rademacherPrefix N) = LogMoments.signMeasure N := by
  unfold rademacherSequenceMeasure rademacherPrefix LogMoments.signMeasure
  rw [Measure.map_infinitePi_infinitePi_of_inj (fun i j h => Fin.ext h), Measure.infinitePi_eq_pi]

/-- A finite prefix is measure preserving for its finite sign distribution. -/
theorem measurePreserving_rademacherPrefix (N : ℕ) :
    MeasurePreserving (rademacherPrefix N) rademacherSequenceMeasure (LogMoments.signMeasure N) :=
  ⟨measurable_rademacherPrefix N, map_rademacherPrefix N⟩

/-- Pulling a finite event back to the infinite coin sequence preserves its probability. -/
theorem measure_rademacherPrefix_preimage (N : ℕ) (E : Set (LogMoments.SignVector N)) :
    rademacherSequenceMeasure ((rademacherPrefix N) ⁻¹' E) = (LogMoments.signMeasure N) E := by
  rw [← map_rademacherPrefix N, Measure.map_apply (measurable_rademacherPrefix N) (Set.toFinite E).measurableSet]

/-- The same finite-event identity in real-valued probability notation. -/
theorem measureReal_rademacherPrefix_preimage (N : ℕ) (E : Set (LogMoments.SignVector N)) :
    rademacherSequenceMeasure.real ((rademacherPrefix N) ⁻¹' E) = (LogMoments.signMeasure N).real E := by
  simp only [measureReal_def, measure_rademacherPrefix_preimage]

/-- The polynomial built from a prefix is the prefix of the same infinite coefficient sequence. -/
theorem rademacherPrefix_polynomial (N : ℕ) (ω : RademacherSequence) :
    rademacherPolynomial N (rademacherPrefix N ω) =
      polynomialPrefix (fun k => LogMoments.sign (ω k)) (fun _ => 1) N :=
  rademacherPolynomial_eq_prefix ω N

/-- Summable finite-prefix failures are summable on the infinite product probability space. -/
theorem summable_rademacherPrefix_preimages (n : ℕ → ℕ)
    (E : ∀ N, Set (LogMoments.SignVector N))
    (hs : Summable (fun j => (LogMoments.signMeasure (n j)).real (E (n j)))) :
    Summable (fun j => rademacherSequenceMeasure.real ((rademacherPrefix (n j)) ⁻¹' E (n j))) := by
  simpa only [measureReal_rademacherPrefix_preimage] using hs

/-- Borel–Cantelli for an indexed family of finite-prefix events. The event may depend on
    the block index as well as on the number of coordinates inspected. -/
theorem ae_eventually_indexed_rademacherPrefix_notMem (n : ℕ → ℕ)
    (E : ∀ j, Set (LogMoments.SignVector (n j)))
    (hs : Summable (fun j => (LogMoments.signMeasure (n j)).real (E j))) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j in atTop, rademacherPrefix (n j) ω ∉ E j := by
  have hsum : Summable (fun j =>
      rademacherSequenceMeasure.real ((rademacherPrefix (n j)) ⁻¹' E j)) := by
    simpa only [measureReal_rademacherPrefix_preimage] using hs
  have hfinite : (∑' j, rademacherSequenceMeasure ((rademacherPrefix (n j)) ⁻¹' E j)) ≠ ∞ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      hsum.tsum_ofReal_ne_top
  exact ae_eventually_notMem hfinite

/-- Borel–Cantelli for arbitrary finite-prefix events, without independence between degrees. -/
theorem ae_eventually_rademacherPrefix_notMem (n : ℕ → ℕ)
    (E : ∀ N, Set (LogMoments.SignVector N))
    (hs : Summable (fun j => (LogMoments.signMeasure (n j)).real (E (n j)))) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j in atTop, rademacherPrefix (n j) ω ∉ E (n j) := by
  exact ae_eventually_indexed_rademacherPrefix_notMem n (fun j => E (n j)) hs

end Erdos522

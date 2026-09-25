/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.ZeroRuns
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Independent coefficient sequences and actual degree

Finite coefficient estimates transfer to a single infinite product law.
Borel–Cantelli then bounds every sufficiently late trailing zero run, giving
the actual-degree correction simultaneously across all degree blocks.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Polynomial Filter Set
open scoped ENNReal

namespace Erdos522

/-- The law of one infinite sequence of independent coefficients with law `μ`. -/
def coefficientSequenceMeasure (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    Measure (ℕ → ℂ) := Measure.infinitePi (fun _ : ℕ => μ)

instance (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (coefficientSequenceMeasure μ) := by
  unfold coefficientSequenceMeasure
  infer_instance

/-- Restriction of one coefficient sequence to its first `N + 1` entries. -/
def coefficientPrefix (N : ℕ) (ω : ℕ → ℂ) : Fin (N + 1) → ℂ := fun k => ω k.val

theorem measurable_coefficientPrefix (N : ℕ) : Measurable (coefficientPrefix N) := by
  unfold coefficientPrefix
  fun_prop

theorem map_coefficientPrefix (μ : Measure ℂ) [IsProbabilityMeasure μ] (N : ℕ) :
    (coefficientSequenceMeasure μ).map (coefficientPrefix N) =
      Measure.pi (fun _ : Fin (N + 1) => μ) := by
  unfold coefficientSequenceMeasure coefficientPrefix
  rw [Measure.map_infinitePi_infinitePi_of_inj (fun i j h => Fin.ext h),
    Measure.infinitePi_eq_pi]

theorem measureReal_coefficientPrefix_preimage (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (N : ℕ) (E : Set (Fin (N + 1) → ℂ)) (hE : MeasurableSet E) :
    (coefficientSequenceMeasure μ).real ((coefficientPrefix N) ⁻¹' E) =
      (Measure.pi (fun _ : Fin (N + 1) => μ)).real E := by
  simp only [measureReal_def]
  rw [← map_coefficientPrefix μ N, Measure.map_apply (measurable_coefficientPrefix N) hE]

/-- Arbitrary finite coefficient events pull back with no increase in outer probability. -/
theorem measure_coefficientPrefix_preimage_le (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (N : ℕ) (E : Set (Fin (N + 1) → ℂ)) :
    coefficientSequenceMeasure μ ((coefficientPrefix N) ⁻¹' E) ≤
      (Measure.pi (fun _ : Fin (N + 1) => μ)) E := by
  rw [← map_coefficientPrefix μ N]
  exact Measure.le_map_apply (measurable_coefficientPrefix N).aemeasurable E

theorem measureReal_coefficientPrefix_preimage_le (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (N : ℕ) (E : Set (Fin (N + 1) → ℂ)) :
    (coefficientSequenceMeasure μ).real ((coefficientPrefix N) ⁻¹' E) ≤
      (Measure.pi (fun _ : Fin (N + 1) => μ)).real E :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_coefficientPrefix_preimage_le μ N E)

/-- Summable finite exceptions cease on any degree schedule for the shared
coefficient sequence. Events may use outer probability. -/
theorem ae_eventually_indexed_coefficientPrefix_notMem
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (n : ℕ → ℕ)
    (E : ∀ j, Set (Fin (n j + 1) → ℂ))
    (hs : Summable (fun j => (Measure.pi (fun _ : Fin (n j + 1) => μ)).real (E j))) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ᶠ j in atTop, coefficientPrefix (n j) ω ∉ E j := by
  have hsum : Summable (fun j =>
      (coefficientSequenceMeasure μ).real ((coefficientPrefix (n j)) ⁻¹' E j)) :=
    Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) (fun j =>
      measureReal_coefficientPrefix_preimage_le μ (n j) (E j)) hs
  have hfinite : (∑' j, coefficientSequenceMeasure μ ((coefficientPrefix (n j)) ⁻¹' E j)) ≠ ∞ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      hsum.tsum_ofReal_ne_top
  exact ae_eventually_notMem hfinite

/-- A property holding almost surely for one coefficient holds simultaneously
at every coordinate of the infinite sequence. -/
theorem ae_coefficientSequence_coordinates (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (p : ℂ → Prop) (hp : ∀ᵐ z ∂μ, p z) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ k, p (ω k) := by
  apply ae_all_iff.mpr
  intro k
  have hm : MeasurePreserving (fun ω : ℕ → ℂ => ω k) (coefficientSequenceMeasure μ) μ :=
    measurePreserving_eval_infinitePi _ k
  exact hm.quasiMeasurePreserving.ae hp

/-- A coefficient law without a zero atom gives the nominal degree and a
nonzero constant coefficient simultaneously for every prefix. -/
theorem ae_polynomialPrefix_degree_and_constant
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (hμ : μ {0} = 0) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ N,
      (polynomialPrefix ω (fun _ => 1) N).natDegree = N ∧
      (polynomialPrefix ω (fun _ => 1) N).coeff 0 ≠ 0 := by
  have hcoord : ∀ᵐ z ∂μ, z ≠ 0 := by
    rw [ae_iff]
    have he : {z : ℂ | ¬ z ≠ 0} = {0} := by ext z; simp
    rw [he]
    exact hμ
  filter_upwards [ae_coefficientSequence_coordinates μ (fun z => z ≠ 0) hcoord] with ω hω
  intro N
  constructor
  · exact polynomialPrefix_natDegree ω (fun _ => 1) N (by simpa using hω N)
  · simpa using hω 0

/-- The finite vector polynomial is exactly the corresponding nested prefix. -/
theorem coefficientPrefix_polynomial (N : ℕ) (ω : ℕ → ℂ) :
    Polynomial.ofFn (N + 1) (coefficientPrefix N ω) =
      polynomialPrefix ω (fun _ => 1) N := by
  ext k
  by_cases hk : k < N + 1
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hk, polynomialPrefix_coeff,
      ite_eq_left (by omega)]
    simp [coefficientPrefix]
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega), polynomialPrefix_coeff,
      ite_eq_right (by omega)]

/-- Summable measurable finite-prefix events eventually cease on the shared
infinite coefficient space. Independence between different degrees is unnecessary. -/
theorem ae_eventually_coefficientPrefix_notMem (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (E : ∀ N, Set (Fin (N + 1) → ℂ)) (hE : ∀ N, MeasurableSet (E N))
    (hs : Summable (fun N => (Measure.pi (fun _ : Fin (N + 1) => μ)).real (E N))) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ᶠ N in atTop, coefficientPrefix N ω ∉ E N := by
  have hsum : Summable (fun N =>
      (coefficientSequenceMeasure μ).real ((coefficientPrefix N) ⁻¹' E N)) := by
    simpa only [measureReal_coefficientPrefix_preimage μ _ _ (hE _)] using hs
  have hfinite : (∑' N, coefficientSequenceMeasure μ ((coefficientPrefix N) ⁻¹' E N)) ≠ ∞ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      hsum.tsum_ofReal_ne_top
  exact ae_eventually_notMem hfinite

/-- A logarithmic trailing-run bound holds eventually for every degree of the
same coefficient sequence. The auxiliary `q` may be any positive upper bound
below one for the zero atom. -/
theorem ae_eventually_polynomialPrefix_degree_deficit_le
    (μ : Measure ℂ) [IsProbabilityMeasure μ] {q D : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hatom : μ.real {0} ≤ q)
    (hD : 4 ≤ -D * Real.log q) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ᶠ N in atTop,
      N ≤ (polynomialPrefix ω (fun _ => 1) N).natDegree +
        ⌈D * Real.log (N + 1 : ℕ)⌉₊ := by
  classical
  let L (N : ℕ) := ⌈D * Real.log (N + 1 : ℕ)⌉₊
  let E (N : ℕ) : Set (Fin (N + 1) → ℂ) :=
    if h : L N ≤ N then
      zeroCoordinates (Finset.Ioi (⟨N - L N, by omega⟩ : Fin (N + 1))) else ∅
  have hE : ∀ N, MeasurableSet (E N) := by
    intro N
    dsimp [E]
    split_ifs
    · exact measurableSet_zeroCoordinates _
    · exact MeasurableSet.empty
  have hbound (N : ℕ) :
      (Measure.pi (fun _ : Fin (N + 1) => μ)).real (E N) ≤ q ^ L N := by
    dsimp [E]
    split_ifs with h
    · rw [measureReal_zeroCoordinates, Fin.card_Ioi]
      have hcard : N + 1 - 1 - (N - L N) = L N := by omega
      change (μ.real {0}) ^ (N + 1 - 1 - (N - L N)) ≤ q ^ L N
      rw [hcard]
      exact pow_le_pow_left₀ (measureReal_nonneg) hatom _
    · simp only [measureReal_empty]
      exact pow_nonneg hq.le _
  have hs := (summable_geometric_logarithmic_cutoff hq hq1 hD).of_nonneg_of_le
    (fun N => (measureReal_nonneg :
      0 ≤ (Measure.pi (fun _ : Fin (N + 1) => μ)).real (E N))) hbound
  filter_upwards [ae_eventually_coefficientPrefix_notMem μ E hE hs] with ω hω
  filter_upwards [hω] with N hN
  change N ≤ (polynomialPrefix ω (fun _ => 1) N).natDegree + L N
  by_cases hL : L N ≤ N
  · by_contra hdeg
    apply hN
    dsimp [E]
    rw [dite_eq_left hL]
    apply natDegree_add_le_mem_zeroCoordinates hL
    rw [coefficientPrefix_polynomial]
    omega
  · omega

/-- Every sufficiently late block has actual-degree increase at most its
length plus the same logarithmic correction at its left endpoint. -/
theorem ae_eventually_polynomialPrefix_degree_increase_le
    (μ : Measure ℂ) [IsProbabilityMeasure μ] {q D : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hatom : μ.real {0} ≤ q)
    (hD : 4 ≤ -D * Real.log q) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ᶠ N in atTop, ∀ m : ℕ,
      (polynomialPrefix ω (fun _ => 1) (N + m)).natDegree -
        (polynomialPrefix ω (fun _ => 1) N).natDegree ≤
          m + ⌈D * Real.log (N + 1 : ℕ)⌉₊ := by
  filter_upwards [ae_eventually_polynomialPrefix_degree_deficit_le μ hq hq1 hatom hD] with ω hω
  filter_upwards [hω] with N hN
  exact fun m => polynomialPrefix_degree_increase_le ω (fun _ => 1) hN

/-- A coefficient law with a zero atom smaller than one produces nonzero
prefixes at every sufficiently large degree, on the shared sequence space. -/
theorem ae_eventually_polynomialPrefix_ne_zero (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hatom : μ.real {0} < 1) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ᶠ N in atTop,
      polynomialPrefix ω (fun _ => 1) N ≠ 0 := by
  let E (N : ℕ) := zeroCoordinates (Finset.univ : Finset (Fin (N + 1)))
  have hs : Summable (fun N => (Measure.pi (fun _ : Fin (N + 1) => μ)).real (E N)) := by
    simp only [E, measureReal_zeroCoordinates, Finset.card_univ, Fintype.card_fin]
    exact (summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one measureReal_nonneg hatom)
  filter_upwards [ae_eventually_coefficientPrefix_notMem μ E
    (fun _ => measurableSet_zeroCoordinates _) hs] with ω hω
  filter_upwards [hω] with N hN
  rw [← coefficientPrefix_polynomial]
  exact fun hz => hN ((ofFn_eq_zero_iff_zeroCoordinates _ _).mp hz)

/-- A positive geometric majorant for the atom at zero. -/
def zeroRunProbability (μ : Measure ℂ) : ℝ := max (μ.real {0}) (1 / 2)

/-- An explicit logarithmic correction whose zero-run probabilities are bounded
by fourth inverse powers. -/
def zeroRunLogarithmicConstant (μ : Measure ℂ) : ℝ :=
  4 / (-Real.log (zeroRunProbability μ))

theorem zeroRunProbability_pos (μ : Measure ℂ) : 0 < zeroRunProbability μ :=
  lt_of_lt_of_le (by norm_num) (le_max_right _ _)

theorem zeroRunProbability_lt_one (μ : Measure ℂ) (hatom : μ.real {0} < 1) :
    zeroRunProbability μ < 1 := max_lt hatom (by norm_num)

theorem zeroRunLogarithmicConstant_mul_log (μ : Measure ℂ) (hatom : μ.real {0} < 1) :
    -zeroRunLogarithmicConstant μ * Real.log (zeroRunProbability μ) = 4 := by
  have hn : Real.log (zeroRunProbability μ) ≠ 0 :=
    ne_of_lt (Real.log_neg (zeroRunProbability_pos μ) (zeroRunProbability_lt_one μ hatom))
  unfold zeroRunLogarithmicConstant
  field_simp

/-- The explicit almost-sure degree correction for any nontrivial coefficient
law, including laws with an atom at zero. -/
theorem ae_eventually_actual_degree_correction (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hatom : μ.real {0} < 1) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ᶠ N in atTop,
      N ≤ (polynomialPrefix ω (fun _ => 1) N).natDegree +
        ⌈zeroRunLogarithmicConstant μ * Real.log (N + 1 : ℕ)⌉₊ ∧
      ∀ m : ℕ, (polynomialPrefix ω (fun _ => 1) (N + m)).natDegree -
        (polynomialPrefix ω (fun _ => 1) N).natDegree ≤
          m + ⌈zeroRunLogarithmicConstant μ * Real.log (N + 1 : ℕ)⌉₊ := by
  have hD : 4 ≤ -zeroRunLogarithmicConstant μ * Real.log (zeroRunProbability μ) :=
    (zeroRunLogarithmicConstant_mul_log μ hatom).ge
  have hdeg := ae_eventually_polynomialPrefix_degree_deficit_le μ
    (zeroRunProbability_pos μ) (zeroRunProbability_lt_one μ hatom) (le_max_left _ _) hD
  filter_upwards [hdeg] with ω hω
  filter_upwards [hω] with N hN
  exact ⟨hN, fun _ => polynomialPrefix_degree_increase_le ω (fun _ => 1) hN⟩

/-- Once the first nonzero coefficient has appeared, the root multiplicity at
the origin is constant for all subsequent prefixes. -/
theorem polynomialPrefix_rootMultiplicity_zero_of_first_nonzero (ω : ℕ → ℂ)
    {k N : ℕ} (hk : ω k ≠ 0) (hbefore : ∀ j < k, ω j = 0) (hkN : k ≤ N) :
    (polynomialPrefix ω (fun _ => 1) N).rootMultiplicity 0 = k := by
  have hcoeff : (polynomialPrefix ω (fun _ => 1) N).coeff k ≠ 0 := by
    simpa only [polynomialPrefix_coeff, ite_eq_left hkN, mul_one] using hk
  have hP : polynomialPrefix ω (fun _ => 1) N ≠ 0 := by
    intro hzero
    exact hcoeff (by rw [hzero, Polynomial.coeff_zero])
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree']
  apply le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hcoeff)
  apply Polynomial.le_natTrailingDegree hP
  intro j hj
  simp only [polynomialPrefix_coeff, ite_eq_left (by omega : j ≤ N), mul_one,
    hbefore j hj]

/-- Almost surely one finite initial run fixes the multiplicity at zero of
every later polynomial in the same sequence. -/
theorem ae_exists_initial_zero_multiplicity (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hatom : μ.real {0} < 1) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∃ k : ℕ,
      ω k ≠ 0 ∧ (∀ j < k, ω j = 0) ∧ ∀ N, k ≤ N →
        (polynomialPrefix ω (fun _ => 1) N).rootMultiplicity 0 = k := by
  classical
  filter_upwards [ae_eventually_polynomialPrefix_ne_zero μ hatom] with ω hω
  obtain ⟨N, hN⟩ := hω.exists
  have hex : ∃ k, ω k ≠ 0 := by
    by_contra h
    push Not at h
    apply hN
    ext j
    simp [h]
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, ?_⟩
  · intro j hj
    exact not_ne_iff.mp (Nat.find_min hex hj)
  · intro N hN
    exact polynomialPrefix_rootMultiplicity_zero_of_first_nonzero ω (Nat.find_spec hex)
      (fun j hj => not_ne_iff.mp (Nat.find_min hex hj)) hN

end Erdos522

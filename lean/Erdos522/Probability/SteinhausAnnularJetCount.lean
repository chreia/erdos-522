/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AnnularJetCount
import Erdos522.Probability.GaussianApproximation.CircularPairedSmallBall

/-!
# Small Steinhaus jets on annular meshes

The four- and eight-dimensional circular approximations yield concentration
of mesh detections. A common finite envelope retains the exact square-root
normalization and absorbs the circular approximation constants by a factor
of eight.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace Erdos522
namespace SteinhausAnnularJetCount

/-- The circular four-dimensional error fits the common annular envelope. -/
theorem circular_jet_error_majorant (C K : ℝ) (hC : 0 ≤ C) :
    circularJetGaussianErrorConstant C K ≤ jetGaussianErrorConstant (8 * C) K := by
  have hden : 0 < Real.sqrt (Real.exp (-4 * K) / 80) ^ 3 := by positivity
  have hcompare : Real.sqrt (Real.exp (-4 * K) / 80) ^ 3 ≤
      Real.sqrt (Real.exp (-4 * K) / 32) ^ 3 := by
    apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
    apply Real.sqrt_le_sqrt
    nlinarith [Real.exp_pos (-4 * K)]
  unfold circularJetGaussianErrorConstant jetGaussianErrorConstant
  have hnum : 0 ≤ 128 * C * (4 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (3 * K) := by positivity
  calc
    _ ≤ (128 * C * (4 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (3 * K)) /
        Real.sqrt (Real.exp (-4 * K) / 80) ^ 3 :=
      div_le_div_of_nonneg_left hnum hden hcompare
    _ = _ := by ring

/-- The circular small-ball density and approximation error admit one finite envelope. -/
theorem circular_jet_small_ball_majorant (N : ℕ) (C K u v : ℝ) (hC : 0 ≤ C) :
    u ^ 2 * v ^ 2 / (4 * (Real.exp (-4 * K) / 32) ^ 2) +
        circularJetGaussianErrorConstant C K / Real.sqrt N ≤
      annularJetProbabilityBound N (8 * C) K u v := by
  apply add_le_add _ (div_le_div_of_nonneg_right (circular_jet_error_majorant C K hC)
    (Real.sqrt_nonneg _))
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have h := Real.exp_pos (-4 * K)
  nlinarith [sq_nonneg (Real.exp (-4 * K))]

/-- Both circular approximation errors fit the separated-pair envelope. -/
theorem circular_jet_pair_majorant (C K : ℝ) (hC : 0 ≤ C) :
    2 * circularJetGaussianErrorConstant C K + circularPairedJetGaussianErrorConstant C K +
        80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80) ≤
      annularJetPairConstant (8 * C) K := by
  have hpair : circularPairedJetGaussianErrorConstant C K =
      pairedJetGaussianErrorConstant (8 * C) K := by
    unfold circularPairedJetGaussianErrorConstant pairedJetGaussianErrorConstant
    ring
  unfold annularJetPairConstant
  rw [hpair]
  linarith [circular_jet_error_majorant C K hC]

/-- Closed polynomial jet events are measurable in their complex coefficients. -/
theorem measurableSet_circularPolynomialJetSmallBallEvent (N : ℕ) (w : ℂ) (u v : ℝ) :
    MeasurableSet (circularPolynomialJetSmallBallEvent N w u v) := by
  unfold circularPolynomialJetSmallBallEvent
  apply MeasurableSet.inter
  · change MeasurableSet {a : Fin (N + 1) → ℂ |
      ‖(Polynomial.ofFn (N + 1) a).eval w‖ ≤ u * Real.sqrt N}
    apply measurableSet_le _ measurable_const
    simp only [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
      Polynomial.eval_monomial]
    fun_prop
  · change MeasurableSet {a : Fin (N + 1) → ℂ |
      ‖w * (Polynomial.ofFn (N + 1) a).derivative.eval w‖ ≤ v * ((N : ℝ) * Real.sqrt N)}
    apply measurableSet_le _ measurable_const
    simp only [ofFn_radial_derivative]
    fun_prop

/-- A closed jet event at an angularly retained mesh index. -/
def retainedAnnularJetEvent (N : ℕ) (K h u v : ℝ) (i : AnnularMeshIndex N K h) :
    Set (Fin (N + 1) → ℂ) :=
  {ω | 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle h i.2) ∧
    ω ∈ circularPolynomialJetSmallBallEvent N (annularMeshPoint N K h i) u v}

/-- Every retained mesh event is measurable on the complex coefficient space. -/
theorem measurableSet_retainedAnnularJetEvent (N : ℕ) (K h u v : ℝ)
    (i : AnnularMeshIndex N K h) : MeasurableSet (retainedAnnularJetEvent N K h u v i) :=
  by
    unfold retainedAnnularJetEvent
    by_cases hi : 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle h i.2)
    · simpa only [hi, true_and, circularPolynomialJetSmallBallEvent, Set.mem_ofPred_eq] using
        measurableSet_circularPolynomialJetSmallBallEvent N (annularMeshPoint N K h i) u v
    · simp only [hi, false_and, Set.ofPred_false, MeasurableSet.empty]

/-- At a retained index, the angular predicate may be removed from the event. -/
theorem retainedAnnularJetEvent_eq (N : ℕ) (K h u v : ℝ) (i : AnnularMeshIndex N K h)
    (hi : 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle h i.2)) :
    retainedAnnularJetEvent N K h u v i =
      circularPolynomialJetSmallBallEvent N (annularMeshPoint N K h i) u v := by
  ext ω
  exact and_iff_right hi

/-- An excluded angular index contributes the empty event. -/
theorem retainedAnnularJetEvent_eq_empty (N : ℕ) (K h u v : ℝ) (i : AnnularMeshIndex N K h)
    (hi : ¬1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle h i.2)) :
    retainedAnnularJetEvent N K h u v i = ∅ := by
  ext ω
  constructor
  · intro hω
    exact (hi hω.1).elim
  · intro hω
    exact hω.elim

/-- One-point small-ball bounds hold at every retained point of the actual annular mesh. -/
theorem exists_retained_annular_jet_probability_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K h u v : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : 0 < h) (_ : 0 ≤ u) (_ : 0 ≤ v)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (i : AnnularMeshIndex N K h),
      (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real (retainedAnnularJetEvent N K h u v i) ≤
        annularJetProbabilityBound N C K u v := by
  obtain ⟨C, hC, h⟩ := exists_steinhaus_polynomial_jet_small_ball_constant
  refine ⟨8 * C, by positivity, ?_⟩
  intro N hN K hmesh u v hK hKN hh hu hv _hdegree i
  by_cases hi : 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle hmesh i.2)
  · rw [retainedAnnularJetEvent_eq N K hmesh u v i hi, annularMeshPoint_eq_exp]
    have hr := annularMeshRadius_mem hN hK hh i.1
    exact (h N hN K (annularMeshRadius N K hmesh i.1) hK hKN hr.1 hr.2
      (Complex.exp (Complex.I * annularMeshRadians hmesh i.2))
      (Complex.norm_exp_I_mul_ofReal _) u v hu hv).trans
        (circular_jet_small_ball_majorant N C K u v hC.le)
  · rw [retainedAnnularJetEvent_eq_empty N K hmesh u v i hi, measureReal_empty]
    unfold annularJetProbabilityBound
    have hG := jetGaussianErrorConstant_pos (8 * C) K (by positivity)
    positivity

/-- Separated retained mesh events factorize up to the actual eight-dimensional error. -/
theorem exists_retained_annular_jet_pair_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K h u v : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : 0 < h)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (i j : AnnularMeshIndex N K h)
      (_ : 1 / Real.sqrt N ≤ ‖annularMeshAngle h i.2 - annularMeshAngle h j.2‖)
      (_ : 1 / Real.sqrt N ≤ ‖annularMeshAngle h i.2 + annularMeshAngle h j.2‖),
      |(Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real
          (retainedAnnularJetEvent N K h u v i ∩ retainedAnnularJetEvent N K h u v j) -
        (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real (retainedAnnularJetEvent N K h u v i) *
          (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real (retainedAnnularJetEvent N K h u v j)| ≤
        annularJetPairConstant C K / Real.sqrt N := by
  obtain ⟨C, hC, h⟩ := exists_steinhaus_polynomial_small_ball_factorization_constant
  refine ⟨8 * C, by positivity, ?_⟩
  intro N hN K hmesh u v hK hKN hh hdegree i j hd hs
  have hpos : 0 ≤ annularJetPairConstant (8 * C) K / Real.sqrt N := by
    exact div_nonneg (annularJetPairConstant_pos (8 * C) K (by positivity)).le (Real.sqrt_nonneg _)
  by_cases hi : 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle hmesh i.2)
  · by_cases hj : 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle hmesh j.2)
    · rw [retainedAnnularJetEvent_eq N K hmesh u v i hi,
        retainedAnnularJetEvent_eq N K hmesh u v j hj, annularMeshPoint_eq_exp, annularMeshPoint_eq_exp]
      have hri := annularMeshRadius_mem hN hK hh i.1
      have hrj := annularMeshRadius_mem hN hK hh j.1
      have hd' : 1 / Real.sqrt N ≤
          ‖((annularMeshRadians hmesh i.2 - annularMeshRadians hmesh j.2 : ℝ) : Real.Angle)‖ := by
        rwa [Real.Angle.coe_sub]
      have hs' : 1 / Real.sqrt N ≤
          ‖((annularMeshRadians hmesh i.2 + annularMeshRadians hmesh j.2 : ℝ) : Real.Angle)‖ := by
        rwa [Real.Angle.coe_add]
      apply (h N hN K (annularMeshRadius N K hmesh i.1) (annularMeshRadius N K hmesh j.1)
        (annularMeshRadians hmesh i.2) (annularMeshRadians hmesh j.2)
        hK hKN hri.1 hri.2 hrj.1 hrj.2 hdegree
        (retained_annularMeshAngle_nondegenerate i.2 hi) (retained_annularMeshAngle_nondegenerate j.2 hj)
        hd' hs' u v u v).trans
      exact div_le_div_of_nonneg_right (circular_jet_pair_majorant C K hC.le) (Real.sqrt_nonneg _)
    · rw [retainedAnnularJetEvent_eq_empty N K hmesh u v j hj]
      simpa using hpos
  · rw [retainedAnnularJetEvent_eq_empty N K hmesh u v i hi]
    simpa using hpos

/-- The retained event count is precisely the number of deterministic mesh detections. -/
theorem indicatorCount_retainedAnnularJetEvent_eq {N : ℕ} (hN : 0 < N) (K S L : ℝ)
    (ω : Fin (N + 1) → ℂ) :
    indicatorCount (retainedAnnularJetEvent N K (derivativeMeshSpacing N S L)
      (derivativeMeshValueThreshold N S L) (3 / L)) ω =
      (detectedAnnularMesh (Polynomial.ofFn (N + 1) ω) N K S L).card := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hevent (i : AnnularMeshIndex N K (derivativeMeshSpacing N S L)) :
      ω ∈ retainedAnnularJetEvent N K (derivativeMeshSpacing N S L)
        (derivativeMeshValueThreshold N S L) (3 / L) i ↔
      i ∈ detectedAnnularMesh (Polynomial.ofFn (N + 1) ω) N K S L := by
    simp only [retainedAnnularJetEvent, circularPolynomialJetSmallBallEvent, Set.mem_ofPred_eq,
      detectedAnnularMesh, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [← degree_mul_sqrt_eq_three_halves N hN, div_le_iff₀ hs, div_le_iff₀ (mul_pos hNr hs)]
  unfold indicatorCount
  rw [detectedAnnularMesh]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro i _
  change (if ω ∈ retainedAnnularJetEvent N K (derivativeMeshSpacing N S L)
    (derivativeMeshValueThreshold N S L) (3 / L) i then (1 : ℝ) else 0) = _
  rw [hevent i]
  simp only [detectedAnnularMesh, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The derivative-mesh detections satisfy a quantitative tail estimate under the actual Steinhaus law. -/
theorem exists_annular_mesh_detection_constants :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (N : ℕ) (_ : 2 ≤ N) (K S L Q : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : 1 ≤ S) (_ : 1 ≤ L)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ)) (_ : 0 < Q)
      (_ : (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) *
        annularJetProbabilityBound N C₁ K (derivativeMeshValueThreshold N S L) (3 / L) ≤ Q / 2),
      (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real {ω | Q ≤
        (detectedAnnularMesh (Polynomial.ofFn (N + 1) ω) N K S L).card} ≤
      4 * (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) ^ 2 *
        (annularJetPairConstant C₂ K +
          5 * annularJetProbabilityBound N C₁ K (derivativeMeshValueThreshold N S L) (3 / L)) /
        (Real.sqrt N * Q ^ 2) := by
  obtain ⟨C₁, hC₁, hpoint⟩ := exists_retained_annular_jet_probability_constant
  obtain ⟨C₂, hC₂, hpair⟩ := exists_retained_annular_jet_pair_constant
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro N hN K S L Q hK hKN hS hL hdegree hQ hthreshold
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hh := (derivativeMeshSpacing_le_inv_degree hN hS hL).1
  let h := derivativeMeshSpacing N S L
  let u := derivativeMeshValueThreshold N S L
  let v := 3 / L
  let E := retainedAnnularJetEvent N K h u v
  let p := annularJetProbabilityBound N C₁ K u v
  let ε := annularJetPairConstant C₂ K / Real.sqrt N
  let D : Finset (AnnularMeshIndex N K h × AnnularMeshIndex N K h) := Finset.univ.filter fun ij =>
    ‖annularMeshAngle h ij.1.2 - annularMeshAngle h ij.2.2‖ ≤ 1 / Real.sqrt N ∨
    ‖annularMeshAngle h ij.1.2 + annularMeshAngle h ij.2.2‖ ≤ 1 / Real.sqrt N
  have hu : 0 ≤ u := by dsimp [u, derivativeMeshValueThreshold]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hp : 0 ≤ p := by
    dsimp [p, annularJetProbabilityBound]
    have hG := jetGaussianErrorConstant_pos C₁ K hC₁
    positivity
  have hε : 0 ≤ ε := div_nonneg (annularJetPairConstant_pos C₂ K hC₂).le hsqrt.le
  have hprob (i : AnnularMeshIndex N K h) : (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real (E i) ≤ p :=
    hpoint N hNp K h u v hK hKN hh hu hv hdegree i
  have hcov (i j : AnnularMeshIndex N K h) (hij : (i, j) ∉ D) :
      |(Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real (E i ∩ E j) -
        (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real (E i) * (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real (E j)| ≤ ε := by
    have hsep : ¬ (‖annularMeshAngle h i.2 - annularMeshAngle h j.2‖ ≤ 1 / Real.sqrt N ∨
        ‖annularMeshAngle h i.2 + annularMeshAngle h j.2‖ ≤ 1 / Real.sqrt N) := by
      intro hb
      exact hij (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
    exact hpair N hNp K h u v hK hKN hh hdegree i j
      (lt_of_not_ge (not_or.mp hsep).1).le (lt_of_not_ge (not_or.mp hsep).2).le
  have htail := measureReal_indicatorCount_ge_le E
    (measurableSet_retainedAnnularJetEvent N K h u v) D hp hε hQ hprob hcov hthreshold
  have hcard := derivative_mesh_close_pairs_le (K := K) hN hS hL
  have hbound : 4 * ((Fintype.card (AnnularMeshIndex N K h) : ℝ) ^ 2 * ε + (D.card : ℝ) * p) / Q ^ 2 ≤
      4 * (Fintype.card (AnnularMeshIndex N K h) : ℝ) ^ 2 *
        (annularJetPairConstant C₂ K + 5 * p) / (Real.sqrt N * Q ^ 2) := by
    have hd : (D.card : ℝ) ≤
        5 * (Fintype.card (AnnularMeshIndex N K h) : ℝ) ^ 2 / Real.sqrt N := hcard
    calc
      _ ≤ 4 * ((Fintype.card (AnnularMeshIndex N K h) : ℝ) ^ 2 * ε +
          (5 * (Fintype.card (AnnularMeshIndex N K h) : ℝ) ^ 2 / Real.sqrt N) * p) / Q ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_right hd hp) _) (by norm_num))
          (sq_nonneg _)
      _ = _ := by dsimp [ε]; ring
  have heq : indicatorCount E = fun ω =>
      ((detectedAnnularMesh (Polynomial.ofFn (N + 1) ω) N K S L).card : ℝ) := by
    funext ω
    exact indicatorCount_retainedAnnularJetEvent_eq hNp K S L ω
  rw [heq] at htail
  exact htail.trans hbound

end SteinhausAnnularJetCount
end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.IndicatorCounts
import Erdos522.Probability.GaussianApproximation.PairedSmallBall
import Erdos522.Stability.AngularMeshPairs
import Erdos522.Stability.MeshRootCount

/-!
# Counts of small jets on an annular mesh

The events use one common Rademacher polynomial. Angularly retained mesh
points satisfy the four-dimensional covariance lower bound, and separated
pairs satisfy the eight-dimensional factorization estimate. The finite
exceptional-pair count then gives concentration of the number of detections.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace Erdos522

/-- The real angular representative used to evaluate a mesh point. -/
def annularMeshRadians (h : ℝ) (i : Fin (annularAngularSamples h)) : ℝ :=
  2 * Real.pi * i.val / annularAngularSamples h

/-- The polar coordinates of an annular mesh point agree with its exponential representation. -/
theorem annularMeshPoint_eq_exp (N : ℕ) (K h : ℝ) (i : AnnularMeshIndex N K h) :
    annularMeshPoint N K h i = annularMeshRadius N K h i.1 *
      Complex.exp (Complex.I * annularMeshRadians h i.2) := by
  simp only [annularMeshPoint, annularMeshAngle, Real.Angle.toCircle_coe, Circle.coe_exp,
    annularMeshRadians]
  congr 2
  ring

/-- Retention away from the real sectors supplies the covariance separation condition. -/
theorem retained_annularMeshAngle_nondegenerate {N : ℕ} {h : ℝ}
    (i : Fin (annularAngularSamples h))
    (hi : 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle h i)) :
    1 / Real.sqrt N ≤ ‖((2 * annularMeshRadians h i : ℝ) : Real.Angle)‖ := by
  have heq : ((2 * annularMeshRadians h i : ℝ) : Real.Angle) =
      (2 : ℕ) • annularMeshAngle h i := by
    rw [two_mul, Real.Angle.coe_add, two_nsmul]
    rfl
  rw [heq]
  change 1 / Real.sqrt N ≤ ‖(2 : ℕ) • annularMeshAngle h i‖ / 2 at hi
  have hnorm := norm_nonneg ((2 : ℕ) • annularMeshAngle h i)
  linarith

/-- A closed jet event at an angularly retained mesh index. -/
def retainedAnnularJetEvent (N : ℕ) (K h u v : ℝ) (i : AnnularMeshIndex N K h) :
    Set (LogMoments.SignVector N) :=
  {ω | 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle h i.2) ∧
    ω ∈ polynomialJetSmallBallEvent N (annularMeshPoint N K h i) u v}

/-- Every retained mesh event is measurable on the finite sign space. -/
theorem measurableSet_retainedAnnularJetEvent (N : ℕ) (K h u v : ℝ)
    (i : AnnularMeshIndex N K h) : MeasurableSet (retainedAnnularJetEvent N K h u v i) :=
  (Set.toFinite _).measurableSet

/-- At a retained index, the angular predicate may be removed from the event. -/
theorem retainedAnnularJetEvent_eq (N : ℕ) (K h u v : ℝ) (i : AnnularMeshIndex N K h)
    (hi : 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle h i.2)) :
    retainedAnnularJetEvent N K h u v i =
      polynomialJetSmallBallEvent N (annularMeshPoint N K h i) u v := by
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

/-- The explicit one-point jet probability bound. -/
def annularJetProbabilityBound (N : ℕ) (C K u v : ℝ) : ℝ :=
  u ^ 2 * v ^ 2 / (4 * (Real.exp (-4 * K) / 80) ^ 2) +
    jetGaussianErrorConstant C K / Real.sqrt N

/-- The coefficient in the separated-pair factorization error. -/
def annularJetPairConstant (C K : ℝ) : ℝ :=
  2 * jetGaussianErrorConstant C K + pairedJetGaussianErrorConstant C K +
    80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)

/-- The separated-pair coefficient is positive for a positive Gaussian approximation constant. -/
theorem annularJetPairConstant_pos (C K : ℝ) (hC : 0 < C) : 0 < annularJetPairConstant C K := by
  unfold annularJetPairConstant
  have h₁ := jetGaussianErrorConstant_pos C K hC
  have h₂ := pairedJetGaussianErrorConstant_pos C K hC
  positivity

/-- One-point small-ball bounds hold at every retained point of the actual annular mesh. -/
theorem exists_retained_annular_jet_probability_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K h u v : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : 0 < h) (_ : 0 ≤ u) (_ : 0 ≤ v)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (i : AnnularMeshIndex N K h),
      (LogMoments.signMeasure N).real (retainedAnnularJetEvent N K h u v i) ≤
        annularJetProbabilityBound N C K u v := by
  obtain ⟨C, hC, h⟩ := exists_annular_polynomial_small_ball_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K hmesh u v hK hKN hh hu hv hdegree i
  by_cases hi : 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle hmesh i.2)
  · rw [retainedAnnularJetEvent_eq N K hmesh u v i hi, annularMeshPoint_eq_exp]
    have hr := annularMeshRadius_mem hN hK hh i.1
    exact h N hN K (annularMeshRadius N K hmesh i.1) (annularMeshRadians hmesh i.2)
      hK hKN hr.1 hr.2 hdegree (retained_annularMeshAngle_nondegenerate i.2 hi) u v hu hv
  · rw [retainedAnnularJetEvent_eq_empty N K hmesh u v i hi, measureReal_empty]
    unfold annularJetProbabilityBound
    have hG := jetGaussianErrorConstant_pos C K hC
    positivity

/-- Separated retained mesh events factorize up to the actual eight-dimensional error. -/
theorem exists_retained_annular_jet_pair_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K h u v : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : 0 < h)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (i j : AnnularMeshIndex N K h)
      (_ : 1 / Real.sqrt N ≤ ‖annularMeshAngle h i.2 - annularMeshAngle h j.2‖)
      (_ : 1 / Real.sqrt N ≤ ‖annularMeshAngle h i.2 + annularMeshAngle h j.2‖),
      |(LogMoments.signMeasure N).real
          (retainedAnnularJetEvent N K h u v i ∩ retainedAnnularJetEvent N K h u v j) -
        (LogMoments.signMeasure N).real (retainedAnnularJetEvent N K h u v i) *
          (LogMoments.signMeasure N).real (retainedAnnularJetEvent N K h u v j)| ≤
        annularJetPairConstant C K / Real.sqrt N := by
  obtain ⟨C, hC, h⟩ := exists_annular_polynomial_small_ball_factorization_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K hmesh u v hK hKN hh hdegree i j hd hs
  have hpos : 0 ≤ annularJetPairConstant C K / Real.sqrt N := by
    exact div_nonneg (annularJetPairConstant_pos C K hC).le (Real.sqrt_nonneg _)
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
      exact h N hN K (annularMeshRadius N K hmesh i.1) (annularMeshRadius N K hmesh j.1)
        (annularMeshRadians hmesh i.2) (annularMeshRadians hmesh j.2)
        hK hKN hri.1 hri.2 hrj.1 hrj.2 hdegree
        (retained_annularMeshAngle_nondegenerate i.2 hi) (retained_annularMeshAngle_nondegenerate j.2 hj)
        hd' hs' u v u v
    · rw [retainedAnnularJetEvent_eq_empty N K hmesh u v j hj]
      simpa using hpos
  · rw [retainedAnnularJetEvent_eq_empty N K hmesh u v i hi]
    simpa using hpos

/-- The retained event count is precisely the number of deterministic mesh detections. -/
theorem indicatorCount_retainedAnnularJetEvent_eq {N : ℕ} (hN : 0 < N) (K S L : ℝ)
    (ω : LogMoments.SignVector N) :
    indicatorCount (retainedAnnularJetEvent N K (derivativeMeshSpacing N S L)
      (derivativeMeshValueThreshold N S L) (3 / L)) ω =
      (detectedAnnularMesh (rademacherPolynomial N ω) N K S L).card := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hevent (i : AnnularMeshIndex N K (derivativeMeshSpacing N S L)) :
      ω ∈ retainedAnnularJetEvent N K (derivativeMeshSpacing N S L)
        (derivativeMeshValueThreshold N S L) (3 / L) i ↔
      i ∈ detectedAnnularMesh (rademacherPolynomial N ω) N K S L := by
    simp only [retainedAnnularJetEvent, polynomialJetSmallBallEvent, Set.mem_ofPred_eq,
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

/-- The derivative-mesh detections satisfy a quantitative tail estimate under the actual sign law. -/
theorem exists_annular_mesh_detection_constants :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (N : ℕ) (_ : 2 ≤ N) (K S L Q : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : 1 ≤ S) (_ : 1 ≤ L)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ)) (_ : 0 < Q)
      (_ : (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) *
        annularJetProbabilityBound N C₁ K (derivativeMeshValueThreshold N S L) (3 / L) ≤ Q / 2),
      (LogMoments.signMeasure N).real {ω | Q ≤
        (detectedAnnularMesh (rademacherPolynomial N ω) N K S L).card} ≤
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
  have hprob (i : AnnularMeshIndex N K h) : (LogMoments.signMeasure N).real (E i) ≤ p :=
    hpoint N hNp K h u v hK hKN hh hu hv hdegree i
  have hcov (i j : AnnularMeshIndex N K h) (hij : (i, j) ∉ D) :
      |(LogMoments.signMeasure N).real (E i ∩ E j) -
        (LogMoments.signMeasure N).real (E i) * (LogMoments.signMeasure N).real (E j)| ≤ ε := by
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
      ((detectedAnnularMesh (rademacherPolynomial N ω) N K S L).card : ℝ) := by
    funext ω
    exact indicatorCount_retainedAnnularJetEvent_eq hNp K S L ω
  rw [heq] at htail
  exact htail.trans hbound

end Erdos522

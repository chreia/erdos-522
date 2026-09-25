/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianJetSmallBall
import Erdos522.Probability.AnnularJetCount

/-!
# Small Gaussian jets on annular meshes

Exact Gaussian small-ball bounds and separated-pair covariance comparison
control the number of mesh detections. The exceptional ordered-pair count
retains the diagonal and both angular resonances.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace Erdos522
namespace GaussianAnnularJetCount

/-- Simultaneous value and radial derivative thresholds for the actual Gaussian polynomial. -/
def polynomialJetSmallBallEvent (N : ℕ) (w : ℂ) (u v : ℝ) : Set (Fin (N + 1) → ℝ) :=
  {g | ‖(gaussianPolynomial N g).eval w‖ ≤ u * Real.sqrt N ∧
    ‖w * (gaussianPolynomial N g).derivative.eval w‖ ≤ v * ((N : ℝ) * Real.sqrt N)}

theorem measurableSet_polynomialJetSmallBallEvent (N : ℕ) (w : ℂ) (u v : ℝ) :
    MeasurableSet (polynomialJetSmallBallEvent N w u v) := by
  unfold polynomialJetSmallBallEvent
  apply MeasurableSet.inter
  · change MeasurableSet {g : Fin (N + 1) → ℝ | ‖(gaussianPolynomial N g).eval w‖ ≤ u * Real.sqrt N}
    apply measurableSet_le _ measurable_const
    simp only [gaussianPolynomial_eval]
    fun_prop
  · change MeasurableSet {g : Fin (N + 1) → ℝ | ‖w * (gaussianPolynomial N g).derivative.eval w‖ ≤ v * ((N : ℝ) * Real.sqrt N)}
    apply measurableSet_le _ measurable_const
    simp only [gaussianPolynomial_radial_derivative]
    fun_prop

/-- Gaussian value-derivative disk events approximately factor at separated annular points. -/
theorem polynomial_small_ball_factorization (N : ℕ) (hN : 0 < N) (K r s θ φ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsl : 1 - K / N ≤ s) (hsu : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hθ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (hφ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖) (u v u' v' : ℝ) :
    |(gaussianCoefficientMeasure (N + 1)).real
      (polynomialJetSmallBallEvent N (r * Complex.exp (Complex.I * θ)) u v ∩
        polynomialJetSmallBallEvent N (s * Complex.exp (Complex.I * φ)) u' v') -
      (gaussianCoefficientMeasure (N + 1)).real
        (polynomialJetSmallBallEvent N (r * Complex.exp (Complex.I * θ)) u v) *
      (gaussianCoefficientMeasure (N + 1)).real
        (polynomialJetSmallBallEvent N (s * Complex.exp (Complex.I * φ)) u' v')| ≤
      (80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N := by
  have h := gaussian_annular_jet_factorization N hN K r s θ φ hK hNK hrl hru hsl hsu
    hdegree hθ hφ hdifference hsum (jetSmallBallSet u v) (jetSmallBallSet u' v')
    (measurableSet_jetSmallBallSet u v) (measurableSet_jetSmallBallSet u' v')
  simpa only [mem_jetSmallBallSet_gaussian N hN, polynomialJetSmallBallEvent, Set.ofPred_and] using h

/-- A closed jet event at an angularly retained mesh index. -/
def retainedAnnularJetEvent (N : ℕ) (K h u v : ℝ) (i : AnnularMeshIndex N K h) :
    Set (Fin (N + 1) → ℝ) :=
  {ω | 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle h i.2) ∧
    ω ∈ polynomialJetSmallBallEvent N (annularMeshPoint N K h i) u v}

/-- Every retained mesh event is measurable under the Gaussian product law. -/
theorem measurableSet_retainedAnnularJetEvent (N : ℕ) (K h u v : ℝ)
    (i : AnnularMeshIndex N K h) : MeasurableSet (retainedAnnularJetEvent N K h u v i) :=
  by
    unfold retainedAnnularJetEvent
    by_cases hi : 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle h i.2)
    · simpa only [hi, true_and, polynomialJetSmallBallEvent, Set.mem_ofPred_eq] using measurableSet_polynomialJetSmallBallEvent N (annularMeshPoint N K h i) u v
    · simp only [hi, false_and, Set.ofPred_false, MeasurableSet.empty]

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

/-- The exact Gaussian density coefficient gives the product threshold scale. -/
def pointProbabilityBound (K u v : ℝ) : ℝ :=
  u ^ 2 * v ^ 2 / (4 * (Real.exp (-4 * K) / 80) ^ 2)

/-- The separated-pair error coefficient is the Gaussian covariance comparison constant. -/
def pairErrorConstant (K : ℝ) : ℝ :=
  80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)

/-- One-point small-ball bounds hold at every retained point of the actual annular mesh. -/
theorem retained_annular_jet_probability (N : ℕ) (hN : 0 < N) (K hmesh u v : ℝ)
    (hK : 0 ≤ K) (hKN : 2 * K ≤ N) (hh : 0 < hmesh) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (i : AnnularMeshIndex N K hmesh) :
    (gaussianCoefficientMeasure (N + 1)).real (retainedAnnularJetEvent N K hmesh u v i) ≤
      pointProbabilityBound K u v := by
  by_cases hi : 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle hmesh i.2)
  · rw [retainedAnnularJetEvent_eq N K hmesh u v i hi, annularMeshPoint_eq_exp]
    have hr := annularMeshRadius_mem hN hK hh i.1
    exact gaussian_annular_polynomial_small_ball N hN K (annularMeshRadius N K hmesh i.1) (annularMeshRadians hmesh i.2)
      hK hKN hr.1 hr.2 hdegree (retained_annularMeshAngle_nondegenerate i.2 hi) u v hu hv
  · rw [retainedAnnularJetEvent_eq_empty N K hmesh u v i hi, measureReal_empty]
    unfold pointProbabilityBound
    positivity

/-- Separated retained mesh events factorize up to the eight-dimensional covariance error. -/
theorem retained_annular_jet_pair (N : ℕ) (hN : 0 < N) (K hmesh u v : ℝ)
    (hK : 0 ≤ K) (hKN : 2 * K ≤ N) (hh : 0 < hmesh)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (i j : AnnularMeshIndex N K hmesh)
    (hd : 1 / Real.sqrt N ≤ ‖annularMeshAngle hmesh i.2 - annularMeshAngle hmesh j.2‖)
    (hs : 1 / Real.sqrt N ≤ ‖annularMeshAngle hmesh i.2 + annularMeshAngle hmesh j.2‖) :
    |(gaussianCoefficientMeasure (N + 1)).real
        (retainedAnnularJetEvent N K hmesh u v i ∩ retainedAnnularJetEvent N K hmesh u v j) -
      (gaussianCoefficientMeasure (N + 1)).real (retainedAnnularJetEvent N K hmesh u v i) *
      (gaussianCoefficientMeasure (N + 1)).real (retainedAnnularJetEvent N K hmesh u v j)| ≤
      pairErrorConstant K / Real.sqrt N := by
  have hpos : 0 ≤ pairErrorConstant K / Real.sqrt N := by unfold pairErrorConstant; positivity
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
      exact polynomial_small_ball_factorization N hN K (annularMeshRadius N K hmesh i.1) (annularMeshRadius N K hmesh j.1)
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
    (ω : Fin (N + 1) → ℝ) :
    indicatorCount (retainedAnnularJetEvent N K (derivativeMeshSpacing N S L)
      (derivativeMeshValueThreshold N S L) (3 / L)) ω =
      (detectedAnnularMesh (gaussianPolynomial N ω) N K S L).card := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hevent (i : AnnularMeshIndex N K (derivativeMeshSpacing N S L)) :
      ω ∈ retainedAnnularJetEvent N K (derivativeMeshSpacing N S L)
        (derivativeMeshValueThreshold N S L) (3 / L) i ↔
      i ∈ detectedAnnularMesh (gaussianPolynomial N ω) N K S L := by
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

/-- The derivative-mesh detections satisfy a quantitative tail estimate under the actual Gaussian law. -/
theorem annular_mesh_detection (N : ℕ) (hN : 2 ≤ N) (K S L Q : ℝ)
    (hK : 0 ≤ K) (hKN : 2 * K ≤ N) (hS : 1 ≤ S) (hL : 1 ≤ L)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ)) (hQ : 0 < Q)
    (hthreshold : (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) *
      pointProbabilityBound K (derivativeMeshValueThreshold N S L) (3 / L) ≤ Q / 2) :
    (gaussianCoefficientMeasure (N + 1)).real {ω | Q ≤
      (detectedAnnularMesh (gaussianPolynomial N ω) N K S L).card} ≤
    4 * (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) ^ 2 *
      (pairErrorConstant K + 5 * pointProbabilityBound K (derivativeMeshValueThreshold N S L) (3 / L)) /
      (Real.sqrt N * Q ^ 2) := by
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hh := (derivativeMeshSpacing_le_inv_degree hN hS hL).1
  let h := derivativeMeshSpacing N S L
  let u := derivativeMeshValueThreshold N S L
  let v := 3 / L
  let E := retainedAnnularJetEvent N K h u v
  let p := pointProbabilityBound K u v
  let ε := pairErrorConstant K / Real.sqrt N
  let D : Finset (AnnularMeshIndex N K h × AnnularMeshIndex N K h) := Finset.univ.filter fun ij =>
    ‖annularMeshAngle h ij.1.2 - annularMeshAngle h ij.2.2‖ ≤ 1 / Real.sqrt N ∨
    ‖annularMeshAngle h ij.1.2 + annularMeshAngle h ij.2.2‖ ≤ 1 / Real.sqrt N
  have hu : 0 ≤ u := by dsimp [u, derivativeMeshValueThreshold]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hp : 0 ≤ p := by
    dsimp [p, pointProbabilityBound]
    positivity
  have hε : 0 ≤ ε := by dsimp [ε, pairErrorConstant]; positivity
  have hprob (i : AnnularMeshIndex N K h) : (gaussianCoefficientMeasure (N + 1)).real (E i) ≤ p :=
    retained_annular_jet_probability N hNp K h u v hK hKN hh hu hv hdegree i
  have hcov (i j : AnnularMeshIndex N K h) (hij : (i, j) ∉ D) :
      |(gaussianCoefficientMeasure (N + 1)).real (E i ∩ E j) -
        (gaussianCoefficientMeasure (N + 1)).real (E i) * (gaussianCoefficientMeasure (N + 1)).real (E j)| ≤ ε := by
    have hsep : ¬ (‖annularMeshAngle h i.2 - annularMeshAngle h j.2‖ ≤ 1 / Real.sqrt N ∨
        ‖annularMeshAngle h i.2 + annularMeshAngle h j.2‖ ≤ 1 / Real.sqrt N) := by
      intro hb
      exact hij (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
    exact retained_annular_jet_pair N hNp K h u v hK hKN hh hdegree i j
      (lt_of_not_ge (not_or.mp hsep).1).le (lt_of_not_ge (not_or.mp hsep).2).le
  have htail := measureReal_indicatorCount_ge_le E
    (measurableSet_retainedAnnularJetEvent N K h u v) D hp hε hQ hprob hcov hthreshold
  have hcard := derivative_mesh_close_pairs_le (K := K) hN hS hL
  have hbound : 4 * ((Fintype.card (AnnularMeshIndex N K h) : ℝ) ^ 2 * ε + (D.card : ℝ) * p) / Q ^ 2 ≤
      4 * (Fintype.card (AnnularMeshIndex N K h) : ℝ) ^ 2 *
        (pairErrorConstant K + 5 * p) / (Real.sqrt N * Q ^ 2) := by
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
      ((detectedAnnularMesh (gaussianPolynomial N ω) N K S L).card : ℝ) := by
    funext ω
    exact indicatorCount_retainedAnnularJetEvent_eq hNp K S L ω
  rw [heq] at htail
  exact htail.trans hbound

end GaussianAnnularJetCount
end Erdos522

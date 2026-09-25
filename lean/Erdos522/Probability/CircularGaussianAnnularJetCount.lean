/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianJetSmallBall
import Erdos522.Probability.SteinhausAnnularJetCount

/-!
# Circular Gaussian jets on annular meshes

Exact Gaussian small-ball bounds and separated-pair covariance comparison
control the deterministic mesh detections. Diagonal and angularly resonant
pairs are retained in the explicit variance budget.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace Erdos522
namespace CircularGaussianAnnularJetCount

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
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real (SteinhausAnnularJetCount.retainedAnnularJetEvent N K hmesh u v i) ≤
      pointProbabilityBound K u v := by
  by_cases hi : 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle hmesh i.2)
  · rw [SteinhausAnnularJetCount.retainedAnnularJetEvent_eq N K hmesh u v i hi, annularMeshPoint_eq_exp]
    have hr := annularMeshRadius_mem hN hK hh i.1
    exact circularGaussian_annular_polynomial_small_ball N hN K (annularMeshRadius N K hmesh i.1) (annularMeshRadians hmesh i.2)
      hK hKN hr.1 hr.2 hdegree (retained_annularMeshAngle_nondegenerate i.2 hi) u v hu hv
  · rw [SteinhausAnnularJetCount.retainedAnnularJetEvent_eq_empty N K hmesh u v i hi, measureReal_empty]
    unfold pointProbabilityBound
    positivity

/-- Separated retained mesh events factorize up to the eight-dimensional covariance error. -/
theorem retained_annular_jet_pair (N : ℕ) (hN : 0 < N) (K hmesh u v : ℝ)
    (hK : 0 ≤ K) (hKN : 2 * K ≤ N) (hh : 0 < hmesh)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (i j : AnnularMeshIndex N K hmesh)
    (hd : 1 / Real.sqrt N ≤ ‖annularMeshAngle hmesh i.2 - annularMeshAngle hmesh j.2‖)
    (hs : 1 / Real.sqrt N ≤ ‖annularMeshAngle hmesh i.2 + annularMeshAngle hmesh j.2‖) :
    |(Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
        (SteinhausAnnularJetCount.retainedAnnularJetEvent N K hmesh u v i ∩ SteinhausAnnularJetCount.retainedAnnularJetEvent N K hmesh u v j) -
      (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real (SteinhausAnnularJetCount.retainedAnnularJetEvent N K hmesh u v i) *
      (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real (SteinhausAnnularJetCount.retainedAnnularJetEvent N K hmesh u v j)| ≤
      pairErrorConstant K / Real.sqrt N := by
  have hpos : 0 ≤ pairErrorConstant K / Real.sqrt N := by unfold pairErrorConstant; positivity
  by_cases hi : 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle hmesh i.2)
  · by_cases hj : 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle hmesh j.2)
    · rw [SteinhausAnnularJetCount.retainedAnnularJetEvent_eq N K hmesh u v i hi,
        SteinhausAnnularJetCount.retainedAnnularJetEvent_eq N K hmesh u v j hj, annularMeshPoint_eq_exp, annularMeshPoint_eq_exp]
      have hri := annularMeshRadius_mem hN hK hh i.1
      have hrj := annularMeshRadius_mem hN hK hh j.1
      have hd' : 1 / Real.sqrt N ≤
          ‖((annularMeshRadians hmesh i.2 - annularMeshRadians hmesh j.2 : ℝ) : Real.Angle)‖ := by
        rwa [Real.Angle.coe_sub]
      have hs' : 1 / Real.sqrt N ≤
          ‖((annularMeshRadians hmesh i.2 + annularMeshRadians hmesh j.2 : ℝ) : Real.Angle)‖ := by
        rwa [Real.Angle.coe_add]
      exact circularGaussian_polynomial_small_ball_factorization N hN K (annularMeshRadius N K hmesh i.1) (annularMeshRadius N K hmesh j.1)
        (annularMeshRadians hmesh i.2) (annularMeshRadians hmesh j.2)
        hK hKN hri.1 hri.2 hrj.1 hrj.2 hdegree
        (retained_annularMeshAngle_nondegenerate i.2 hi) (retained_annularMeshAngle_nondegenerate j.2 hj)
        hd' hs' u v u v
    · rw [SteinhausAnnularJetCount.retainedAnnularJetEvent_eq_empty N K hmesh u v j hj]
      simpa using hpos
  · rw [SteinhausAnnularJetCount.retainedAnnularJetEvent_eq_empty N K hmesh u v i hi]
    simpa using hpos

/-- The derivative-mesh detections satisfy a quantitative tail estimate under the actual circular Gaussian law. -/
theorem annular_mesh_detection (N : ℕ) (hN : 2 ≤ N) (K S L Q : ℝ)
    (hK : 0 ≤ K) (hKN : 2 * K ≤ N) (hS : 1 ≤ S) (hL : 1 ≤ L)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ)) (hQ : 0 < Q)
    (hthreshold : (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) *
      pointProbabilityBound K (derivativeMeshValueThreshold N S L) (3 / L) ≤ Q / 2) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {ω | Q ≤
      (detectedAnnularMesh (Polynomial.ofFn (N + 1) ω) N K S L).card} ≤
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
  let E := SteinhausAnnularJetCount.retainedAnnularJetEvent N K h u v
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
  have hprob (i : AnnularMeshIndex N K h) : (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real (E i) ≤ p :=
    retained_annular_jet_probability N hNp K h u v hK hKN hh hu hv hdegree i
  have hcov (i j : AnnularMeshIndex N K h) (hij : (i, j) ∉ D) :
      |(Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real (E i ∩ E j) -
        (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real (E i) * (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real (E j)| ≤ ε := by
    have hsep : ¬ (‖annularMeshAngle h i.2 - annularMeshAngle h j.2‖ ≤ 1 / Real.sqrt N ∨
        ‖annularMeshAngle h i.2 + annularMeshAngle h j.2‖ ≤ 1 / Real.sqrt N) := by
      intro hb
      exact hij (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
    exact retained_annular_jet_pair N hNp K h u v hK hKN hh hdegree i j
      (lt_of_not_ge (not_or.mp hsep).1).le (lt_of_not_ge (not_or.mp hsep).2).le
  have htail := measureReal_indicatorCount_ge_le E
    (SteinhausAnnularJetCount.measurableSet_retainedAnnularJetEvent N K h u v) D hp hε hQ hprob hcov hthreshold
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
      ((detectedAnnularMesh (Polynomial.ofFn (N + 1) ω) N K S L).card : ℝ) := by
    funext ω
    exact SteinhausAnnularJetCount.indicatorCount_retainedAnnularJetEvent_eq hNp K S L ω
  rw [heq] at htail
  exact htail.trans hbound

end CircularGaussianAnnularJetCount
end Erdos522

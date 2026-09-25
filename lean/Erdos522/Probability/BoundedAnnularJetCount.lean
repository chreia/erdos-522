/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SteinhausAnnularJetCount
import Erdos522.Probability.GaussianApproximation.BoundedPairedSmallBall

/-!
# Annular mesh counts for bounded coefficient laws

The joint value-derivative estimates use only boundedness, zero mean and unit
second moment. Both finite Gaussian error coefficients equal the common
annular coefficients after the explicit substitution `C ↦ 8 C B³`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace Erdos522
namespace BoundedAnnularJetCount
open SteinhausAnnularJetCount

/-- The bounded jet constant has the common annular normalization. -/
theorem boundedJetGaussianErrorConstant_eq (C B K : ℝ) :
    boundedJetGaussianErrorConstant C B K = jetGaussianErrorConstant (8 * C * B ^ 3) K := by
  unfold boundedJetGaussianErrorConstant jetGaussianErrorConstant
  ring

/-- The same substitution normalizes the separated-pair approximation. -/
theorem boundedPairedJetGaussianErrorConstant_eq (C B K : ℝ) :
    boundedPairedJetGaussianErrorConstant C B K =
      pairedJetGaussianErrorConstant (8 * C * B ^ 3) K := by
  unfold boundedPairedJetGaussianErrorConstant pairedJetGaussianErrorConstant
  ring

variable (μ : Measure ℂ) [IsProbabilityMeasure μ] {B : ℝ}
    (hB : 0 < B) (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
    (hmean : (∫ z, z ∂μ) = 0) (hsecond : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)

include hB hbound hmean hsecond

/-- One-point small-ball bounds hold at every retained point of the actual annular mesh. -/
theorem exists_retained_annular_jet_probability_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K h u v : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : 0 < h) (_ : 0 ≤ u) (_ : 0 ≤ v)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (i : AnnularMeshIndex N K h),
      (Measure.pi (fun _ : Fin (N + 1) => μ)).real (SteinhausAnnularJetCount.retainedAnnularJetEvent N K h u v i) ≤
        annularJetProbabilityBound N C K u v := by
  obtain ⟨C, hC, h⟩ := exists_bounded_polynomial_jet_small_ball_constant
  refine ⟨8 * C * B ^ 3, by positivity, ?_⟩
  intro N hN K hmesh u v hK hKN hh hu hv hdegree i
  by_cases hi : 1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle hmesh i.2)
  · rw [SteinhausAnnularJetCount.retainedAnnularJetEvent_eq N K hmesh u v i hi, annularMeshPoint_eq_exp]
    have hr := annularMeshRadius_mem hN hK hh i.1
    have hb := h μ B hB.le hbound hmean hsecond N hN K (annularMeshRadius N K hmesh i.1) (annularMeshRadians hmesh i.2)
      hK hKN hr.1 hr.2 hdegree (retained_annularMeshAngle_nondegenerate i.2 hi) u v hu hv
    simpa only [annularJetProbabilityBound, boundedJetGaussianErrorConstant_eq] using hb
  · rw [SteinhausAnnularJetCount.retainedAnnularJetEvent_eq_empty N K hmesh u v i hi, measureReal_empty]
    unfold annularJetProbabilityBound
    have hG := jetGaussianErrorConstant_pos (8 * C * B ^ 3) K (by positivity)
    positivity

/-- Separated retained mesh events factorize up to the actual eight-dimensional error. -/
theorem exists_retained_annular_jet_pair_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K h u v : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : 0 < h)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (i j : AnnularMeshIndex N K h)
      (_ : 1 / Real.sqrt N ≤ ‖annularMeshAngle h i.2 - annularMeshAngle h j.2‖)
      (_ : 1 / Real.sqrt N ≤ ‖annularMeshAngle h i.2 + annularMeshAngle h j.2‖),
      |(Measure.pi (fun _ : Fin (N + 1) => μ)).real
          (SteinhausAnnularJetCount.retainedAnnularJetEvent N K h u v i ∩ SteinhausAnnularJetCount.retainedAnnularJetEvent N K h u v j) -
        (Measure.pi (fun _ : Fin (N + 1) => μ)).real (SteinhausAnnularJetCount.retainedAnnularJetEvent N K h u v i) *
          (Measure.pi (fun _ : Fin (N + 1) => μ)).real (SteinhausAnnularJetCount.retainedAnnularJetEvent N K h u v j)| ≤
        annularJetPairConstant C K / Real.sqrt N := by
  obtain ⟨C, hC, h⟩ := exists_bounded_polynomial_small_ball_factorization_constant
  refine ⟨8 * C * B ^ 3, by positivity, ?_⟩
  intro N hN K hmesh u v hK hKN hh hdegree i j hd hs
  have hpos : 0 ≤ annularJetPairConstant (8 * C * B ^ 3) K / Real.sqrt N := by
    exact div_nonneg (annularJetPairConstant_pos (8 * C * B ^ 3) K (by positivity)).le (Real.sqrt_nonneg _)
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
      have hb := h μ B hB.le hbound hmean hsecond N hN K (annularMeshRadius N K hmesh i.1) (annularMeshRadius N K hmesh j.1)
        (annularMeshRadians hmesh i.2) (annularMeshRadians hmesh j.2)
        hK hKN hri.1 hri.2 hrj.1 hrj.2 hdegree
        (retained_annularMeshAngle_nondegenerate i.2 hi) (retained_annularMeshAngle_nondegenerate j.2 hj)
        hd' hs' u v u v
      simpa only [annularJetPairConstant, boundedJetGaussianErrorConstant_eq,
        boundedPairedJetGaussianErrorConstant_eq] using hb
    · rw [SteinhausAnnularJetCount.retainedAnnularJetEvent_eq_empty N K hmesh u v j hj]
      simpa using hpos
  · rw [SteinhausAnnularJetCount.retainedAnnularJetEvent_eq_empty N K hmesh u v i hi]
    simpa using hpos

/-- The derivative-mesh detections satisfy a quantitative tail estimate under the actual bounded coefficient law. -/
theorem exists_annular_mesh_detection_constants :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (N : ℕ) (_ : 2 ≤ N) (K S L Q : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : 1 ≤ S) (_ : 1 ≤ L)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ)) (_ : 0 < Q)
      (_ : (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) *
        annularJetProbabilityBound N C₁ K (derivativeMeshValueThreshold N S L) (3 / L) ≤ Q / 2),
      (Measure.pi (fun _ : Fin (N + 1) => μ)).real {ω | Q ≤
        (detectedAnnularMesh (Polynomial.ofFn (N + 1) ω) N K S L).card} ≤
      4 * (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) ^ 2 *
        (annularJetPairConstant C₂ K +
          5 * annularJetProbabilityBound N C₁ K (derivativeMeshValueThreshold N S L) (3 / L)) /
        (Real.sqrt N * Q ^ 2) := by
  obtain ⟨C₁, hC₁, hpoint⟩ := exists_retained_annular_jet_probability_constant μ hB hbound hmean hsecond
  obtain ⟨C₂, hC₂, hpair⟩ := exists_retained_annular_jet_pair_constant μ hB hbound hmean hsecond
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro N hN K S L Q hK hKN hS hL hdegree hQ hthreshold
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hh := (derivativeMeshSpacing_le_inv_degree hN hS hL).1
  let h := derivativeMeshSpacing N S L
  let u := derivativeMeshValueThreshold N S L
  let v := 3 / L
  let E := SteinhausAnnularJetCount.retainedAnnularJetEvent N K h u v
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
  have hprob (i : AnnularMeshIndex N K h) : (Measure.pi (fun _ : Fin (N + 1) => μ)).real (E i) ≤ p :=
    hpoint N hNp K h u v hK hKN hh hu hv hdegree i
  have hcov (i j : AnnularMeshIndex N K h) (hij : (i, j) ∉ D) :
      |(Measure.pi (fun _ : Fin (N + 1) => μ)).real (E i ∩ E j) -
        (Measure.pi (fun _ : Fin (N + 1) => μ)).real (E i) * (Measure.pi (fun _ : Fin (N + 1) => μ)).real (E j)| ≤ ε := by
    have hsep : ¬ (‖annularMeshAngle h i.2 - annularMeshAngle h j.2‖ ≤ 1 / Real.sqrt N ∨
        ‖annularMeshAngle h i.2 + annularMeshAngle h j.2‖ ≤ 1 / Real.sqrt N) := by
      intro hb
      exact hij (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
    exact hpair N hNp K h u v hK hKN hh hdegree i j
      (lt_of_not_ge (not_or.mp hsep).1).le (lt_of_not_ge (not_or.mp hsep).2).le
  have htail := measureReal_indicatorCount_ge_le E
    (SteinhausAnnularJetCount.measurableSet_retainedAnnularJetEvent N K h u v) D hp hε hQ hprob hcov hthreshold
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
    exact SteinhausAnnularJetCount.indicatorCount_retainedAnnularJetEvent_eq hNp K S L ω
  rw [heq] at htail
  exact htail.trans hbound

end BoundedAnnularJetCount
end Erdos522

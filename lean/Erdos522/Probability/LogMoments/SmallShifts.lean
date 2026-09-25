/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.RademacherLogMoments
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linear combinations of small Fourier shifts

An excess of vectors over the dimension of a subspace gives a normalized
linear combination perpendicular to that subspace. Applied to translated
Fourier coefficients, this is the finite-dimensional step in the small-shift
method for logarithmic integrability.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos522.LogMoments

/-- A linearly dependent finite family has a relation with unit coefficient energy. -/
theorem exists_normalized_relation {E : Type*} [AddCommGroup E] [Module ℂ E]
    {n : ℕ} (v : Fin (n + 1) → E) (hv : ¬ LinearIndependent ℂ v) :
    ∃ a : Fin (n + 1) → ℂ, (∑ k, ‖a k‖ ^ 2) = 1 ∧ ∑ k, a k • v k = 0 := by
  obtain ⟨b, hb, hb0⟩ := Fintype.not_linearIndependent_iff.mp hv
  refine ⟨normalizedCoefficients b, sum_sq_norm_normalizedCoefficients b hb0, ?_⟩
  have hfactor : ∑ k, normalizedCoefficients b k • v k =
      (Real.sqrt (∑ j, ‖b j‖ ^ 2) : ℂ)⁻¹ • ∑ k, b k • v k := by
    simp only [normalizedCoefficients, div_eq_mul_inv, Finset.smul_sum, ← mul_smul]
    congr 1
    funext k
    rw [mul_comm]
  rw [hfactor, hb, smul_zero]

/-- More vectors than the dimension of a subspace admit a unit relation modulo its orthogonal. -/
theorem exists_normalized_sum_mem_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (V : Submodule ℂ E) [FiniteDimensional ℂ V]
    {n : ℕ} (hV : Module.finrank ℂ V ≤ n) (v : Fin (n + 1) → E) :
    ∃ a : Fin (n + 1) → ℂ, (∑ k, ‖a k‖ ^ 2) = 1 ∧ ∑ k, a k • v k ∈ Vᗮ := by
  have hdep : ¬ LinearIndependent ℂ (fun k => V.orthogonalProjectionOnto (v k)) := by
    intro hind
    have hc := hind.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨a, ha, hz⟩ := exists_normalized_relation _ hdep
  refine ⟨a, ha, V.orthogonalProjectionOnto_eq_zero_iff.mp ?_⟩
  simpa only [map_sum, map_smul] using hz

/-- Multiplying the coefficients by characters represents angular translation. -/
def translatedCoefficients {N : ℕ} (a : Fin (N + 1) → ℂ)
    (t : AddCircle (1 : ℝ)) (k : Fin (N + 1)) : ℂ :=
  a k * fourier k.val t

theorem fourierPolynomial_translatedCoefficients {N : ℕ}
    (a : Fin (N + 1) → ℂ) (t θ : AddCircle (1 : ℝ)) (ω : SignVector N) :
    fourierPolynomial (translatedCoefficients a t) ω θ = fourierPolynomial a ω (θ + t) := by
  simp only [fourierPolynomial_eq_sum, translatedCoefficients, fourier_apply,
    zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem sum_sq_norm_translatedCoefficients {N : ℕ}
    (a : Fin (N + 1) → ℂ) (t : AddCircle (1 : ℝ)) :
    (∑ k, ‖translatedCoefficients a t k‖ ^ 2) = ∑ k, ‖a k‖ ^ 2 := by
  simp [translatedCoefficients, fourier_apply]

/-- A unit coefficient vector bounds the energy of a finite linear combination pointwise. -/
theorem norm_sum_mul_sq_le {ι : Type*} [Fintype ι] (a z : ι → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) :
    ‖∑ k, a k * z k‖ ^ 2 ≤ ∑ k, ‖z k‖ ^ 2 := by
  classical
  calc
    ‖∑ k, a k * z k‖ ^ 2 ≤ (∑ k, ‖a k‖ * ‖z k‖) ^ 2 := by
      gcongr
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun k => a k * z k)
    _ ≤ (∑ k, ‖a k‖ ^ 2) * ∑ k, ‖z k‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = ∑ k, ‖z k‖ ^ 2 := by rw [ha, one_mul]

/-- Fourier synthesis commutes with finite linear combinations of coefficient vectors. -/
theorem randomFourier_sum_mul {N : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (a : ι → Fin (N + 1) → ℂ)
    (q : SignVector N × AddCircle (1 : ℝ)) :
    randomFourier (fun k => ∑ j, c j * a j k) q = ∑ j, c j * randomFourier (a j) q := by
  classical
  simp only [randomFourier, fourierPolynomial_eq_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Restriction does not increase the energy bound for a unit linear combination. -/
theorem restricted_energy_sum_mul_le {N : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (a : ι → Fin (N + 1) → ℂ) (E : Set (SignVector N × AddCircle (1 : ℝ)))
    (hc : ∑ j, ‖c j‖ ^ 2 = 1) :
    (∫ q in E, ‖randomFourier (fun k => ∑ j, c j * a j k) q‖ ^ 2 ∂fourierMeasure N) ≤
      ∑ j, ∫ q in E, ‖randomFourier (a j) q‖ ^ 2 ∂fourierMeasure N := by
  classical
  have hi (j : ι) : IntegrableOn (fun q => ‖randomFourier (a j) q‖ ^ 2) E (fourierMeasure N) :=
    (integrable_norm_sq_randomFourier (a j)).integrableOn
  calc
    _ ≤ ∫ q in E, ∑ j, ‖randomFourier (a j) q‖ ^ 2 ∂fourierMeasure N := by
      apply integral_mono (integrable_norm_sq_randomFourier _).integrableOn
        (integrable_finsetSum _ (fun j _ => hi j))
      intro q
      change ‖randomFourier (fun k => ∑ j, c j * a j k) q‖ ^ 2 ≤
        ∑ j, ‖randomFourier (a j) q‖ ^ 2
      rw [randomFourier_sum_mul]
      exact norm_sum_mul_sq_le c (fun j => randomFourier (a j) q) hc
    _ = _ := integral_finsetSum _ (fun j _ => hi j)

/-- A spectral lower bound on a finite-codimensional subspace yields a small unit combination.
The loss is exactly the number of vectors divided by the coercivity constant. -/
theorem exists_fourier_combination_energy_le
    {N n : ℕ} (a : Fin (n + 1) → EuclideanSpace ℂ (Fin (N + 1)))
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin (N + 1))))
    (hV : Module.finrank ℂ V ≤ n)
    (E : Set (SignVector N × AddCircle (1 : ℝ))) {c₀ B : ℝ} (hc₀ : 0 < c₀)
    (hcoercive : ∀ b : EuclideanSpace ℂ (Fin (N + 1)), b ∈ Vᗮ →
      c₀ * ∑ k, ‖b k‖ ^ 2 ≤ ∫ q in E, ‖randomFourier b q‖ ^ 2 ∂fourierMeasure N)
    (hsmall : ∀ j, (∫ q in E, ‖randomFourier (a j) q‖ ^ 2 ∂fourierMeasure N) ≤ B) :
    ∃ c : Fin (n + 1) → ℂ, (∑ j, ‖c j‖ ^ 2) = 1 ∧
      (∫ q, ‖∑ j, c j * randomFourier (a j) q‖ ^ 2 ∂fourierMeasure N) ≤
        ((n : ℝ) + 1) * B / c₀ := by
  classical
  obtain ⟨c, hc, hv⟩ := exists_normalized_sum_mem_orthogonal V hV a
  let b : EuclideanSpace ℂ (Fin (N + 1)) := ∑ j, c j • a j
  have hb : ∀ k, b k = ∑ j, c j * a j k := by
    intro k
    simp [b]
  have hcomb (q : SignVector N × AddCircle (1 : ℝ)) :
      (∑ j, c j * randomFourier (a j) q) = randomFourier b q := by
    rw [← randomFourier_sum_mul]
    congr 1
    funext k
    exact (hb k).symm
  refine ⟨c, hc, ?_⟩
  simp_rw [hcomb]
  rw [integral_norm_sq_randomFourier]
  apply (le_div_iff₀ hc₀).mpr
  calc
    (∑ k, ‖b k‖ ^ 2) * c₀ = c₀ * ∑ k, ‖b k‖ ^ 2 := mul_comm _ _
    _ ≤ ∫ q in E, ‖randomFourier b q‖ ^ 2 ∂fourierMeasure N := hcoercive b hv
    _ ≤ ∑ j, ∫ q in E, ‖randomFourier (a j) q‖ ^ 2 ∂fourierMeasure N := by
      have hbf : b.ofLp = (fun k => ∑ j, c j * a j k) := funext hb
      rw [hbf]
      exact restricted_energy_sum_mul_le c (fun j k => a j k) E hc
    _ ≤ ∑ _j : Fin (n + 1), B := Finset.sum_le_sum (fun j _ => hsmall j)
    _ = ((n : ℝ) + 1) * B := by simp

/-- Translation of the angular coordinate, preserving the signs. -/
def angularTranslation (N : ℕ) (t : AddCircle (1 : ℝ)) :
    (SignVector N × AddCircle (1 : ℝ)) ≃ᵐ (SignVector N × AddCircle (1 : ℝ)) :=
  (MeasurableEquiv.refl (SignVector N)).prodCongr (MeasurableEquiv.addRight t)

@[simp] theorem angularTranslation_apply (N : ℕ) (t : AddCircle (1 : ℝ))
    (q : SignVector N × AddCircle (1 : ℝ)) :
    angularTranslation N t q = (q.1, q.2 + t) := rfl

/-- Angular translations preserve the joint sign and angular law. -/
theorem measurePreserving_angularTranslation (N : ℕ) (t : AddCircle (1 : ℝ)) :
    MeasurePreserving (angularTranslation N t) (fourierMeasure N) (fourierMeasure N) := by
  exact (MeasurePreserving.id (signMeasure N)).prod
    (measurePreserving_add_right AddCircle.haarAddCircle t)

/-- Translating both the coefficients and the integration set leaves restricted energy unchanged. -/
theorem restricted_energy_translatedCoefficients {N : ℕ} (a : Fin (N + 1) → ℂ)
    (t : AddCircle (1 : ℝ)) (E : Set (SignVector N × AddCircle (1 : ℝ))) :
    (∫ q in angularTranslation N t ⁻¹' E,
      ‖randomFourier (translatedCoefficients a t) q‖ ^ 2 ∂fourierMeasure N) =
      ∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N := by
  simpa only [randomFourier, fourierPolynomial_translatedCoefficients,
    angularTranslation_apply] using
    (measurePreserving_angularTranslation N t).setIntegral_preimage_emb
      (angularTranslation N t).measurableEmbedding (fun q => ‖randomFourier a q‖ ^ 2) E

/-- Points whose first `n + 1` angular shifts belong to a given set. -/
def shiftIntersection {N : ℕ} (E : Set (SignVector N × AddCircle (1 : ℝ)))
    (n : ℕ) (t : AddCircle (1 : ℝ)) : Set (SignVector N × AddCircle (1 : ℝ)) :=
  ⋂ j : Fin (n + 1), angularTranslation N (j.val • t) ⁻¹' E

/-- Every shifted Fourier sum has restricted energy on the intersection bounded by
    the original energy on the initial set. -/
theorem restricted_energy_shiftIntersection_le {N n : ℕ}
    (a : Fin (N + 1) → ℂ) (E : Set (SignVector N × AddCircle (1 : ℝ)))
    (t : AddCircle (1 : ℝ)) (j : Fin (n + 1)) :
    (∫ q in shiftIntersection E n t,
      ‖randomFourier (translatedCoefficients a (j.val • t)) q‖ ^ 2 ∂fourierMeasure N) ≤
      ∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N := by
  rw [← restricted_energy_translatedCoefficients a (j.val • t) E]
  apply setIntegral_mono_set (integrable_norm_sq_randomFourier _).integrableOn
    (ae_of_all _ (fun _ => sq_nonneg _))
  exact ae_of_all _ (fun q hq => Set.mem_iInter.mp hq j)

/-- A finite-codimensional restricted-energy bound produces a normalized small-shift relation.
    The coefficient `4 (n + 1) / δ` is the exact finite-dimensional loss. -/
theorem exists_small_shift_energy_le {N n : ℕ} (a : Fin (N + 1) → ℂ)
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (t : AddCircle (1 : ℝ))
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin (N + 1))))
    (hV : Module.finrank ℂ V ≤ n) {δ : ℝ} (hδ : 0 < δ)
    (hcoercive : ∀ b : EuclideanSpace ℂ (Fin (N + 1)), b ∈ Vᗮ →
      (δ / 4) * ∑ k, ‖b k‖ ^ 2 ≤
        ∫ q in shiftIntersection E n t, ‖randomFourier b q‖ ^ 2 ∂fourierMeasure N) :
    ∃ c : Fin (n + 1) → ℂ, (∑ j, ‖c j‖ ^ 2) = 1 ∧
      (∫ q, ‖∑ j, c j * randomFourier a (angularTranslation N (j.val • t) q)‖ ^ 2
        ∂fourierMeasure N) ≤
        (4 * ((n : ℝ) + 1) / δ) *
          ∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N := by
  let v (j : Fin (n + 1)) : EuclideanSpace ℂ (Fin (N + 1)) :=
    WithLp.toLp 2 (translatedCoefficients a (j.val • t))
  obtain ⟨c, hc, hbound⟩ := exists_fourier_combination_energy_le v V hV
    (shiftIntersection E n t) (by positivity : 0 < δ / 4) hcoercive
    (fun j => restricted_energy_shiftIntersection_le a E t j)
  refine ⟨c, hc, ?_⟩
  have hv (j : Fin (n + 1)) (q : SignVector N × AddCircle (1 : ℝ)) :
      randomFourier (v j) q = randomFourier a (angularTranslation N (j.val • t) q) :=
    fourierPolynomial_translatedCoefficients a (j.val • t) q.2 q.1
  simp_rw [hv] at hbound
  convert hbound using 1
  ring

end Erdos522.LogMoments

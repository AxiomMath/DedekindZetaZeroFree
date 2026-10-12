module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree
namespace KPContCotangentRealOrthogonalComplexification

open scoped BigOperators

variable (I : Type*) [Fintype I] [DecidableEq I]

 lemma operatorComplexification_aux_add
    (A B : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) :
    (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
        (Matrix.of fun i j => ((((A + B) (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ)) :
      EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) =
    (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
        (Matrix.of fun i j => (((A (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ)) :
      EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) +
    (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
        (Matrix.of fun i j => (((B (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ)) :
      EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) := by
  have hM : (Matrix.of fun i j => ((((A + B) (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ))
      = Matrix.of (fun i j => (((A (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ))
        + Matrix.of (fun i j => (((B (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ)) := by
    ext i j
    simp [ContinuousLinearMap.add_apply]
  rw [hM, map_add]

 lemma operatorComplexification_aux_smul
    (c : ℝ) (A : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) :
    (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
        (Matrix.of fun i j => ((((c • A) (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ)) :
      EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) =
    c • (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
        (Matrix.of fun i j => (((A (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ)) :
      EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) := by
  have hM : (Matrix.of fun i j => ((((c • A) (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ))
      = (c : ℂ) • Matrix.of (fun i j => (((A (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ)) := by
    ext i j
    simp [ContinuousLinearMap.smul_apply, Complex.ofReal_mul]
  rw [hM, map_smul]
  ext v i
  simp [ContinuousLinearMap.smul_apply, RCLike.real_smul_eq_coe_smul]

def operatorComplexification :
    (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) →L[ℝ]
      (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) where
  toFun A := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
    (fun i j => (((A (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ))
  map_add' := operatorComplexification_aux_add I
  map_smul' := operatorComplexification_aux_smul I
  cont := by
    let f : (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) →ₗ[ℝ]
        (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :=
      { toFun := fun A => Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
          (fun i j => (((A (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ))
        map_add' := operatorComplexification_aux_add I
        map_smul' := operatorComplexification_aux_smul I }
    exact f.continuous_of_finiteDimensional

theorem operatorComplexification_apply
    (A : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (v : EuclideanSpace ℂ I) (i : I) :
    operatorComplexification I A v i =
      ∑ j, (((A (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ) * v j := by
  rw [show operatorComplexification I A = Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
      (Matrix.of fun i j => (((A (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ)) from rfl]
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [Matrix.mulVec, dotProduct]

@[simp] theorem operatorComplexification_id :
    operatorComplexification I (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ I)) =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ I) := by
  ext v i
  rw [operatorComplexification_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem operatorComplexification_comp
    (A B : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) :
    operatorComplexification I (B.comp A) =
      (operatorComplexification I B).comp (operatorComplexification I A) := by
  rw [show operatorComplexification I (B.comp A) = Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
      (Matrix.of fun i j => ((((B.comp A) (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ)) from rfl]
  rw [show operatorComplexification I B = Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
      (Matrix.of fun i j => (((B (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ)) from rfl]
  rw [show operatorComplexification I A = Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
      (Matrix.of fun i j => (((A (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ)) from rfl]
  have h1 : ∀ j, (∑ k, (A (EuclideanSpace.basisFun I ℝ j)) k • EuclideanSpace.basisFun I ℝ k)
      = A (EuclideanSpace.basisFun I ℝ j) := by
    intro j
    conv_rhs => rw [← OrthonormalBasis.sum_repr (EuclideanSpace.basisFun I ℝ)
      (A (EuclideanSpace.basisFun I ℝ j))]
    simp only [EuclideanSpace.basisFun_repr]
  have hcoord : ∀ j, B (A (EuclideanSpace.basisFun I ℝ j)) =
      ∑ k, (A (EuclideanSpace.basisFun I ℝ j)) k • B (EuclideanSpace.basisFun I ℝ k) := by
    intro j
    conv_lhs => rw [← h1 j]
    simp only [map_sum, ContinuousLinearMap.map_smul]
  have hM : (Matrix.of fun i j => ((((B.comp A) (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ))
      = Matrix.of (fun i j => (((B (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ))
        * Matrix.of (fun i j => (((A (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ)) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [ContinuousLinearMap.comp_apply, hcoord j]
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [Finset.sum_congr rfl (fun k _ => mul_comm _ _)]
  rw [hM, map_mul]
  ext v
  simp [ContinuousLinearMap.mul_apply]

private lemma conjTranspose_mul_self_orthogonalMatrix
    (q : EuclideanSpace ℝ I ≃ₗᵢ[ℝ] EuclideanSpace ℝ I) :
    Matrix.conjTranspose (Matrix.of fun i j => (((q (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ)) *
      (Matrix.of fun i j => (((q (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ)) = 1 := by
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def,
    Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  have hsum : (∑ i, (q (EuclideanSpace.basisFun I ℝ j)) i *
      (q (EuclideanSpace.basisFun I ℝ k)) i : ℝ) = if j = k then 1 else 0 := by
    rw [show (∑ i, (q (EuclideanSpace.basisFun I ℝ j)) i *
        (q (EuclideanSpace.basisFun I ℝ k)) i : ℝ) =
        inner ℝ (q (EuclideanSpace.basisFun I ℝ j)) (q (EuclideanSpace.basisFun I ℝ k)) from by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
      simp only [star_trivial]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
    rw [q.inner_map_map]
    exact (orthonormal_iff_ite.mp (EuclideanSpace.basisFun I ℝ).orthonormal) j k
  rw [hsum]
  by_cases h : j = k <;> simp [h]

private lemma star_mul_self_operatorComplexification_orthogonal
    (q : EuclideanSpace ℝ I ≃ₗᵢ[ℝ] EuclideanSpace ℝ I) :
    star (operatorComplexification I q.toContinuousLinearEquiv.toContinuousLinearMap) *
      operatorComplexification I q.toContinuousLinearEquiv.toContinuousLinearMap = 1 := by
  rw [show operatorComplexification I q.toContinuousLinearEquiv.toContinuousLinearMap =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
        (Matrix.of fun i j => (((q (EuclideanSpace.basisFun I ℝ j)) i : ℝ) : ℂ)) from rfl]
  rw [← map_star, Matrix.star_eq_conjTranspose, ← map_mul,
    conjTranspose_mul_self_orthogonalMatrix I q, map_one]

 lemma inner_operatorComplexification_orthogonal
    (q : EuclideanSpace ℝ I ≃ₗᵢ[ℝ] EuclideanSpace ℝ I) (v w : EuclideanSpace ℂ I) :
    inner ℂ (operatorComplexification I q.toContinuousLinearEquiv.toContinuousLinearMap v)
      (operatorComplexification I q.toContinuousLinearEquiv.toContinuousLinearMap w) =
      inner ℂ v w := by
  have hKK := star_mul_self_operatorComplexification_orthogonal I q
  rw [← ContinuousLinearMap.adjoint_inner_right]
  show inner ℂ v (star (operatorComplexification I q.toContinuousLinearEquiv.toContinuousLinearMap)
      (operatorComplexification I q.toContinuousLinearEquiv.toContinuousLinearMap w)) = inner ℂ v w
  rw [← mul_apply_eq_comp, hKK, one_apply_eq_self]

def orthogonalComplexification
    (q : EuclideanSpace ℝ I ≃ₗᵢ[ℝ] EuclideanSpace ℝ I) :
    EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ I where
  toLinearEquiv :=
    { toLinearMap :=
        (operatorComplexification I
          q.toContinuousLinearEquiv.toContinuousLinearMap).toLinearMap
      invFun := operatorComplexification I
        q.symm.toContinuousLinearEquiv.toContinuousLinearMap
      left_inv := by
        intro v
        have hcomp : (q.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
            q.toContinuousLinearEquiv.toContinuousLinearMap =
            ContinuousLinearMap.id ℝ (EuclideanSpace ℝ I) := by
          ext w
          simp
        have h := congrArg (fun f : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I => f v)
          (operatorComplexification_comp I q.toContinuousLinearEquiv.toContinuousLinearMap
            q.symm.toContinuousLinearEquiv.toContinuousLinearMap)
        rw [hcomp, operatorComplexification_id, ContinuousLinearMap.id_apply] at h
        exact h.symm
      right_inv := by
        intro v
        have hcomp : (q.toContinuousLinearEquiv.toContinuousLinearMap).comp
            q.symm.toContinuousLinearEquiv.toContinuousLinearMap =
            ContinuousLinearMap.id ℝ (EuclideanSpace ℝ I) := by
          ext w
          simp
        have h := congrArg (fun f : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I => f v)
          (operatorComplexification_comp I q.symm.toContinuousLinearEquiv.toContinuousLinearMap
            q.toContinuousLinearEquiv.toContinuousLinearMap)
        rw [hcomp, operatorComplexification_id, ContinuousLinearMap.id_apply] at h
        exact h.symm }
  norm_map' := by
    intro v
    show ‖(operatorComplexification I q.toContinuousLinearEquiv.toContinuousLinearMap) v‖ = ‖v‖
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_operatorComplexification_orthogonal I q v v,
      ← norm_eq_sqrt_re_inner (𝕜 := ℂ)]

theorem orthogonalComplexification_toContinuousLinearMap
    (q : EuclideanSpace ℝ I ≃ₗᵢ[ℝ] EuclideanSpace ℝ I) :
    (orthogonalComplexification I q).toContinuousLinearEquiv.toContinuousLinearMap =
      operatorComplexification I q.toContinuousLinearEquiv.toContinuousLinearMap := by
  ext v
  rfl

@[simp] theorem orthogonalComplexification_refl :
    orthogonalComplexification I (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ I)) =
      LinearIsometryEquiv.refl ℂ (EuclideanSpace ℂ I) := by
  apply LinearIsometryEquiv.ext
  intro v
  change operatorComplexification I (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ I)) v = v
  rw [operatorComplexification_id]
  rfl

@[simp] theorem orthogonalComplexification_symm
    (q : EuclideanSpace ℝ I ≃ₗᵢ[ℝ] EuclideanSpace ℝ I) :
    orthogonalComplexification I q.symm = (orthogonalComplexification I q).symm := by
  ext v
  rfl

theorem contDiffOn_operatorComplexification
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {D : Set X} (hD : IsOpen D)
    {A : X → (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A D) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => operatorComplexification I (A x)) D := by
  exact hA.continuousLinearMap_comp (operatorComplexification I)

end KPContCotangentRealOrthogonalComplexification
end DedekindZetaZeroFree

end

module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

noncomputable section
open scoped Classical FourierTransform SchwartzMap
open MeasureTheory NumberField

namespace DedekindZetaZeroFree
namespace PoissonArch

variable (F : Type) [Field F] [NumberField F]

abbrev Space := NumberField.mixedEmbedding.euclidean.mixedSpace F

def tracePairing (x y : Space F) : ℝ :=
  let x' := NumberField.mixedEmbedding.euclidean.toMixed F x
  let y' := NumberField.mixedEmbedding.euclidean.toMixed F y
  (∑ v, x'.1 v * y'.1 v) + 2 * ∑ v, (x'.2 v * y'.2 v).re

def traceAdapter : Space F ≃L[ℝ] Space F :=
  (NumberField.mixedEmbedding.euclidean.toMixed F).trans
    ((ContinuousLinearEquiv.refl ℝ _).prodCongr
      (ContinuousLinearEquiv.piCongrRight fun _ =>
        Units.mk0 (2 : ℝ) (by norm_num) • Complex.conjCLE)) |>.trans
    (NumberField.mixedEmbedding.euclidean.toMixed F).symm

def haarScalar : ℝ := (2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces F

def traceMeasure : Measure (Space F) := ENNReal.ofReal (haarScalar F) • volume

def traceFourier (f : Space F → ℂ) (y : Space F) : ℂ :=
  ∫ x, f x * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (tracePairing F x y : ℂ))
    ∂traceMeasure F

def fieldMul (a : F) (x : Space F) : Space F :=
  (NumberField.mixedEmbedding.euclidean.toMixed F).symm
    (NumberField.mixedEmbedding F a * NumberField.mixedEmbedding.euclidean.toMixed F x)

def fieldModule (a : F) : ℝ :=
  (∏ v : {v : NumberField.InfinitePlace F // v.IsReal},
    |(NumberField.mixedEmbedding F a).1 v|) *
  ∏ v : {v : NumberField.InfinitePlace F // v.IsComplex},
    Complex.normSq ((NumberField.mixedEmbedding F a).2 v)

theorem traceAdapter_coordinates (y : Space F) :
    (NumberField.mixedEmbedding.euclidean.toMixed F (traceAdapter F y)).1 =
      (NumberField.mixedEmbedding.euclidean.toMixed F y).1 ∧
    (NumberField.mixedEmbedding.euclidean.toMixed F (traceAdapter F y)).2 =
      fun v => (2 : ℝ) • star ((NumberField.mixedEmbedding.euclidean.toMixed F y).2 v) := by
  simp [traceAdapter, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply]
  ext v
  simp [ContinuousLinearEquiv.piCongrRight_apply, ContinuousLinearEquiv.smul_apply]

theorem tracePairing_eq_inner (x y : Space F) :
    tracePairing F x y = inner ℝ x (traceAdapter F y) := by
  have h₁ := (traceAdapter_coordinates F y).1
  have h₂ := (traceAdapter_coordinates F y).2
  simp only [WithLp.prod_inner_apply, PiLp.inner_apply, Real.inner_apply]
  change tracePairing F x y =
    (∑ v, (NumberField.mixedEmbedding.euclidean.toMixed F x).1 v *
      (NumberField.mixedEmbedding.euclidean.toMixed F (traceAdapter F y)).1 v) +
    ∑ v, inner ℝ ((NumberField.mixedEmbedding.euclidean.toMixed F x).2 v)
      ((NumberField.mixedEmbedding.euclidean.toMixed F (traceAdapter F y)).2 v)
  simp only [tracePairing, h₁, h₂, inner_smul_right, Complex.inner,
    RCLike.inner_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.star_def, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem haarScalar_pos : 0 < haarScalar F := by
  exact pow_pos (by norm_num) _

theorem traceFourier_eq_euclidean (f : 𝓢(Space F, ℂ)) (y : Space F) :
    traceFourier F f y = (haarScalar F : ℂ) * (𝓕 f) (traceAdapter F y) := by
  rw [traceFourier, traceMeasure, integral_smul_measure, ENNReal.toReal_ofReal
    (le_of_lt (haarScalar_pos F))]
  change (haarScalar F : ℂ) * _ = _
  congr 1
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  simp only [Circle.smul_def, Real.fourierChar_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [tracePairing_eq_inner]
  simp only [innerₗ_apply_apply, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_ofNat, smul_eq_mul]
  rw [mul_comm (f x)]
  congr 2 <;> ring

theorem traceFourier_schwartz (f : 𝓢(Space F, ℂ)) :
    ∃ g : 𝓢(Space F, ℂ), ∀ y, g y = traceFourier F f y := by
  refine ⟨(haarScalar F : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (traceAdapter F) (𝓕 f), ?_⟩
  intro y
  simpa using (traceFourier_eq_euclidean F f y).symm

private theorem integral_comp_equiv (A : Space F ≃L[ℝ] Space F)
    (g : Space F → ℂ) :
    (∫ x, g (A x)) = |(LinearMap.det A.toLinearMap)⁻¹| • ∫ x, g x := by
  have hdet : LinearMap.det A.toLinearMap ≠ 0 :=
    (A.toLinearEquiv.isUnit_det').ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Space F)) hdet
  have hi := integral_map_equiv (μ := (volume : Measure (Space F))) A.toHomeomorph.toMeasurableEquiv g
  rw [show Measure.map A.toHomeomorph.toMeasurableEquiv volume =
    Measure.map A.toLinearMap volume from rfl, hmap,
    integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at hi
  exact hi.symm

def fieldEquiv (a : Fˣ) : Space F ≃L[ℝ] Space F :=
  ((NumberField.mixedEmbedding.euclidean.toMixed F).trans
    ((ContinuousLinearEquiv.piCongrRight fun v : {v : NumberField.InfinitePlace F // v.IsReal} =>
      ContinuousLinearEquiv.unitsEquivAut ℝ (a.map (v.val.embedding_of_isReal v.prop))).prodCongr
      (ContinuousLinearEquiv.piCongrRight fun v : {v : NumberField.InfinitePlace F // v.IsComplex} =>
        (ContinuousLinearEquiv.unitsEquivAut ℂ (a.map v.val.embedding)).restrictScalars ℝ))).trans
    (NumberField.mixedEmbedding.euclidean.toMixed F).symm

private theorem fieldEquiv_apply (a : Fˣ) (x : Space F) :
    fieldEquiv F a x = fieldMul F (a : F) x := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed F).injective
  simp only [fieldEquiv, fieldMul, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.prodCongr_apply]
  ext v <;> simp [ContinuousLinearEquiv.piCongrRight_apply,
    ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm]

private theorem complex_mul_det (z : ℂ) :
    LinearMap.det ((LinearMap.mulLeft ℂ z).restrictScalars ℝ) = Complex.normSq z := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI,
    Matrix.det_fin_two, Complex.normSq_apply, LinearMap.restrictScalars_apply,
    LinearMap.mulLeft_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  ring

private theorem fieldEquiv_abs_det (a : Fˣ) :
    |LinearMap.det (fieldEquiv F a).toLinearMap| = fieldModule F (a : F) := by
  let R : {v : NumberField.InfinitePlace F // v.IsReal} → ℝ →ₗ[ℝ] ℝ :=
    fun v => LinearMap.mulLeft ℝ ((NumberField.mixedEmbedding F (a : F)).1 v)
  let C : {v : NumberField.InfinitePlace F // v.IsComplex} → ℂ →ₗ[ℝ] ℂ :=
    fun v => (LinearMap.mulLeft ℂ ((NumberField.mixedEmbedding F (a : F)).2 v)).restrictScalars ℝ
  have he : (fieldEquiv F a).toLinearMap =
    (NumberField.mixedEmbedding.euclidean.toMixed F).symm.toLinearMap.comp
      (((LinearMap.pi fun v => (R v).comp (LinearMap.proj v)).prodMap
        (LinearMap.pi fun v => (C v).comp (LinearMap.proj v))).comp
          (NumberField.mixedEmbedding.euclidean.toMixed F).toLinearMap) := by
    ext x
    apply (NumberField.mixedEmbedding.euclidean.toMixed F).injective
    change (NumberField.mixedEmbedding.euclidean.toMixed F) (fieldEquiv F a x) = _
    rw [fieldEquiv_apply]
    simp only [fieldMul, LinearMap.prodMap_apply, ContinuousLinearEquiv.coe_coe,
      LinearMap.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    ext v <;> simp [R, C, mul_comm]
  rw [he, ContinuousLinearEquiv.toLinearEquiv_symm]
  have hd := LinearMap.det_conj
    ((LinearMap.pi fun v => (R v).comp (LinearMap.proj v)).prodMap
      (LinearMap.pi fun v => (C v).comp (LinearMap.proj v)))
    (NumberField.mixedEmbedding.euclidean.toMixed F).toLinearEquiv.symm
  simp only [LinearEquiv.symm_symm] at hd
  rw [hd, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi, abs_mul]
  simp only [R, C, LinearMap.det_mulLeft, complex_mul_det, Finset.abs_prod,
    abs_of_nonneg (Finset.prod_nonneg fun v _ => Complex.normSq_nonneg _), fieldModule]

private theorem fieldPairing_scale (a : Fˣ) (x y : Space F) :
    tracePairing F (fieldEquiv F a x) (fieldMul F ((a⁻¹ : Fˣ) : F) y) =
      tracePairing F x y := by
  have hh : NumberField.mixedEmbedding F (a : F) *
      NumberField.mixedEmbedding F ((a⁻¹ : Fˣ) : F) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  simp only [fieldEquiv_apply, tracePairing, fieldMul,
    ContinuousLinearEquiv.apply_symm_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro v hv
    have h := congrArg (fun z => z.1 v) hh
    simp only [Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply] at h ⊢
    rw [mul_mul_mul_comm, h, one_mul]
  · congr 1
    apply Finset.sum_congr rfl
    intro v hv
    have h := congrArg (fun z => z.2 v) hh
    simp only [Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply] at h ⊢
    rw [mul_mul_mul_comm, h, one_mul]

theorem traceFourier_field_scale (f : 𝓢(Space F, ℂ)) (a : Fˣ) (y : Space F) :
    traceFourier F (fun x => f (fieldMul F (a : F) x)) y =
      ((fieldModule F (a : F))⁻¹ : ℂ) *
        traceFourier F f (fieldMul F ((a⁻¹ : Fˣ) : F) y) := by
  have h := integral_comp_equiv F (fieldEquiv F a)
    (fun x => f x * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
      (tracePairing F x (fieldMul F ((a⁻¹ : Fˣ) : F) y) : ℂ)))
  simp only [fieldPairing_scale, abs_inv, fieldEquiv_abs_det] at h
  simp only [fieldEquiv_apply] at h
  unfold traceFourier traceMeasure
  simp only [integral_smul_measure, ENNReal.toReal_ofReal (le_of_lt (haarScalar_pos F))]
  rw [h]
  simp only [Complex.real_smul, Complex.ofReal_inv]
  ring

end PoissonArch
end DedekindZetaZeroFree

end

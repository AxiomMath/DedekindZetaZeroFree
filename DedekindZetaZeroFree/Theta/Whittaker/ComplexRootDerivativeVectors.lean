module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.PlanarBesselKernelAndJacquetValues
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.UpperRoot.SeminormDifferentiation
public import DedekindZetaZeroFree.Analysis.SmoothSubmoduleSeminormConvergence

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxRootDerivativeVectors

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
open KPCplxJacquetFunctional KPCplxPlanarKernel KPCplxBessel

abbrev ComplexifiedUpperRoot := ℂ × ℂ

def E_R : ComplexifiedUpperRoot := (1, 0)

def E_I : ComplexifiedUpperRoot := (0, 1)

noncomputable def Z_plus : ComplexifiedUpperRoot :=
  (1 / 2 : ℂ) • (E_R - Complex.I • E_I)

noncomputable def Z_minus : ComplexifiedUpperRoot :=
  (1 / 2 : ℂ) • (E_R + Complex.I • E_I)

noncomputable def realUpperRootDerivativeFunction (β : ℂˣ) (z : ℂ)
    (h : Theta β) (g : ComplexGL2) : ℂ :=
  deriv (fun t : ℝ => (h : PrincipalSeries negativeParameter)
    (g * upperUnipotent ((t : ℂ) * z))) 0

open scoped Matrix.Norms.Elementwise ContDiff
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
private theorem unipotent_affine (z : ℂ) (t : ℝ) :
  (upperUnipotent ((t : ℂ) * z) : Mat) = (1 : Mat) + t • !![0,z;0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent, Matrix.one_apply, Complex.real_smul, Matrix.smul_apply]
private theorem invertible_open : IsOpen {p : Mat × ℂ | p.1.det ≠ 0} := by
  have hc : Continuous (fun p : Mat × ℂ => p.1.det) := by
    simp only [Matrix.det_fin_two]; fun_prop
  exact isOpen_ne_fun hc continuous_const
private theorem smooth_slice (F : Mat × ℂ → ℂ)
    (hF : ContDiffOn ℝ ∞ F {p | p.1.det ≠ 0}) (X : Mat) :
    ContDiff ℝ ∞ (fun x : ℂ => deriv (fun t : ℝ => F (1 + t • X, x)) 0) := by
  have hd := hF.fderiv_of_isOpen invertible_open (m := ∞) (by simp)
  have hi : ContDiff ℝ ∞ (fun x : ℂ => ((1 : Mat), x)) := contDiff_const.prodMk contDiff_id
  have hm : ∀ x : ℂ, ((1 : Mat), x) ∈ {p : Mat × ℂ | p.1.det ≠ 0} := by
    intro x; simp
  have hh : ContDiff ℝ ∞ (fun x : ℂ => fderiv ℝ F (1,x) (X,0)) :=
    (hd.comp_contDiff hi hm).clm_apply contDiff_const
  convert hh using 1
  funext x
  have hx : DifferentiableAt ℝ F ((1 : Mat), x) :=
    (hF.contDiffAt (invertible_open.mem_nhds (hm x))).differentiableAt (by simp)
  have ht : HasDerivAt (fun t : ℝ => ((1 : Mat) + t • X, x)) (X, 0) 0 := by
    apply HasDerivAt.prodMk
    · convert ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat) using 1 <;> simp
    · exact hasDerivAt_const (0 : ℝ) x
  exact (hx.hasFDerivAt.comp_hasDerivAt_of_eq 0 ht (by simp)).deriv

theorem realUpperRootDerivativeFunction_mem (β : ℂˣ) (z : ℂ) (h : Theta β) :
    realUpperRootDerivativeFunction β z h ∈ principalSeriesSubmodule negativeParameter := by
  change HasCovariance negativeParameter _ ∧ ContDiff ℝ ∞ (openCoordinate _) ∧ ContDiff ℝ ∞ (infinityCoordinate _)
  refine ⟨?_, ?_, ?_⟩
  · intro a d b g
    unfold realUpperRootDerivativeFunction
    have he : (fun t : ℝ => (h : PrincipalSeries negativeParameter)
        (upperTriangular a d b * g * upperUnipotent ((t : ℂ) * z))) =
        fun t : ℝ => (inductionWeight negativeParameter a d : ℂ) *
          (h : PrincipalSeries negativeParameter) (g * upperUnipotent ((t : ℂ) * z)) := by
      funext t
      rw [mul_assoc]
      exact h.val.property.1 a d b _
    rw [he, deriv_const_mul_field]
  · have hh := smooth_slice _ (image_smooth β h).1 !![0,z;0,0]
    convert hh using 1
    funext x
    unfold openCoordinate realUpperRootDerivativeFunction
    congr 1
    funext t
    unfold orbitOpenCoordinate
    rw [← unipotent_affine]
    rw [← Matrix.GeneralLinearGroup.coe_mul]
    unfold matrixFunction
    rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero _)]
    apply congrArg (h : PrincipalSeries negativeParameter)
    apply Units.ext
    rfl
  · have hh := smooth_slice _ (image_smooth β h).2 !![0,z;0,0]
    convert hh using 1
    funext x
    unfold infinityCoordinate realUpperRootDerivativeFunction
    congr 1
    funext t
    unfold orbitInfinityCoordinate
    rw [← unipotent_affine]
    rw [← Matrix.GeneralLinearGroup.coe_mul]
    unfold matrixFunction
    rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero _)]
    apply congrArg (h : PrincipalSeries negativeParameter)
    apply Units.ext
    rfl

noncomputable def ambientRealUpperRootDerivative (β : ℂˣ) (z : ℂ) (h : Theta β) :
    PrincipalSeries negativeParameter :=
  ⟨realUpperRootDerivativeFunction β z h, realUpperRootDerivativeFunction_mem β z h⟩

theorem ambientRealUpperRootDerivative_mem_image (β : ℂˣ) (z : ℂ) (h : Theta β) :
    ambientRealUpperRootDerivative β z h ∈ imageSubmodule β := by
  rw [imageSubmodule_eq_top]
  trivial

noncomputable def dPiRealUpperRoot (β : ℂˣ) (z : ℂ) (h : Theta β) : Theta β :=
  ⟨ambientRealUpperRootDerivative β z h,
    ambientRealUpperRootDerivative_mem_image β z h⟩

noncomputable def dPiComplexUpperRoot (β : ℂˣ) (X : ComplexifiedUpperRoot)
    (h : Theta β) : Theta β :=
  X.1 • dPiRealUpperRoot β 1 h + X.2 • dPiRealUpperRoot β Complex.I h

noncomputable def vZero (c : ℝ) (β : ℂˣ) : Theta β :=
  ((besselCoefficient c : ℂ)⁻¹) •
    intertwinerToImage β (sphericalSection positiveParameter)

noncomputable def vPlus (c : ℝ) (β : ℂˣ) : Theta β :=
  (2 / (Complex.I * (c : ℂ))) • dPiComplexUpperRoot β Z_plus (vZero c β)

noncomputable def vMinus (c : ℝ) (β : ℂˣ) : Theta β :=
  (2 / (Complex.I * (c : ℂ))) • dPiComplexUpperRoot β Z_minus (vZero c β)

noncomputable def whittakerValue (β : ℂˣ) (h : Theta β) (y : ℂˣ) : ℂ :=
  thetaJacquetFunctional β
    (imageAction β (Matrix.ProjGenLinGroup.mk (diagonal y)) h)

noncomputable def radius (y : ℂˣ) : ℝ := ‖(y : ℂ)‖

noncomputable def omegaPlus (y : ℂˣ) : ℂ := (y : ℂ) / (radius y : ℂ)

noncomputable def omegaMinus (y : ℂˣ) : ℂ := star (y : ℂ) / (radius y : ℂ)

theorem imageAction_smul (β : ℂˣ) (g : ComplexPGL2) (a : ℂ) (h : Theta β) :
    imageAction β g (a • h) = a • imageAction β g h := by
  induction g using Quotient.inductionOn with
  | _ g =>
    apply Subtype.ext
    apply Subtype.ext
    funext x
    rfl

private theorem whittakerValue_smul (β : ℂˣ) (a : ℂ) (h : Theta β) (y : ℂˣ) :
    whittakerValue β (a • h) y = a * whittakerValue β h y := by
  simp [whittakerValue, imageAction_smul]

private theorem whittakerValue_add (β : ℂˣ) (h k : Theta β) (y : ℂˣ) :
    whittakerValue β (h + k) y = whittakerValue β h y + whittakerValue β k y := by
  have he : imageAction β (Matrix.ProjGenLinGroup.mk (diagonal y)) (h + k) =
      imageAction β (Matrix.ProjGenLinGroup.mk (diagonal y)) h +
      imageAction β (Matrix.ProjGenLinGroup.mk (diagonal y)) k := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    rfl
  simp only [whittakerValue, he, map_add]

private theorem whittakerValue_zero (β : ℂˣ) (y : ℂˣ) :
    whittakerValue β 0 y = 0 := by
  simpa using whittakerValue_smul β 0 (0 : Theta β) y

private theorem diagonal_upper (y : ℂˣ) (x : ℂ) :
    diagonal y * upperUnipotent x = upperUnipotent ((y : ℂ) * x) * diagonal y := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, upperUnipotent, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem whittakerValue_upperUnipotent (β : ℂˣ) (h : Theta β) (y : ℂˣ) (x : ℂ) :
    whittakerValue β (imageAction β (Matrix.ProjGenLinGroup.mk (upperUnipotent x)) h) y =
      (character (β : ℂ) ((y : ℂ) * x) : ℂ) * whittakerValue β h y := by
  unfold whittakerValue
  have he : imageAction β (Matrix.ProjGenLinGroup.mk (diagonal y))
      (imageAction β (Matrix.ProjGenLinGroup.mk (upperUnipotent x)) h) =
      imageAction β (Matrix.ProjGenLinGroup.mk (upperUnipotent ((y : ℂ) * x)))
        (imageAction β (Matrix.ProjGenLinGroup.mk (diagonal y)) h) := by
    apply Subtype.ext
    simp only [imageAction_coe, ← pi_mul, ← map_mul, diagonal_upper]
  rw [he, thetaJacquetFunctional_covariance]

theorem whittaker_upperRootOrbit_hasDerivAt (c : ℝ) (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (z : ℂ) (h : Theta β) (y : ℂˣ) :
    HasDerivAt (fun t : ℝ =>
      whittakerValue β (imageAction β (Matrix.ProjGenLinGroup.mk
        (upperUnipotent ((t : ℂ) * z))) h) y)
      (Complex.I * (c : ℂ) * (((y : ℂ) * z).re : ℂ) * whittakerValue β h y) 0 := by
  simp_rw [whittakerValue_upperUnipotent]
  have he : (fun t : ℝ => (character (β : ℂ) ((y : ℂ) * ((t : ℂ) * z)) : ℂ)) =
      fun t : ℝ => Complex.exp ((t : ℂ) * (Complex.I * (c : ℂ) * (((y : ℂ) * z).re : ℂ))) := by
    funext t
    change (Circle.exp _ : ℂ) = _
    rw [Circle.coe_exp, hβ]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have ht := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const
    (Complex.I * (c : ℂ) * (((y : ℂ) * z).re : ℂ))).cexp
  have hmul := ht.mul_const (whittakerValue β h y)
  convert hmul using 1
  · funext t
    rw [congrFun he t]
    rfl
  · simp

noncomputable def whittakerCLM (β : ℂˣ) (y : ℂˣ) : Theta β →L[ℂ] ℂ := by
  let T : Theta β →ₗ[ℂ] Theta β :=
    { toFun := imageAction β (Matrix.ProjGenLinGroup.mk (diagonal y))
      map_add' := by
        intro h k
        apply Subtype.ext
        apply Subtype.ext
        rfl
      map_smul' := by
        intro a h
        exact imageAction_smul β _ a h }
  exact (thetaJacquetFunctional β).comp
    { toLinearMap := T
      cont := (imageAction_continuous β).comp
        (continuous_const.prodMk continuous_id) }

theorem whittaker_realUpperRootDerivative_of_tendsto (c : ℝ)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (z : ℂ) (h : Theta β) (y : ℂˣ)
    (hd : Filter.Tendsto (fun t : ℝ => (t⁻¹ : ℂ) •
      (imageAction β (Matrix.ProjGenLinGroup.mk (upperUnipotent ((t : ℂ) * z))) h - h))
      (nhdsWithin 0 {0}ᶜ) (nhds (dPiRealUpperRoot β z h))) :
    whittakerValue β (dPiRealUpperRoot β z h) y =
      Complex.I * (c : ℂ) * (((y : ℂ) * z).re : ℂ) * whittakerValue β h y := by
  let L := whittakerCLM β y
  have hl := (L.continuous.tendsto _).comp hd
  have hs := (whittaker_upperRootOrbit_hasDerivAt c β hβ z h y).tendsto_slope
  have he : (fun t : ℝ => L ((t⁻¹ : ℂ) •
      (imageAction β (Matrix.ProjGenLinGroup.mk (upperUnipotent ((t : ℂ) * z))) h - h))) =
      slope (fun t : ℝ => whittakerValue β
        (imageAction β (Matrix.ProjGenLinGroup.mk (upperUnipotent ((t : ℂ) * z))) h) y) 0 := by
    funext t
    rw [L.map_smul]
    have hsub : L (imageAction β (Matrix.ProjGenLinGroup.mk
        (upperUnipotent ((t : ℂ) * z))) h - h) =
        L (imageAction β (Matrix.ProjGenLinGroup.mk
          (upperUnipotent ((t : ℂ) * z))) h) - L h := map_sub L.toLinearMap _ _
    rw [hsub]
    change (t⁻¹ : ℂ) • (whittakerValue β
      (imageAction β (Matrix.ProjGenLinGroup.mk (upperUnipotent ((t : ℂ) * z))) h) y -
      whittakerValue β h y) = (t - 0)⁻¹ • (whittakerValue β
      (imageAction β (Matrix.ProjGenLinGroup.mk (upperUnipotent ((t : ℂ) * z))) h) y -
      whittakerValue β (imageAction β (Matrix.ProjGenLinGroup.mk
        (upperUnipotent ((0 : ℂ) * z))) h) y)
    simp only [sub_zero, Complex.real_smul, Complex.ofReal_inv]
    congr 2
    change whittakerValue β h y = whittakerValue β
      (imageAction β (Matrix.ProjGenLinGroup.mk (upperUnipotent ((0 : ℂ) * z))) h) y
    rw [whittakerValue_upperUnipotent]
    simp [character]
  change Filter.Tendsto (fun t : ℝ => L ((t⁻¹ : ℂ) •
    (imageAction β (Matrix.ProjGenLinGroup.mk (upperUnipotent ((t : ℂ) * z))) h - h)))
    (nhdsWithin 0 {0}ᶜ) (nhds (L (dPiRealUpperRoot β z h))) at hl
  rw [he] at hl
  exact tendsto_nhds_unique hl hs

private theorem realUpperRootDerivative_hasDerivAt (β : ℂˣ) (z : ℂ)
    (h : Theta β) (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => (h : PrincipalSeries negativeParameter)
      (g * upperUnipotent ((t : ℂ) * z)))
      (ambientRealUpperRootDerivative β z h g) 0 := by
  have hf := ((principalSeries_mem_iff negativeParameter
    (h : PrincipalSeries negativeParameter)).mp h.val.property).2
  have hM : ContDiff ℝ ∞ (fun t : ℝ =>
      (g : Mat) * ((1 : Mat) + t • !![0,z;0,0])) := by
    change ContDiff ℝ ∞ (fun t : ℝ => (fun i j =>
      ((g : Mat) * ((1 : Mat) + t • !![0,z;0,0])) i j : Fin 2 → Fin 2 → ℂ))
    rw [contDiff_pi]
    intro i
    rw [contDiff_pi]
    intro j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply]
    fun_prop
  have hm : ∀ t : ℝ, ((g : Mat) * ((1 : Mat) + t • !![0,z;0,0])).det ≠ 0 := by
    intro t
    rw [← unipotent_affine, ← Matrix.GeneralLinearGroup.coe_mul]
    exact Matrix.GeneralLinearGroup.det_ne_zero _
  have hc := hf.comp_contDiff hM hm
  have he : (fun t : ℝ => matrixFunction (h : PrincipalSeries negativeParameter)
      ((g : Mat) * ((1 : Mat) + t • !![0,z;0,0]))) =
      fun t : ℝ => (h : PrincipalSeries negativeParameter)
        (g * upperUnipotent ((t : ℂ) * z)) := by
    funext t
    rw [← unipotent_affine, ← Matrix.GeneralLinearGroup.coe_mul]
    unfold matrixFunction
    rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero _)]
    apply congrArg (h : PrincipalSeries negativeParameter)
    apply Units.ext
    rfl
  change ContDiff ℝ ∞ (fun t : ℝ => matrixFunction (h : PrincipalSeries negativeParameter)
    ((g : Mat) * ((1 : Mat) + t • !![0,z;0,0]))) at hc
  rw [he] at hc
  have hc' : ContDiff ℝ ∞ (fun t : ℝ => (h : PrincipalSeries negativeParameter)
    (g * upperUnipotent ((t : ℂ) * z))) := hc
  exact (hc'.differentiable (by simp) (0 : ℝ)).hasDerivAt

theorem whittaker_realUpperRootDerivative (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (z : ℂ) (h : Theta β) (y : ℂˣ) :
    whittakerValue β (dPiRealUpperRoot β z h) y =
      Complex.I * (c : ℂ) * (((y : ℂ) * z).re : ℂ) * whittakerValue β h y := by
  apply whittaker_realUpperRootDerivative_of_tendsto c β hβ z h y
  apply ThetaArchAngularChartSeminorms.tendsto_submodule_of_chartSeminorm
    negativeParameter (imageSubmodule β)
  exact KPCplxUpperRootSeminormDifferentiation.upperRoot_differenceQuotient_chartSeminorm_of_pointwise
    β h z (ambientRealUpperRootDerivative β z h)
    (realUpperRootDerivative_hasDerivAt β z h)

theorem whittaker_complexUpperRootDerivatives (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (h : Theta β) (y : ℂˣ) :
    whittakerValue β (dPiComplexUpperRoot β Z_plus h) y =
        (Complex.I * (c : ℂ) / 2) * (y : ℂ) * whittakerValue β h y ∧
    whittakerValue β (dPiComplexUpperRoot β Z_minus h) y =
        (Complex.I * (c : ℂ) / 2) * star (y : ℂ) * whittakerValue β h y := by
  simp only [dPiComplexUpperRoot, whittakerValue_add, whittakerValue_smul]
  rw [whittaker_realUpperRootDerivative c hc β hβ 1,
    whittaker_realUpperRootDerivative c hc β hβ Complex.I]
  simp only [Z_plus, Z_minus, E_R, E_I, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, smul_eq_mul,
    mul_one, mul_zero, sub_zero, zero_sub, add_zero, zero_add,
    Complex.mul_I_re]
  constructor <;> apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

theorem whittaker_vZero (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (y : ℂˣ) :
    whittakerValue β (vZero c β) y =
      ((radius y * besselKThird (c * radius y) : ℝ) : ℂ) := by
  rw [vZero, whittakerValue_smul]
  unfold whittakerValue
  rw [← intertwinerToImage_equivariant, thetaJacquetFunctional_intertwiner,
    jacquet_spherical_diagonal_eq_bessel c hc β hβ y]
  have hb : (besselCoefficient c : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (besselCoefficient_pos c hc))
  simp only [Complex.ofReal_mul, radius]
  field_simp

theorem whittaker_vPlus (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (y : ℂˣ) :
    whittakerValue β (vPlus c β) y =
      ((radius y ^ 2 : ℝ) : ℂ) * omegaPlus y *
        (besselKThird (c * radius y) : ℂ) := by
  rw [vPlus, whittakerValue_smul,
    (whittaker_complexUpperRootDerivatives c hc β hβ (vZero c β) y).1,
    whittaker_vZero c hc β hβ y]
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  have hr : (radius y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (Units.ne_zero y))
  simp only [omegaPlus, Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp

theorem whittaker_vMinus (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (y : ℂˣ) :
    whittakerValue β (vMinus c β) y =
      ((radius y ^ 2 : ℝ) : ℂ) * omegaMinus y *
        (besselKThird (c * radius y) : ℂ) := by
  rw [vMinus, whittakerValue_smul,
    (whittaker_complexUpperRootDerivatives c hc β hβ (vZero c β) y).2,
    whittaker_vZero c hc β hβ y]
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  have hr : (radius y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (Units.ne_zero y))
  simp only [omegaMinus, Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp

theorem first_root_vectors_nonzero (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) :
    vZero c β ≠ 0 ∧ vPlus c β ≠ 0 ∧ vMinus c β ≠ 0 ∧
      dPiComplexUpperRoot β Z_plus (vZero c β) ≠ 0 ∧
      dPiComplexUpperRoot β Z_minus (vZero c β) ≠ 0 := by
  have hK : (besselKThird c : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (besselKThird_pos c hc))
  have h0 : vZero c β ≠ 0 := by
    intro he
    have hv := whittaker_vZero c hc β hβ 1
    rw [he, whittakerValue_zero] at hv
    simp [radius] at hv
    exact hK hv.symm
  have hp : vPlus c β ≠ 0 := by
    intro he
    have hv := whittaker_vPlus c hc β hβ 1
    rw [he, whittakerValue_zero] at hv
    simp [radius, omegaPlus] at hv
    exact hK hv.symm
  have hm : vMinus c β ≠ 0 := by
    intro he
    have hv := whittaker_vMinus c hc β hβ 1
    rw [he, whittakerValue_zero] at hv
    simp [radius, omegaMinus] at hv
    exact hK hv.symm
  refine ⟨h0, hp, hm, ?_, ?_⟩
  · intro he
    apply hp
    simp [vPlus, he]
  · intro he
    apply hm
    simp [vMinus, he]

end DedekindZetaZeroFree.KPCplxRootDerivativeVectors

section

namespace DedekindZetaZeroFree.KPCplxRootDerivativeVectors

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
open KPCplxJacquetFunctional KPCplxPlanarKernel KPCplxBessel

open scoped Matrix.Norms.Elementwise ContDiff
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ

theorem vZero_spherical (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (k : compactSubgroup) :
    imageAction β k (vZero c β) = vZero c β := by
  rw [vZero, imageAction_smul, (spherical_image β).2 k]

end DedekindZetaZeroFree.KPCplxRootDerivativeVectors

end

module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ComplexFirstRootBounds
public import DedekindZetaZeroFree.Theta.Profiles.LocalTensorActions

@[expose] public section

noncomputable section
open scoped NumberField Classical ENNReal
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.RootDerivatives
open NumberField MeasureTheory
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
open KPCplxRootDerivativeVectors KPReferenceChange.StandardComplexImage
open KPActualReflectionData.StandardLocalSource
variable {F : Type} [Field F] [NumberField F]

theorem besselKThird_eq_KThird (z : ℝ) (hz : 0 < z) :
    KPCplxBessel.besselKThird z = KThird z := by
  rw [KPCplxBessel.besselKThird_eq_modifiedBesselK z hz, KThird_eq_integral z hz]
  unfold KPCplxBessel.modifiedBesselK thirdBesselSchlafliIntegrand
  congr 1
  funext u
  congr 1
  congr 1
  ring

def sphericalSeed : Theta frequency := vZero (4 * Real.pi) frequency

theorem sphericalSeed_value (y : ℂˣ) :
    whittakerValue frequency sphericalSeed y =
      (‖(y : ℂ)‖ : ℂ) * (KThird (4 * Real.pi * ‖(y : ℂ)‖) : ℂ) := by
  rw [sphericalSeed, whittaker_vZero (4 * Real.pi) (by positivity)
    frequency frequency_coe, radius,
    besselKThird_eq_KThird _ (mul_pos (by positivity) (norm_pos_iff.mpr y.ne_zero))]
  exact Complex.ofReal_mul _ _

theorem sphericalSeed_mem_core :
    (sphericalSeed : PrincipalSeries negativeParameter) ∈ KPGlobalResidualConstruction.complexCore := by
  change (sphericalSeed : PrincipalSeries negativeParameter) ∈
    imageSubmodule (1 : ℂˣ) ⊓ ⨆ ℓ, KPCplxIntertwinerEigenvalues.harmonicKType negativeParameter ℓ
  rw [imageSubmodule_eq_top, top_inf_eq]
  apply Submodule.mem_iSup_of_mem 0
  change (vZero (4 * Real.pi) frequency : PrincipalSeries negativeParameter) ∈ _
  rw [vZero, SetLike.val_smul, intertwinerToImage_coe,
    KPCplxIntertwinerEigenvalues.standardIntertwiner_spherical]
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  rw [KPCplxIntertwinerEigenvalues.harmonicKType_zero_eq_span]
  exact Submodule.subset_span (Set.mem_singleton _)

def sphericalCoreSeed : KPGlobalResidualConstruction.complexCore :=
  ⟨(sphericalSeed : PrincipalSeries negativeParameter), sphericalSeed_mem_core⟩

theorem sphericalCoreSeed_SU2_fixed (k : ComplexSU2) :
    KPGlobalResidualConstruction.complexCoreSU2Action k sphericalCoreSeed = sphericalCoreSeed := by
  apply Subtype.ext
  have h := vZero_spherical (4 * Real.pi) (by positivity) frequency frequency_coe
    ⟨Matrix.ProjGenLinGroup.mk (complexSU2Embedding k), ⟨k, rfl⟩⟩
  change KPCplxPrincipalSeriesCharts.pi negativeParameter (Matrix.ProjGenLinGroup.mk (complexSU2Embedding k))
    (vZero (4 * Real.pi) frequency).val = (vZero (4 * Real.pi) frequency).val
  exact congrArg (fun v : Theta frequency => v.val) h

theorem sphericalSeed_detected : whittakerValue frequency sphericalSeed 1 ≠ 0 := by
  rw [sphericalSeed_value]
  simp only [Units.val_one, norm_one, Complex.ofReal_one, mul_one, one_mul]
  exact Complex.ofReal_ne_zero.mpr (KThird_pos _ (by positivity)).ne'

theorem completion_coordinate_norm (A : SArithmeticData F) (w : InfinitePlace F)
    (z : w.Completion) : ‖coordinate A w z‖ = ‖z‖ := by
  have hi := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F A.zeta12 A.primitive_zeta12 w)).isometry
  have hd := hi.dist_eq z 0
  change dist (coordinate A w z) (coordinate A w 0) = dist z 0 at hd
  simpa only [map_zero, dist_zero_right] using hd

theorem sphericalSeed_completion_value (A : SArithmeticData F) (w : InfinitePlace F)
    (z : w.Completionˣ) :
    KPCplxJacquetFunctional.thetaJacquetFunctional frequency
      (action A w (KPPGLLocalCover.A F A.zeta12 A.primitive_zeta12 (Sum.inl w) z)
        sphericalSeed) =
      (‖(z : w.Completion)‖ : ℂ) *
        (KThird (4 * Real.pi * Real.sqrt (‖(z : w.Completion)‖ ^ 2)) : ℂ) := by
  let y : ℂˣ := Units.map (coordinate A w).toMonoidHom z
  have hu : Units.map (coordinate A w).symm.toRingHom.toMonoidHom y = z := by
    apply Units.ext
    exact (coordinate A w).symm_apply_apply _
  rw [← hu, complexJacquet_actualDiagonal, sphericalSeed_value]
  have hn : ‖(y : ℂ)‖ = ‖(z : w.Completion)‖ := completion_coordinate_norm A w _
  rw [hn, Real.sqrt_sq (norm_nonneg _), hu]

theorem sphericalCoreSeed_ne_zero : sphericalCoreSeed ≠ 0 := by
  intro hz
  have he : (sphericalSeed : PrincipalSeries negativeParameter) = 0 :=
    congrArg (fun h : KPGlobalResidualConstruction.complexCore => h.val) hz
  have hv : sphericalSeed = 0 := Subtype.ext he
  apply sphericalSeed_detected
  rw [hv]
  unfold whittakerValue
  have hz' : imageAction frequency (Matrix.ProjGenLinGroup.mk (diagonal (1 : ℂˣ)))
      (0 : Theta frequency) = 0 := by
    apply Subtype.ext
    change KPCplxPrincipalSeriesCharts.pi negativeParameter (Matrix.ProjGenLinGroup.mk (diagonal (1 : ℂˣ))) 0 = 0
    exact KPGlobalResidualConstruction.pi_zero _ _
  rw [hz', map_zero]

def coreInStandardImage : KPGlobalResidualConstruction.complexCore →ₗ[ℂ] Theta frequency :=
  KPGlobalResidualConstruction.complexCore.subtype.codRestrict (imageSubmodule frequency)
    (fun h => by rw [imageSubmodule_eq_top]; trivial)

@[simp] theorem coreInStandardImage_spherical : coreInStandardImage sphericalCoreSeed =
    sphericalSeed := rfl

theorem continuous_whittaker_sphericalCore_ne_zero (A : SArithmeticData F)
    (w : InfinitePlace F) (ell : Theta frequency →L[ℂ] ℂ)
    (hell : ell ∈ localWhittakerSpace _ (Theta frequency) (complexRootAction A w)
      (complexRawPsi w).toAddChar.toMonoidHom) (hne : ell ≠ 0) :
    ell (coreInStandardImage sphericalCoreSeed) ≠ 0 := by
  obtain ⟨a, ha, he⟩ := complexWhittaker_scalar A w ell hell hne
  rw [coreInStandardImage_spherical, he, ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply mul_ne_zero ha
  have hv : KPCplxJacquetFunctional.thetaJacquetFunctional frequency sphericalSeed =
      whittakerValue frequency sphericalSeed 1 := by
    unfold whittakerValue
    have hd : diagonal (1 : ℂˣ) = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagonal, Matrix.one_apply]
    rw [hd, Matrix.ProjGenLinGroup.mk_one]
    congr 1
    apply Subtype.ext
    exact (KPCplxPrincipalSeriesCharts.pi_one _ _).symm
  rw [hv]
  exact sphericalSeed_detected

theorem sphericalSeed_completion_normalization (A : SArithmeticData F)
    (w : InfinitePlace F) (ell : Theta frequency →L[ℂ] ℂ)
    (hell : ell ∈ localWhittakerSpace _ (Theta frequency) (complexRootAction A w)
      (complexRawPsi w).toAddChar.toMonoidHom) (hne : ell ≠ 0) :
    ∃ t : ℂ, t ≠ 0 ∧ ∀ z : w.Completionˣ,
      t * ell (action A w (KPPGLLocalCover.A F A.zeta12 A.primitive_zeta12 (Sum.inl w) z)
        sphericalSeed) = (‖(z : w.Completion)‖ : ℂ) *
          (KThird (4 * Real.pi * Real.sqrt (‖(z : w.Completion)‖ ^ 2)) : ℂ) := by
  obtain ⟨a, ha, he⟩ := complexWhittaker_scalar A w ell hell hne
  refine ⟨a⁻¹, inv_ne_zero ha, fun z => ?_⟩
  rw [he, ContinuousLinearMap.smul_apply, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ ha, one_mul, sphericalSeed_completion_value]

end DedekindZetaZeroFree.RootDerivatives

end

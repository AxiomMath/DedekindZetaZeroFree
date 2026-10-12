module

public import DedekindZetaZeroFree.Eisenstein.Induction.FiniteEvaluation.SphericalPGLCoreRealization
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.ArchimedeanRootCovariance
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.ArchimedeanSliceCharts

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.CurrentArchFamily
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralChamber
open KPLiteralScalarHCCompactOrbit KPLiteralScalarHCSliceCharts KPLiteralScalarHCExtraction
open KPCplxCharacterHaar KPGlobalTorusBorelTwistCompatibility
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming complexSectionHom → complexSectionHom
open _root_.DedekindZetaZeroFree.ScalarRationalProductTransport renaming scalar → scalar
open KPLiteralScalarHCLocalCovariance
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
variable (C : ModelData F ζ hζ) (f : Flat F ζ hζ K)
theorem productHCScalar_borel
    (t : (productModel F ζ hζ C).H) (x : KPGlobalTorusFunctionData.Adeles F)
    (g : KPLiteralRaw.G F ζ hζ) :
    productHCScalar F ζ hζ K hK C f
        ((t.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ t.val *
        ((productModel F ζ hζ C).character t : ℂ) * productHCScalar F ζ hζ K hK C f g := by
  have hc := (scalarSection F ζ hζ _ (productHCSection F ζ hζ K hK C f)).property t x g
  change _ = KPGlobalTorusFunctionData.deltaHalf F ζ hζ t.val *
    (((productModel F ζ hζ C).character t : ℂ) * normPower F ζ hζ 0 t.val) * _ at hc
  simpa only [productHCScalar, scalar, LinearMap.comp_apply, Submodule.subtype_apply, normPower, zero_mul, Complex.exp_zero, mul_one] using hc
theorem productHCScalar_arch_borel_zero
    (z : KPGlobalTorusFunctionData.TorusArch F)
    (hz : z ∈ KPGlobalTorusFunctionData.torusArchDomain F)
    (x : KPGlobalTorusFunctionData.Adeles F) (g : KPLiteralRaw.G F ζ hζ) :
    productHCScalar F ζ hζ K hK C f
        (((KPGlobalTorusFunctionData.torusArchChart F ζ hζ z).val *
          KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      (((∏ w : InfinitePlace F, ‖z w‖ ^ 2) ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
        productHCScalar F ζ hζ K hK C f g := by
  obtain ⟨t, he, hχ⟩ := productModel_arch_character F ζ hζ C z
  have hc := productHCScalar_borel F ζ hζ K hK C f t x g
  rw [he] at hc
  rw [hc, hχ]
  have hd : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ t.val : ℝ≥0) : ℝ)) := by
    exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero
      (KPGlobalTorusFunctionData.delta F ζ hζ t.val)))
  have hν : (KPGlobalCenterRationalCharacter.positiveComplex
      (KPGlobalCenterRationalCharacter.nu F ζ hζ t.val) : ℂ) =
      ((((KPGlobalTorusFunctionData.delta F ζ hζ t.val : ℝ≥0) : ℝ) ^ (1 / 6 : ℝ) : ℝ) : ℂ) := by
    change (((KPGlobalCenterRationalCharacter.nu F ζ hζ t.val : ℝ≥0) : ℝ) : ℂ) = _
    rw [KPGlobalCenterRationalCharacter.nu_formula]
    rfl
  rw [he] at hd hν
  rw [he, hν, KPGlobalTorusFunctionData.deltaHalf, ← Complex.ofReal_mul,
    Real.sqrt_eq_rpow, ← Real.rpow_add hd]
  rw [show (1 / 2 : ℝ) + 1 / 6 = 2 / 3 by norm_num,
    KPGlobalTorusBorelNormTwistTransport.AnalyticInputs.delta_chart_formula F ζ hζ z hz]

open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming sectionTuple_insertion → sectionTuple_insertion

theorem archMatrixInsertion_projective_congr
    (a b : InfinitePlace F → ComplexGL2)
    (h : ∀ w, Matrix.ProjGenLinGroup.mk (a w) = Matrix.ProjGenLinGroup.mk (b w)) :
    archMatrixInsertion F ζ hζ a = archMatrixInsertion F ζ hζ b := by
  change scalarQuotient F ζ hζ (amalgamation F ζ hζ (sectionTuple F ζ hζ a)) =
    scalarQuotient F ζ hζ (amalgamation F ζ hζ (sectionTuple F ζ hζ b))
  rw [sectionTuple_insertion, sectionTuple_insertion]
  congr 1
  exact funext h

theorem archMatrixInsertion_diagonal (z : InfinitePlace F → ℂˣ) :
    archMatrixInsertion F ζ hζ (fun w => KubotaRankTwo.d ℂ (z w) 1) =
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ (fun w => (z w : ℂ))).val := by
  change scalarQuotient F ζ hζ (amalgamation F ζ hζ _) =
    scalarQuotient F ζ hζ (amalgamation F ζ hζ _)
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inr q => rfl
  | inl w =>
    change complexSectionHom F ζ hζ w (KubotaRankTwo.d ℂ (z w) 1) = _
    simp only [KPGlobalTorusFunctionData.archDiagonalTuple]
    change KPLocalCover.CubicGL2Raw.mk _ 1 = KPLocalCover.CubicGL2Raw.mk _ 1
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map]

private theorem upper_projective (a d : ℂˣ) (b : ℂ) :
    Matrix.ProjGenLinGroup.mk (KPCplxPrincipalSeriesCharts.upperTriangular a d b) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (a / d) 1 * upperUnipotent (b / a)) := by
  apply (Matrix.ProjGenLinGroup.mk_eq_mk_iff).mpr
  refine ⟨Units.mk0 ((d : ℂ)⁻¹) (inv_ne_zero d.ne_zero), ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [KPCplxPrincipalSeriesCharts.upperTriangular, upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]
  field_simp

theorem productHCScalar_arch_upperTriangular_zero
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ)
    (g : InfinitePlace F → ComplexGL2) :
    productHCScalar F ζ hζ K hK C f
        (c.val * archMatrixInsertion F ζ hζ
          (fun w => KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w) * g w)) =
      (((∏ w : InfinitePlace F, ‖(a w : ℂ) / (d w : ℂ)‖ ^ 2) ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
        productHCScalar F ζ hζ K hK C f
          (c.val * archMatrixInsertion F ζ hζ g) := by
  have he := archMatrixInsertion_projective_congr F ζ hζ
    (fun w => KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w) * g w)
    (fun w => (KubotaRankTwo.d ℂ (a w / d w) 1 * upperUnipotent (b w / a w)) * g w)
    (fun w => by simp only [map_mul, upper_projective])
  rw [he]
  have ht : archMatrixInsertion F ζ hζ
      (fun w => (KubotaRankTwo.d ℂ (a w / d w) 1 * upperUnipotent (b w / a w)) * g w) =
      (archMatrixInsertion F ζ hζ (fun w => KubotaRankTwo.d ℂ (a w / d w) 1) *
        archMatrixInsertion F ζ hζ (fun w => upperUnipotent (b w / a w))) *
          archMatrixInsertion F ζ hζ g := by
    exact map_mul (archMatrixInsertion F ζ hζ) _ _ |>.trans
      (congrArg (· * archMatrixInsertion F ζ hζ g) (map_mul (archMatrixInsertion F ζ hζ) _ _))
  rw [ht]
  have hcomm := archMatrixInsertion_commutes_finite F ζ hζ
    (fun w => KubotaRankTwo.d ℂ (a w / d w) 1) c
  rw [← mul_assoc, ← mul_assoc, ← hcomm.eq, mul_assoc, mul_assoc,
    ← mul_assoc c.val,
    ← (archMatrixInsertion_commutes_finite F ζ hζ (fun w => upperUnipotent (b w / a w)) c).eq,
    mul_assoc, ← mul_assoc, archMatrixInsertion_diagonal, archMatrixInsertion_upper]
  have hz : (fun w => ((a w / d w : ℂˣ) : ℂ)) ∈
      KPGlobalTorusFunctionData.torusArchDomain F := fun w => Units.ne_zero _
  simpa only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val] using productHCScalar_arch_borel_zero F ζ hζ K hK C f
    (fun w => ((a w / d w : ℂˣ) : ℂ)) hz (archRootAdele F ζ hζ (fun w => b w / a w))
    (c.val * archMatrixInsertion F ζ hζ g)

open KPCplxPrincipalSeriesCharts KPLiteralScalarArchUniformBands
open KPLiteralScalarArchIndependentSlices KPLiteralScalarMixedTensorGeneration

theorem productHCScalar_slice_mem_positive
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (w : InfinitePlace F) (g : InfinitePlace F → ComplexGL2) :
    (fun m => productHCScalar F ζ hζ K hK C f
      (c.val * archMatrixInsertion F ζ hζ (Function.update g w m))) ∈
        principalSeriesSubmodule positiveParameter := by
  refine ⟨?_, productHCScalar_slice_two_charts F ζ hζ K hK C f c w g⟩
  intro a d b m
  have hc := productHCScalar_arch_upperTriangular_zero F ζ hζ K hK C f c
    (Function.update 1 w a) (Function.update 1 w d) (Function.update 0 w b)
    (Function.update g w m)
  have hh : (fun v : InfinitePlace F => upperTriangular
      ((Function.update (1 : InfinitePlace F → ℂˣ) w a) v)
      ((Function.update (1 : InfinitePlace F → ℂˣ) w d) v)
      ((Function.update (0 : InfinitePlace F → ℂ) w b) v) *
        (Function.update g w m) v) = Function.update g w (upperTriangular a d b * m) := by
    funext v
    by_cases hv : v = w
    · subst v; simp
    · simp only [Function.update_of_ne hv, Pi.one_apply, Pi.zero_apply]
      have h1 : upperTriangular 1 1 0 = 1 := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [upperTriangular]
      rw [h1, one_mul]
  have hp : (∏ v : InfinitePlace F,
      ‖(((Function.update (1 : InfinitePlace F → ℂˣ) w a) v : ℂˣ) : ℂ) /
        (((Function.update (1 : InfinitePlace F → ℂˣ) w d) v : ℂˣ) : ℂ)‖ ^ 2) = ‖(a : ℂ) / (d : ℂ)‖ ^ 2 := by
    calc _ = ∏ v : InfinitePlace F, if v = w then ‖(a : ℂ) / (d : ℂ)‖ ^ 2 else 1 := by
          apply Finset.prod_congr rfl
          intro v _
          by_cases hv : v = w <;> simp [hv]
      _ = _ := by simp
  rw [hh, hp] at hc
  convert hc using 2
  unfold inductionWeight complexAbs
  norm_num [positiveParameter]

def positiveHCFamily : KPGlobalTorusFunctionData.finitePart F ζ hζ →
    multiPrincipalSeries positiveParameter (InfinitePlace F) :=
  fun c => ⟨fun g => productHCScalar F ζ hζ K hK C f
      (c.val * archMatrixInsertion F ζ hζ g),
    productHCScalar_slice_mem_positive F ζ hζ K hK C f c⟩

open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal.SphericalReseeding renaming full_torus_split → full_torus_split

end DedekindZetaZeroFree.FourierContinuation.CurrentArchFamily

end

module

public import DedekindZetaZeroFree.Metaplectic.Unipotent.RationalFrameConjugation
public import DedekindZetaZeroFree.Eisenstein.Induction.Cubic.ArchimedeanDiagonalCovariance
public import DedekindZetaZeroFree.Geometry.SymmetricSpaces.ArchimedeanSphericalQuotients

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField

namespace DedekindZetaZeroFree.KPContinuation.ChamberFlatCasimir

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def horizontalAdele (x : KPArch.Space (KPCuspLogShape.dimension F)) : InfiniteAdeleRing F :=
  fun w => (InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)).symm
      (x (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)).1

def heights (x : KPArch.Space (KPCuspLogShape.dimension F)) : InfinitePlace F → ℝ :=
  fun w => (x (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)).2

open KPAdelicCoverRestrictedProduct

def diagonalSection (u : InfinitePlace F → ℝ) : KPSmoothActualFlowData.GInfinity F :=
  fun w => Matrix.ProjGenLinGroup.mk
    (KubotaRankTwo.d ℂ (Units.mk0 ((Real.exp (u w) : ℝ) : ℂ) (by simp)) 1)

private theorem hyperbolicGLSection_factor (z : KPArch.H3) :
    KPArithmeticAction.hyperbolicGLSection z =
      KubotaRankTwo.n ℂ z.1 *
        KubotaRankTwo.d ℂ (Units.mk0 ((Real.exp z.2 : ℝ) : ℂ) (by simp)) 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KPArithmeticAction.hyperbolicGLSection, KPArch.height, KubotaRankTwo.coe_n,
      KubotaRankTwo.coe_d]

 def archUnit (z : InfinitePlace F → ℂ) (w : InfinitePlace F) : w.Completionˣ :=
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ w)
  if h : z w = 0 then 1 else Units.mk0 (e.symm (z w))
    (by exact fun h0 => h (by simpa using congrArg e h0))

private theorem map_diagonal {K L : Type} [Field K] [Field L] (e : K →+* L)
    (y : Kˣ) : Matrix.GeneralLinearGroup.map e (KubotaRankTwo.d K y 1) =
      KubotaRankTwo.d L (Units.map e y) 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map_apply, KubotaRankTwo.d]

theorem arch_diagonal_insertion (z : InfinitePlace F → ℂ) (hz : ∀ w, z w ≠ 0) :
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (fun w => Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (Units.mk0 (z w) (hz w)) 1)) =
      KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ z := by
  rw [(KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.2]
  simp only [map_diagonal]
  have he : ∀ w, Units.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom (Units.mk0 (z w) (hz w)) =
        archUnit F ζ hζ z w := by
    intro w
    apply Units.ext
    simp [archUnit, hz w]
  simp only [he]
  let l := (Finset.univ : Finset (InfinitePlace F)).toList
  let f := fun w => localToRestricted F ζ hζ (Sum.inl w)
    (KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w) (archUnit F ζ hζ z w))
  have ht : KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ z = (l.map f).prod := by
    apply Subtype.ext
    funext v
    let p : RestrictedCover F ζ hζ →* KPLocalCover.CubicGL2Raw F ζ hζ v :=
      RestrictedProduct.evalMonoidHom (KPLocalCover.CubicGL2Raw F ζ hζ)
        (B := compact F ζ hζ) v
    change _ = p ((l.map f).prod)
    rw [map_list_prod]
    simp only [List.map_map, Function.comp_def]
    cases v with
    | inl w =>
      rw [List.prod_map_eq_pow_single w (fun v => p (f v)) (by
        intro v hv _
        simp [p, f, localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
          RestrictedProduct.coe_mulSingle_apply, hv])]
      have hc : l.count w = 1 := List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp [l])
      rw [hc, pow_one]
      simp [p, f, localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
        RestrictedProduct.coe_mulSingle_apply, KPGlobalTorusFunctionData.archDiagonalTuple, archUnit]
    | inr q =>
      have hf : ∀ w, p (f w) = 1 := by
        intro w
        simp [p, f, localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
          RestrictedProduct.coe_mulSingle_apply]
      simp [hf, KPGlobalTorusFunctionData.archDiagonalTuple]
  unfold KPGlobalTorusFunctionData.archDiagonalLift
  rw [ht, map_list_prod, map_list_prod]
  simp only [List.map_map]
  rfl

theorem diagonalSection_insertion (u : InfinitePlace F → ℝ) :
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (diagonalSection F u) =
      KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (Real.exp (u w) : ℂ)) :=
  arch_diagonal_insertion F ζ hζ (fun w => (Real.exp (u w) : ℂ)) (fun w => by simp)

theorem iwasawaSection_factor (x : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ x =
      KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.archRoot
        (KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.complexParameter
          F ζ hζ (horizontalAdele F ζ hζ x)) *
      diagonalSection F (heights F ζ hζ x) := by
  funext w
  have hu : KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.complexParameter
      F ζ hζ (horizontalAdele F ζ hζ x) w
      = (x (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)).1 := by
    simp [KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.complexParameter,
      horizontalAdele]
  simp only [KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.archRoot,
    Pi.mul_apply]
  rw [hu]
  show Matrix.ProjGenLinGroup.mk (KPArithmeticAction.hyperbolicGLSection
      (x (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w))) =
    Matrix.ProjGenLinGroup.mk
        (KubotaRankTwo.n ℂ (x (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)).1) *
      Matrix.ProjGenLinGroup.mk
        (KubotaRankTwo.d ℂ (Units.mk0
          ((Real.exp (x (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)).2 : ℝ) : ℂ)
          (by simp)) 1)
  rw [← map_mul]
  exact congrArg Matrix.ProjGenLinGroup.mk
    (hyperbolicGLSection_factor
      (x (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)))

theorem iwasawa_insertion (x : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ x) =
    KPGlobalTorusFunctionData.N F ζ hζ (horizontalAdele F ζ hζ x, 0) *
      (KPContFlatArchDiagonalMultiplier.aInfinity F ζ hζ (heights F ζ hζ x)).val := by
  rw [iwasawaSection_factor F ζ hζ x,
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1,
    ← KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.root_arch_insertion
      F ζ hζ (horizontalAdele F ζ hζ x)]
  congr 1
  exact diagonalSection_insertion F ζ hζ (heights F ζ hζ x)

end DedekindZetaZeroFree.KPContinuation.ChamberFlatCasimir

end

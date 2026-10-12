module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.ProjectiveGroupAction

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRawArchCenter
open KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open _root_.DedekindZetaZeroFree.KPContFlatLogNormSmooth renaming sectionTuple → KPContFlatLogNormSmooth.sectionTuple
open _root_.DedekindZetaZeroFree.KPContFlatLogNormSmooth renaming sectionTuple_insertion → KPContFlatLogNormSmooth.sectionTuple_insertion

def archMatrices (h : RestrictedCover F ζ hζ) (w : InfinitePlace F) :=
  Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom
    (h (Sum.inl w)).g

theorem section_g (h : RestrictedCover F ζ hζ) (hf : ∀q:KPFinitePlace F,h (Sum.inr q)=1)
    (v : KPHilbert.Place F) :
    (KPContFlatLogNormSmooth.sectionTuple F ζ hζ (archMatrices F ζ hζ h) v).g=(h v).g := by
  cases v with
  | inl w =>
    change Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.map _ _) = _
    rw [←MonoidHom.comp_apply,←Matrix.GeneralLinearGroup.map_comp]
    simp
  | inr q => simp [KPContFlatLogNormSmooth.sectionTuple,hf]

theorem projection_section (h : RestrictedCover F ζ hζ) (hf : ∀q:KPFinitePlace F,h (Sum.inr q)=1) :
    restrictedProjection F ζ hζ (KPContFlatLogNormSmooth.sectionTuple F ζ hζ (archMatrices F ζ hζ h))=
    restrictedProjection F ζ hζ h := by
  apply Units.ext
  ext i j
  apply Prod.ext
  · funext w
    exact congrArg (fun g=>g i j) (section_g F ζ hζ h hf (Sum.inl w))
  · apply RestrictedProduct.ext
    intro q
    exact congrArg (fun g=>g i j) (section_g F ζ hζ h hf (Sum.inr q))

theorem raw_arch_center (h : RestrictedCover F ζ hζ) (hf : ∀q:KPFinitePlace F,h (Sum.inr q)=1) :
    ∃ε : rootsOfUnity 3 F,
    scalarQuotient F ζ hζ (amalgamation F ζ hζ h)=
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (scalarQuotient F ζ hζ (amalgamation F ζ hζ h))) *
      pglCentralInjection F ζ hζ ε := by
  let g := scalarQuotient F ζ hζ (amalgamation F ζ hζ h)
  let a := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g)
  have hi : scalarQuotient F ζ hζ (amalgamation F ζ hζ
      (KPContFlatLogNormSmooth.sectionTuple F ζ hζ (archMatrices F ζ hζ h)))=a := by
    rw [KPContFlatLogNormSmooth.sectionTuple_insertion]
    apply congrArg (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ)
    funext w
    exact (PGLComplex.AdelicSlicesRaw.archProjection_restricted_eval F ζ hζ h w).symm
  have hp : pglProjection F ζ hζ g=pglProjection F ζ hζ a := by
    rw [←hi]
    change (QuotientGroup.mk' (scalarSubgroup F)) (projection F ζ hζ (amalgamation F ζ hζ h))=
      (QuotientGroup.mk' (scalarSubgroup F)) (projection F ζ hζ (amalgamation F ζ hζ _))
    rw [projection_amalgamation,projection_amalgamation,projection_section F ζ hζ h hf]
  have hk : a⁻¹*g ∈ (pglCentralInjection F ζ hζ).range := by
    rw [pglCentralInjection_kernel]
    change pglProjection F ζ hζ (a⁻¹*g)=1
    rw [map_mul,map_inv,hp,inv_mul_cancel]
  obtain ⟨ε,he⟩ := hk
  refine ⟨ε,?_⟩
  change g=a*pglCentralInjection F ζ hζ ε
  rw [he,mul_inv_cancel_left]
end DedekindZetaZeroFree.FourierContinuation.CurrentRawArchCenter

end

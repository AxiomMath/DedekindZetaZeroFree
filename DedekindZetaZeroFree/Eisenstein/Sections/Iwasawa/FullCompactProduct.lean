module

public import DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalOfKP

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def archimedeanSectionSet (w : InfinitePlace F) :
    Set (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) :=
  {x | ∃ k : KPCplxCharacterHaar.ComplexSU2,
    x = KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
      (Matrix.GeneralLinearGroup.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom
        (KPCplxCharacterHaar.complexSU2Embedding k))}

def archimedeanLocalCompact (w : InfinitePlace F) :
    Subgroup (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) :=
  Subgroup.closure (archimedeanSectionSet F ζ hζ w)

def localCompactFactor (v : KPHilbert.Place F) :
    Subgroup (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
  match v with
  | Sum.inl w => archimedeanLocalCompact F ζ hζ w
  | Sum.inr q => KPAdelicCoverRestrictedProduct.finiteCompact F ζ hζ q

def fullCompactPreimage :
    Subgroup (KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) where
  carrier := {x | ∀ v, x v ∈ localCompactFactor F ζ hζ v}
  mul_mem' := by
    intro x y hx hy v
    rw [RestrictedProduct.mul_apply]
    exact (localCompactFactor F ζ hζ v).mul_mem (hx v) (hy v)
  one_mem' := by
    intro v
    rw [RestrictedProduct.one_apply]
    exact (localCompactFactor F ζ hζ v).one_mem
  inv_mem' := by
    intro x hx v
    rw [RestrictedProduct.inv_apply]
    exact (localCompactFactor F ζ hζ v).inv_mem (hx v)

def iwasawaCompactSubgroupFull : Subgroup (KPLiteralRaw.G F ζ hζ) :=
  (fullCompactPreimage F ζ hζ).map
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))

theorem complexCompactLift_mem_iwasawaCompactSubgroupFull (w : InfinitePlace F)
    (k : KPCplxCharacterHaar.ComplexSU2) :
    KPGlobalResidualConstruction.complexCompactLift F ζ hζ w k ∈
      iwasawaCompactSubgroupFull F ζ hζ := by
  refine Subgroup.mem_map.mpr ⟨
    KPAdelicCoverRestrictedProduct.localToRestricted F ζ hζ (Sum.inl w)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
        (Matrix.GeneralLinearGroup.map
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom
          (KPCplxCharacterHaar.complexSU2Embedding k))), ?_, ?_⟩
  · intro v
    rw [KPAdelicCoverRestrictedProduct.localToRestricted,
      RestrictedProduct.mulSingleMonoidHom_apply,
      RestrictedProduct.coe_mulSingle_apply]
    rcases eq_or_ne v (Sum.inl w) with rfl | hne
    · rw [Pi.mulSingle_eq_same]
      exact Subgroup.subset_closure ⟨k, rfl⟩
    · rw [Pi.mulSingle_eq_of_ne hne]
      exact (localCompactFactor F ζ hζ v).one_mem
  · rfl

end DedekindZetaZeroFree.PrincipalOfKP

end

module

public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.FullCompactProduct

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalOfKP

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance instCubicRawTopArch (v : KPHilbert.Place F) :
    TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
  KPAdelicCoverRestrictedProduct.localTopology F ζ hζ v

 def archSectionHom (w : InfinitePlace F) :
    KPCplxCharacterHaar.ComplexSU2 →*
      KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) where
  toFun k := KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
    (Matrix.GeneralLinearGroup.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom
      (KPCplxCharacterHaar.complexSU2Embedding k))
  map_one' := by simp [KPLocalCover.sectionMap]; rfl
  map_mul' k l := by
    change KPLocalCover.CubicGL2Raw.mk _ 1 = KPLocalCover.CubicGL2Raw.mk _ _
    congr 1
    · simp only [map_mul, KPLocalCover.sectionMap_g]
    · simp [KPLocalChartTopology.complex_sigmaTwo_eq_one]

private theorem archSectionHom_continuous (w : InfinitePlace F) :
    Continuous (archSectionHom F ζ hζ w) := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  change @Continuous _ _ _ (TopologicalSpace.induced
    (KPLocalChartTopology.complexCoordinates F ζ hζ w) _) _
  apply continuous_induced_rng.mpr
  have he := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)).symm.continuous
  have hc : Continuous (fun k : KPCplxCharacterHaar.ComplexSU2 =>
      Matrix.GeneralLinearGroup.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom
        (KPCplxCharacterHaar.complexSU2Embedding k)) := by
    apply Units.continuous_iff.mpr
    constructor
    · apply continuous_pi; intro i; apply continuous_pi; intro j
      exact he.comp ((continuous_apply j).comp
        ((continuous_apply i).comp continuous_subtype_val))
    · apply continuous_pi; intro i; apply continuous_pi; intro j
      have hi (k : KPCplxCharacterHaar.ComplexSU2) :
          (↑(KPCplxCharacterHaar.complexSU2Embedding k)⁻¹ :
            Matrix (Fin 2) (Fin 2) ℂ) = star k.val := by
        rw [← map_inv]
        rfl
      change Continuous (fun k : KPCplxCharacterHaar.ComplexSU2 =>
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm
          ((↑(KPCplxCharacterHaar.complexSU2Embedding k)⁻¹ :
            Matrix (Fin 2) (Fin 2) ℂ) i j))
      simp_rw [hi]
      change Continuous (fun k : KPCplxCharacterHaar.ComplexSU2 =>
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm (star (k.val j i)))
      have hij : Continuous (fun k : KPCplxCharacterHaar.ComplexSU2 => k.val j i) :=
        (continuous_apply i).comp ((continuous_apply j).comp continuous_subtype_val)
      exact he.comp hij.star
  exact hc.prodMk continuous_const

theorem archimedeanLocalCompact_compact (w : InfinitePlace F) :
    IsCompact (archimedeanLocalCompact F ζ hζ w :
      Set (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w))) := by
  have hset : archimedeanSectionSet F ζ hζ w =
      ((archSectionHom F ζ hζ w).range : Set _) := by
    rw [MonoidHom.coe_range]
    ext x
    exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩
  rw [archimedeanLocalCompact, hset, Subgroup.closure_eq, MonoidHom.coe_range]
  letI : CompactSpace KPCplxCharacterHaar.ComplexSU2 := by
    apply isCompact_iff_compactSpace.mp
    convert KPCplxCharacterHaar.complexSU2_isCompact using 1
    exact Subtype.range_coe.symm
  exact isCompact_range (archSectionHom_continuous F ζ hζ w)

end DedekindZetaZeroFree.PrincipalOfKP

end

module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicMaximalCompactSubgroup
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Iwasawa.IntegralCompactSubgroup

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField
open scoped Classical NumberField Topology
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

local instance rawTopology (R : PrincipalMellin.ActualRecipe S η) (v : KPHilbert.Place F) :
    TopologicalSpace (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 v) :=
  KPAdelicCoverRestrictedProduct.localTopology F R.A.zeta12 R.A.primitive_zeta12 v

 def archSectionHom (R : PrincipalMellin.ActualRecipe S η) (w : InfinitePlace F) :
    KPCplxCharacterHaar.ComplexSU2 →*
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) where
  toFun k := KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
    (Matrix.GeneralLinearGroup.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).symm.toRingHom
      (KPCplxCharacterHaar.complexSU2Embedding k))
  map_one' := by simp [KPLocalCover.sectionMap]; rfl
  map_mul' k l := by
    change KPLocalCover.CubicGL2Raw.mk _ 1 = KPLocalCover.CubicGL2Raw.mk _ _
    congr 1
    · simp only [map_mul, KPLocalCover.sectionMap_g]
    · simp [KPLocalChartTopology.complex_sigmaTwo_eq_one]

private theorem archSectionHom_continuous (R : PrincipalMellin.ActualRecipe S η)
    (w : InfinitePlace F) : Continuous (archSectionHom R w) := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  change @Continuous _ _ _ (TopologicalSpace.induced
    (KPLocalChartTopology.complexCoordinates F R.A.zeta12 R.A.primitive_zeta12 w) _) _
  apply continuous_induced_rng.mpr
  have he := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).symm.continuous
  have hc : Continuous (fun k : KPCplxCharacterHaar.ComplexSU2 =>
      Matrix.GeneralLinearGroup.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).symm.toRingHom
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
          (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).symm
          ((↑(KPCplxCharacterHaar.complexSU2Embedding k)⁻¹ :
            Matrix (Fin 2) (Fin 2) ℂ) i j))
      simp_rw [hi]
      change Continuous (fun k : KPCplxCharacterHaar.ComplexSU2 =>
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).symm (star (k.val j i)))
      have hij : Continuous (fun k : KPCplxCharacterHaar.ComplexSU2 => k.val j i) :=
        (continuous_apply i).comp ((continuous_apply j).comp continuous_subtype_val)
      exact he.comp hij.star
  exact hc.prodMk continuous_const

theorem complex_su2_compact_is_compact (R : PrincipalMellin.ActualRecipe S η) (w : InfinitePlace F) :
    IsCompact (complexSU2Compact R w :
      Set (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w))) := by
  have hset : {x | ∃ k : KPCplxCharacterHaar.ComplexSU2,
      x = archSectionHom R w k} = ((archSectionHom R w).range : Set _) := by
    rw [MonoidHom.coe_range]
    ext x
    exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩
  change IsCompact (↑(Subgroup.closure {x | ∃ k, x = archSectionHom R w k}) :
    Set (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)))
  rw [hset, Subgroup.closure_eq, MonoidHom.coe_range]
  letI : CompactSpace KPCplxCharacterHaar.ComplexSU2 := by
    apply isCompact_iff_compactSpace.mp
    convert KPCplxCharacterHaar.complexSU2_isCompact using 1
    exact Subtype.range_coe.symm
  exact isCompact_range (archSectionHom_continuous R w)

theorem iwasawa_compact_factor_is_compact (R : PrincipalMellin.ActualRecipe S η) (v : KPHilbert.Place F) :
    IsCompact (iwasawaCompactFactor R v :
      Set (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 v)) := by
  cases v with
  | inl w => exact complex_su2_compact_is_compact R w
  | inr q =>
    dsimp only [iwasawaCompactFactor]
    split_ifs with hb
    · exact (PrincipalOfKP.integralRawCompact_compact_open F R.A.zeta12 R.A.primitive_zeta12 q).1
    · exact (KPAdelicCoverRestrictedProduct.finiteCompact_compact_open F R.A.zeta12 R.A.primitive_zeta12 q).1

theorem full_product_compact_preimage_is_compact (R : PrincipalMellin.ActualRecipe S η) :
    IsCompact (fullProductCompactPreimage R :
      Set (KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)) := by
  let A' : (v : KPHilbert.Place F) → Set (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 v) :=
    fun v => (iwasawaCompactFactor R v : Set _)
  let A : (v : KPHilbert.Place F) → Set (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 v) :=
    fun v => (KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 v : Set _)
  have hle : ∀ᶠ v in Filter.cofinite, A' v ⊆ A v := by
    filter_upwards [iwasawa_compact_factor_eq_arithmetic_compact_eventually R] with v hv
    dsimp only [A', A]
    rw [hv]
  haveI hcp : ∀ v, CompactSpace (A' v) := fun v => isCompact_iff_compactSpace.mp
    (iwasawa_compact_factor_is_compact R v)
  let inc := RestrictedProduct.mapAlong
      (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12)
      (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12) (𝓕₁ := Filter.cofinite) (𝓕₂ := Filter.cofinite)
      id Filter.tendsto_id
      (fun v => (id : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 v →
        KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 v)) hle
  have hcont : Continuous inc :=
    RestrictedProduct.mapAlong_continuous _ _ _ _ _ _ (fun v => continuous_id)
  have hstr : IsCompact (Set.range (RestrictedProduct.structureMap
      (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12) A' Filter.cofinite)) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image
      (RestrictedProduct.isEmbedding_structureMap (R := KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12)
        (A := A') (𝓕 := Filter.cofinite)).continuous
  have himg : inc '' Set.range (RestrictedProduct.structureMap
      (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12) A' Filter.cofinite) =
      (fullProductCompactPreimage R : Set (KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)) := by
    ext y
    rw [Set.mem_image, RestrictedProduct.range_structureMap]
    constructor
    · rintro ⟨x,hx,rfl⟩ v
      change (inc x) v ∈ iwasawaCompactFactor R v
      dsimp only [inc]
      rw [RestrictedProduct.mapAlong_apply]
      exact hx v
    · intro hy
      refine ⟨⟨fun v => y v, Filter.Eventually.of_forall hy⟩, hy, ?_⟩
      apply RestrictedProduct.ext
      intro v
      simp only [inc, RestrictedProduct.mapAlong_apply, id_eq, RestrictedProduct.mk_apply]
  rw [← himg]
  exact hstr.image hcont

theorem full_product_compact_is_compact (R : PrincipalMellin.ActualRecipe S η) :
    IsCompact (fullProductCompact R : Set (Group R)) := by
  rw [fullProductCompact, Subgroup.coe_map]
  exact (full_product_compact_preimage_is_compact R).image
    ((QuotientGroup.continuous_mk).comp QuotientGroup.continuous_mk)

end DedekindZetaZeroFree.ThetaExpansion

end

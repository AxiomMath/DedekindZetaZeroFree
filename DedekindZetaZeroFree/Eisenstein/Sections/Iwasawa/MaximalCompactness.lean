module

public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.CompactProductContinuity
public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.MaximalCompactProduct
public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.ArchimedeanCompactFactor
public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.FiniteCompactFactor

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalOfKP

set_option backward.isDefEq.respectTransparency false
open KPAdelicCoverRestrictedProduct

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance rawTopologyMax (v : KPHilbert.Place F) :
    TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
  KPAdelicCoverRestrictedProduct.localTopology F ζ hζ v

theorem localCompactFactorMax_isCompact (v : KPHilbert.Place F) :
    IsCompact (localCompactFactorMax F ζ hζ v :
      Set (KPLocalCover.CubicGL2Raw F ζ hζ v)) := by
  cases v with
  | inl w => exact archimedeanLocalCompact_compact F ζ hζ w
  | inr q =>
    dsimp only [localCompactFactorMax]
    split_ifs with hb
    · exact (integralRawCompact_compact_open F ζ hζ q).1
    · exact localCompactFactor_compact_finite F ζ hζ q

theorem fullCompactPreimageMax_isCompact :
    IsCompact (fullCompactPreimageMax F ζ hζ :
      Set (KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)) := by
  let A' : (v : KPHilbert.Place F) → Set (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
    fun v => (localCompactFactorMax F ζ hζ v : Set _)
  let A : (v : KPHilbert.Place F) → Set (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
    fun v => (KPAdelicCoverRestrictedProduct.compact F ζ hζ v : Set _)
  have hle : ∀ᶠ v in Filter.cofinite, A' v ⊆ A v := by
    filter_upwards [localCompactFactorMax_eq_compact_eventually F ζ hζ] with v hv
    dsimp only [A', A]
    rw [hv]
  haveI hcp : ∀ v, CompactSpace (A' v) := fun v => isCompact_iff_compactSpace.mp
    (localCompactFactorMax_isCompact F ζ hζ v)
  let inc := RestrictedProduct.mapAlong
      (KPLocalCover.CubicGL2Raw F ζ hζ)
      (KPLocalCover.CubicGL2Raw F ζ hζ) (𝓕₁ := Filter.cofinite) (𝓕₂ := Filter.cofinite)
      id Filter.tendsto_id
      (fun v => (id : KPLocalCover.CubicGL2Raw F ζ hζ v → KPLocalCover.CubicGL2Raw F ζ hζ v)) hle
  have hcont : Continuous inc :=
    RestrictedProduct.mapAlong_continuous _ _ _ _ _ _ (fun v => continuous_id)
  have hstr : IsCompact (Set.range (RestrictedProduct.structureMap
      (KPLocalCover.CubicGL2Raw F ζ hζ) A' Filter.cofinite)) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image
      (RestrictedProduct.isEmbedding_structureMap (R := KPLocalCover.CubicGL2Raw F ζ hζ)
        (A := A') (𝓕 := Filter.cofinite)).continuous
  have himg : inc '' Set.range (RestrictedProduct.structureMap
      (KPLocalCover.CubicGL2Raw F ζ hζ) A' Filter.cofinite) =
      (fullCompactPreimageMax F ζ hζ : Set (RestrictedCover F ζ hζ)) := by
    ext y
    rw [Set.mem_image, RestrictedProduct.range_structureMap]
    constructor
    · rintro ⟨x,hx,rfl⟩ v
      change (inc x) v ∈ localCompactFactorMax F ζ hζ v
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

theorem iwasawaCompactSubgroupMax_compact :
    IsCompact (iwasawaCompactSubgroupMax F ζ hζ : Set (KPLiteralRaw.G F ζ hζ)) := by
  rw [iwasawaCompactSubgroupMax, Subgroup.coe_map]
  exact (fullCompactPreimageMax_isCompact F ζ hζ).image
    (continuous_scalarQuotient_comp_amalgamation F ζ hζ)

end DedekindZetaZeroFree.PrincipalOfKP

end

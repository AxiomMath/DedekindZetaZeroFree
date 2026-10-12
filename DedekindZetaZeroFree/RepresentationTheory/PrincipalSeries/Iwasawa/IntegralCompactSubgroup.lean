module

public import DedekindZetaZeroFree.Metaplectic.Kubota.CubicLocalAndAdelicCovers
public import DedekindZetaZeroFree.Metaplectic.Kubota.RankOne.CartanDecomposition

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalOfKP
set_option linter.style.haveILetI false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
def integralRawCompact (q : HeightOneSpectrum (𝓞 F)) :
 Subgroup (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :=
 (KPTameCompact.inclusion F q).range.comap (KPLocalCover.projection F ζ hζ (Sum.inr q))
theorem finiteCompact_le_integralRawCompact (q : HeightOneSpectrum (𝓞 F)) :
 KPAdelicCoverRestrictedProduct.finiteCompact F ζ hζ q ≤ integralRawCompact F ζ hζ q := by
 intro r hr
 rw [KPAdelicCoverRestrictedProduct.finiteCompact] at hr
 split_ifs at hr with hb
 · obtain ⟨g,rfl⟩ := hr
   obtain ⟨k,hk,hkg⟩ := g.property
   exact ⟨k,hkg⟩
 · obtain ⟨k,rfl⟩ := hr
   exact ⟨k,rfl⟩
open _root_.DedekindZetaZeroFree.KPRankOneCartanGeometry renaming finite_kernel_proper → finite_kernel_proper
local instance rawTopology (q : HeightOneSpectrum (𝓞 F)) :
 TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :=
 KPAdelicCoverRestrictedProduct.localTopology F ζ hζ (Sum.inr q)
theorem integralRawCompact_compact_open (q : HeightOneSpectrum (𝓞 F)) :
 IsCompact (integralRawCompact F ζ hζ q : Set (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))) ∧ IsOpen (integralRawCompact F ζ hζ q : Set (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))) := by
 have ht := KPCubicCoverConstruction.local_topological_cover F ζ hζ (Sum.inr q)
 letI := ht.1
 letI := ht.2.2.1
 letI : ValuativeRel (KPTameCompact.K F q) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
 letI : IsNonarchimedeanLocalField (KPTameCompact.K F q) := ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
 letI : CompactSpace (KPTameCompact.O F q) := inferInstance
 letI : CompactSpace (Matrix (Fin 2) (Fin 2) (KPTameCompact.O F q)) := inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → KPTameCompact.O F q))
 letI : CompactSpace (KPTameCompact.K0 F q) := inferInstance
 have hi : Topology.IsOpenEmbedding (KPTameCompact.O F q).subtype :=
  (ValuativeRel.valuation (KPTameCompact.K F q)).isOpen_integer.isOpenEmbedding_subtypeVal
 have hc : Continuous (KPTameCompact.inclusion F q) := hi.continuous.generalLinearGroup_map
 have ho : IsOpenMap (KPTameCompact.inclusion F q) := Units.isOpenMap_map hi.matrix_map.injective hi.matrix_map.isOpenMap
 have hKc : IsCompact (Set.range (KPTameCompact.inclusion F q)) := isCompact_range hc
 have hKo : IsOpen (Set.range (KPTameCompact.inclusion F q)) := by
  rw [← Set.image_univ]; exact ho _ isOpen_univ
 have hf (y : KPLocalCover.LocalGL2 F (Sum.inr q)) :
  (KPLocalCover.projection F ζ hζ (Sum.inr q) ⁻¹' {y}).Finite := by
  change Set.Finite {r : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q) | KPLocalCover.projection F ζ hζ (Sum.inr q) r = y}
  haveI := Nat.finite_of_card_ne_zero (ht.2.2.2.2.2 y ▸ (by decide : (3 : ℕ) ≠ 0))
  exact Set.toFinite _
 have hp := finite_kernel_proper (KPLocalCover.projection F ζ hζ (Sum.inr q)) ht.2.2.2.1
  (fun y => ⟨⟨y,1⟩,rfl⟩) hf
 exact ⟨hp.isCompact_preimage hKc,hKo.preimage ht.2.2.2.1.continuous⟩

end DedekindZetaZeroFree.PrincipalOfKP

end

section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalOfKP
set_option linter.style.haveILetI false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open _root_.DedekindZetaZeroFree.KPRankOneCartanGeometry renaming finite_kernel_proper → finite_kernel_proper

local instance baseGroup (q : HeightOneSpectrum (𝓞 F)) : Group (KPPGLLocalCover.LocalPGL2 F (Sum.inr q)) :=
 @QuotientGroup.Quotient.group _ _ (KPPGLLocalCover.scalarSubgroup F (Sum.inr q))
  (KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q))
local instance scalarNormal (q : HeightOneSpectrum (𝓞 F)) : (KPPGLLocalCover.scalarSubgroup F (Sum.inr q)).Normal :=
 KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
theorem integralRawCompact_projection (q : HeightOneSpectrum (𝓞 F)) :
 (integralRawCompact F ζ hζ q).map (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)) =
 KPRankOneCartanGeometry.coveredK0 F ζ hζ q := by
 apply le_antisymm
 · rintro g ⟨r,hr,rfl⟩
   obtain ⟨k,hk⟩ := hr
   exact ⟨k, congrArg (KPPGLLocalCover.baseQuotient F (Sum.inr q)) hk⟩
 · intro g hg
   obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective (KPPGLLocalCover.splitScalarSubgroup F ζ hζ (Sum.inr q)) g
   obtain ⟨k,hk⟩ := hg
   change KPPGLLocalCover.baseQuotient F (Sum.inr q) (KPTameCompact.inclusion F q k) =
    KPPGLLocalCover.baseQuotient F (Sum.inr q) r.g at hk
   change QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _ at hk
   obtain ⟨z,⟨u,rfl⟩,hu⟩ := (QuotientGroup.mk'_eq_mk' _).mp hk
   let r' := r * (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) u)⁻¹
   refine ⟨r',?_,?_⟩
   · refine ⟨k,?_⟩
     change KPTameCompact.inclusion F q k = KPLocalCover.projection F ζ hζ (Sum.inr q) r'
     dsimp only [r']
     rw [map_mul,map_inv,KPScalarSplitCentral.projection_scalarHom]
     change KPTameCompact.inclusion F q k = r.g * (KPScalarSplitCentral.scalarMatrix F (Sum.inr q) u)⁻¹
     rw [← hu]
     simp
   · dsimp only [r']
     rw [map_mul,map_inv]
     have hs : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) u) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨u,rfl⟩
     rw [hs,inv_one,mul_one]
     rfl
end DedekindZetaZeroFree.PrincipalOfKP

end
end

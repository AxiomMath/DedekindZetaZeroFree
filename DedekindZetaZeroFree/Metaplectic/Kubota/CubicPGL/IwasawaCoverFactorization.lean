module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.LocalPGL.IntegralTriangularization

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ActualFiniteBorel.IwasawaProof
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
local instance : ValuativeRel (q.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F q
local instance : IsNonarchimedeanLocalField (q.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
local instance : Group (KPPGLLocalCover.LocalPGL2 F (Sum.inr q)) :=
  @QuotientGroup.Quotient.group _ _ (KPPGLLocalCover.scalarSubgroup F (Sum.inr q))
    (KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q))

theorem covered_factor (g : KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) :
    ∃ b : KPLocalSmoothRepresentation.Borel F ζ hζ q,
      ∃ k : KPRankOneCartanGeometry.coveredK0 F ζ hζ q,
        g = b.val * k.val := by
  obtain ⟨G, hG⟩ := QuotientGroup.mk_surjective
    (KPPGLLocalCover.projection F ζ hζ (Sum.inr q) g)
  obtain ⟨r, hr⟩ := triangularize F q G
  obtain ⟨k, hk⟩ := KPPGLLocalCover.projection_surjective F ζ hζ (Sum.inr q)
    (KPPGLLocalCover.baseQuotient F (Sum.inr q) (KPTameCompact.inclusion F q r⁻¹))
  have hkmem : k ∈ KPRankOneCartanGeometry.coveredK0 F ζ hζ q := by
    change KPPGLLocalCover.projection F ζ hζ (Sum.inr q) k ∈ KPRankOneCartanGeometry.K0 F q
    rw [hk]
    exact ⟨r⁻¹, rfl⟩
  have hb : g * k⁻¹ ∈ KPLocalSmoothRepresentation.Borel F ζ hζ q := by
    change KPLocalSmoothRepresentation.projection F ζ hζ q (g * k⁻¹) ∈
      KPRankOneInduction.upperBorel F q
    refine ⟨G * KPTameCompact.inclusion F q r, ?_, hr⟩
    change Matrix.ProjGenLinGroup.mk (G * KPTameCompact.inclusion F q r) =
      KPLocalSmoothRepresentation.ordinaryPGLMap F q
        (KPPGLLocalCover.projection F ζ hζ (Sum.inr q) (g * k⁻¹))
    rw [(KPPGLLocalCover.projection F ζ hζ (Sum.inr q)).map_mul,
      (KPPGLLocalCover.projection F ζ hζ (Sum.inr q)).map_inv, ← hG, hk,
      map_inv, map_inv, inv_inv]
    rfl
  refine ⟨⟨g * k⁻¹, hb⟩, ⟨k, hkmem⟩, ?_⟩
  simp

theorem covered_intersection (b : KPLocalSmoothRepresentation.Borel F ζ hζ q)
    (hb : b.val ∈ KPRankOneCartanGeometry.coveredK0 F ζ hζ q) :
    KPLocalPrincipalSeries.localAbs (q.adicCompletion F)
      (KPRankOneInduction.borelRatio F q
        ⟨KPLocalSmoothRepresentation.projection F ζ hζ q b.val, b.property⟩) = 1 := by
  obtain ⟨k, hk⟩ := hb
  apply integral_ratio F q _ k
  change Matrix.ProjGenLinGroup.mk (KPTameCompact.inclusion F q k) =
    KPLocalSmoothRepresentation.ordinaryPGLMap F q
      (KPPGLLocalCover.projection F ζ hζ (Sum.inr q) b.val)
  rw [← hk]
  rfl

end
end DedekindZetaZeroFree.ActualFiniteBorel.IwasawaProof

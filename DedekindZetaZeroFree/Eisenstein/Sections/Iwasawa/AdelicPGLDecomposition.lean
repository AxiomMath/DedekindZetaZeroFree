module

public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.MaximalCompactProduct
public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.ComplexDecomposition

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalOfKP

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem local_factor (v : KPHilbert.Place F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ v) :
    ∃ k : KPLocalCover.CubicGL2Raw F ζ hζ v,
      k ∈ localCompactFactorMax F ζ hζ v ∧ (g.g * k.g⁻¹) 1 0 = 0 := by
  cases v with
  | inl w =>
    obtain ⟨b,k,⟨A,hA,h10⟩,hk,hg⟩ := complexLocal_borel_compact F ζ hζ w g
    refine ⟨k,hk,?_⟩
    have he : g.g = b.g * k.g := congrArg KPLocalCover.CubicGL2Raw.g hg
    rw [he, mul_assoc, mul_inv_cancel, mul_one]
    change A = b.g at hA
    rw [← hA]
    exact h10
  | inr q =>
    obtain ⟨r,hr⟩ := ActualFiniteBorel.IwasawaProof.triangularize F q g.g
    by_cases hb : KPAdelicCoverRestrictedProduct.Bad F q
    · refine ⟨KPLocalCover.sectionMap F ζ hζ (Sum.inr q) (KPTameCompact.inclusion F q r⁻¹), ?_, ?_⟩
      · simp only [localCompactFactorMax, if_pos hb]
        exact ⟨r⁻¹,rfl⟩
      · simpa only [KPLocalCover.sectionMap_g, map_inv, inv_inv] using hr
    · let k := KPGoodCompactSplitting.kStar F ζ hζ q (fun h3 => hb (Or.inr h3)) r⁻¹
      refine ⟨k,?_,?_⟩
      · simp only [localCompactFactorMax, if_neg hb, KPAdelicCoverRestrictedProduct.finiteCompact]
        rw [dif_neg hb]
        exact ⟨r⁻¹,rfl⟩
      · have he : k.g = KPTameCompact.inclusion F q r⁻¹ := rfl
        rw [he, map_inv, inv_inv]
        exact hr

private theorem adele_ext {a b : KPAdelicCoverRestrictedProduct.Adeles F}
    (h : ∀ v, KPAdelicCoverRestrictedProduct.adeleEval F v a =
      KPAdelicCoverRestrictedProduct.adeleEval F v b) : a = b := by
  apply Prod.ext
  · funext w
    exact h (Sum.inl w)
  · apply RestrictedProduct.ext
    intro q
    exact h (Sum.inr q)

theorem base_pgl_iwasawa_max (g : KPAdelicCoverRestrictedProduct.AdelicPGL2 F) :
    ∃ b : KPGlobalTorusFunctionData.ordinaryBorel F,
      ∃ k : iwasawaCompactSubgroupMax F ζ hζ,
        g = b.val * KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ k.val := by
  obtain ⟨G,rfl⟩ := QuotientGroup.mk'_surjective (KPAdelicCoverRestrictedProduct.scalarSubgroup F) g
  obtain ⟨x,hx⟩ := KPAdelicCoverRestrictedProduct.restrictedProjection_surjective F ζ hζ G
  choose k hk ht using (fun v => local_factor F ζ hζ v (x v))
  let y : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ :=
    ⟨k, by
      filter_upwards [localCompactFactorMax_eq_compact_eventually F ζ hζ] with v hv
      rw [← hv]
      exact hk v⟩
  have hy : y ∈ fullCompactPreimageMax F ζ hζ := hk
  let K := (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ)
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ y)
  have hK : K ∈ iwasawaCompactSubgroupMax F ζ hζ := ⟨y,hy,rfl⟩
  let B := G * (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ y)⁻¹
  have hB : B 1 0 = 0 := by
    apply adele_ext F
    intro v
    change (KPAdelicCoverRestrictedProduct.matrixEval F v B) 1 0 =
      KPAdelicCoverRestrictedProduct.adeleEval F v 0
    dsimp only [B]
    rw [map_mul, map_inv,
      KPAdelicCoverRestrictedProduct.restrictedProjection_eval]
    rw [← hx, KPAdelicCoverRestrictedProduct.restrictedProjection_eval]
    simpa only [KPLocalCover.projection_apply, map_zero, y, RestrictedProduct.mk_apply] using ht v
  refine ⟨⟨QuotientGroup.mk' _ B,⟨B,rfl,hB⟩⟩,⟨K,hK⟩,?_⟩
  change QuotientGroup.mk' _ G = QuotientGroup.mk' _ B *
    QuotientGroup.mk' _ (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ y)
  rw [← map_mul]
  congr 1
  simp only [B, mul_assoc, inv_mul_cancel, mul_one]

end DedekindZetaZeroFree.PrincipalOfKP

end

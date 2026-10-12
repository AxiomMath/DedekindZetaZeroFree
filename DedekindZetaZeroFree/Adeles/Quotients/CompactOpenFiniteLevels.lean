module

public import DedekindZetaZeroFree.Eisenstein.Sections.CanonicalFlatFamily
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ScalarRealizationClosure

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPCompactFiniteLevel
open KPAdelicCoverRestrictedProduct
attribute [local instance] KPAdelicCoverRestrictedProduct.pglLocalTopology
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def standardData : ActualFiniteFactor.ProductLevelData F ζ hζ :=
  ⟨fun q => ⟨⟨pglCompact F ζ hζ (Sum.inr q), (ActualFiniteFactor.pgl_standard_compact_open F ζ hζ q).2⟩,
    (ActualFiniteFactor.pgl_standard_compact_open F ζ hζ q).1⟩, Filter.Eventually.of_forall fun _ => rfl⟩

private theorem standard_mem_compact
    (u : ActualFiniteFactor.finiteSubgroup F ζ hζ)
    (hu : u ∈ (ActualFiniteFactor.productLevel F ζ hζ (standardData F ζ hζ)).subgroup) :
    u.val ∈ (KPContFlatSourceRecipe.D F ζ hζ).K := by
  obtain ⟨x, hx, hq, he⟩ := (ActualFiniteFactor.productLevel_rule F ζ hζ _ u).mp hu
  have hlift (q : HeightOneSpectrum (𝓞 F)) :
      ∃ y ∈ finiteCompact F ζ hζ q,
        KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) y =
          KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (x (Sum.inr q)) := by
    exact hq q
  choose y hy hyq using hlift
  let z : RestrictedCover F ζ hζ := ⟨fun v => match v with
    | Sum.inl _ => 1 | Sum.inr q => y q,
    Filter.Eventually.of_forall (fun v => by
      cases v with
      | inl w => exact Subgroup.one_mem _
      | inr q => exact hy q)⟩
  have hz : z ∈ PrincipalOfKP.fullCompactPreimage F ζ hζ := by
    intro v
    cases v with
    | inl w => exact Subgroup.one_mem _
    | inr q => exact hy q
  have hzx : restrictedPGLQuotient F ζ hζ z = restrictedPGLQuotient F ζ hζ x := by
    ext v
    cases v with
    | inl w =>
        change (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)) 1 =
          (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)) (x (Sum.inl w))
        rw [hx w]
    | inr q => exact hyq q
  obtain ⟨e, _, _, herule⟩ := scalar_quotient_commutes_with_amalgamation F ζ hζ
  have heq : scalarQuotient F ζ hζ (amalgamation F ζ hζ z) = u.val := by
    rw [← he]
    apply e.injective
    rw [herule, herule, hzx]
  exact Subgroup.mem_map.mpr ⟨z,
    PrincipalOfKP.fullCompactPreimage_le_max F ζ hζ hz, heq⟩

theorem exists_level :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤ (KPContFlatSourceRecipe.D F ζ hζ).K := by
  have hfinite : ActualFiniteFactor.finiteSubgroup F ζ hζ =
      KPGlobalTorusFunctionData.finitePart F ζ hζ := by
    rw [ActualFiniteFactor.finiteSubgroup_eq_tupleFactor]
    congr 1
    ext x
    simp [PGLComplex.AdelicSlicesRaw.finiteSubgroup,
      PGLComplex.AdelicSlicesRaw.finiteTuples,
      KPGlobalTorusFunctionData.finitePart, Subgroup.mem_iInf]
  have h : ∃ U : CompactOpenLevel (ActualFiniteFactor.finiteSubgroup F ζ hζ),
      U.toOpenSubgroup.toSubgroup.map (ActualFiniteFactor.finiteSubgroup F ζ hζ).subtype ≤
        (KPContFlatSourceRecipe.D F ζ hζ).K := by
    let P := ActualFiniteFactor.productLevel F ζ hζ (standardData F ζ hζ)
    refine ⟨⟨P.subgroup, P.compact⟩, ?_⟩
    rintro a ⟨u, hu, rfl⟩
    exact standard_mem_compact F ζ hζ u hu
  rw [hfinite] at h
  exact h
end DedekindZetaZeroFree.KPCompactFiniteLevel

end

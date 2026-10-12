module

public import DedekindZetaZeroFree.Eisenstein.Induction.CompactInvariance
public import DedekindZetaZeroFree.Eisenstein.Induction.ArchimedeanSectionSmoothness

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 200000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.SourceKFinite
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "f" => RawSource.scalarValue F ζ hζ P C
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology

 theorem finite_translate_locallyConstant : IsLocallyConstant
    (fun b : KPGlobalTorusFunctionData.finitePart F ζ hζ => KPLiteralRaw.rightAction F ζ hζ b.val f) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro b
  let U := SourceLevels.level F ζ hζ P C
  have hc : Continuous (fun y : KPGlobalTorusFunctionData.finitePart F ζ hζ => b⁻¹*y) :=
    continuous_const.mul continuous_id
  have he : ∀ᶠ y in nhds b, b⁻¹*y ∈ U.toOpenSubgroup :=
    hc.continuousAt.preimage_mem_nhds (by simpa using U.toOpenSubgroup.isOpen.mem_nhds U.toOpenSubgroup.one_mem)
  filter_upwards [he] with y hy
  funext g
  have hmem : (b⁻¹*y).val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U :=
    Subgroup.mem_map.mpr ⟨b⁻¹*y, hy, rfl⟩
  have hf := SourceLevels.scalar_fixed F ζ hζ P C (g*b.val) (b⁻¹*y).val hmem
  simpa [KPLiteralRaw.rightAction, mul_assoc] using hf

 theorem compact_translate_finite (k : RestrictedCover F ζ hζ)
    (hk : k ∈ ThetaExpansion.fullProductCompactPreimage R) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    f (g * scalarQuotient F ζ hζ (amalgamation F ζ hζ k)) =
      f (g * (FiniteSourceTopology.finiteQuotient F ζ hζ k).val) := by
  let b := FiniteSourceTopology.finiteProjection F ζ hζ k
  let a : RestrictedCover F ζ hζ := k * b⁻¹
  have hsplit : k = b*a := by
    apply RestrictedProduct.ext
    intro v
    cases v with
    | inl w => change k (Sum.inl w) = 1*(k (Sum.inl w)*1⁻¹); simp
    | inr q => change k (Sum.inr q) = k (Sum.inr q)*(k (Sum.inr q)*(k (Sum.inr q))⁻¹); simp
  have ha : ∀ q, a (Sum.inr q) = 1 := by intro q; change k (Sum.inr q)*(k (Sum.inr q))⁻¹ = 1; simp
  have hc : ∀ w, a (Sum.inl w) ∈ ThetaExpansion.complexSU2Compact R w := by
    intro w
    change k (Sum.inl w)*1⁻¹ ∈ _
    simpa [ThetaExpansion.iwasawaCompactFactor] using hk (Sum.inl w)
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g =>
      change f (scalarQuotient F ζ hζ (amalgamation F ζ hζ g) *
        scalarQuotient F ζ hζ (amalgamation F ζ hζ k)) =
          f (scalarQuotient F ζ hζ (amalgamation F ζ hζ g) *
            scalarQuotient F ζ hζ (amalgamation F ζ hζ b))
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
      unfold RawSource.scalarValue
      rw [RawSource.quotientValue_raw, RawSource.quotientValue_raw, hsplit, ← mul_assoc,
        CompactSource.value_right_arch R P C (g*b) a ha hc]

 theorem orbit_finite : (Set.range (fun k : ThetaExpansion.fullProductCompact R =>
    KPLiteralRaw.rightAction F ζ hζ k.val f)).Finite := by
  let J : Set (KPGlobalTorusFunctionData.finitePart F ζ hζ) :=
    FiniteSourceTopology.finiteQuotient F ζ hζ '' (ThetaExpansion.fullProductCompactPreimage R : Set _)
  have hJ : IsCompact J := (ThetaExpansion.full_product_compact_preimage_is_compact R).image
    (FiniteSourceTopology.finiteQuotient_continuous F ζ hζ)
  letI : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  have hfin : (Set.range (fun b : J => KPLiteralRaw.rightAction F ζ hζ b.val.val f)).Finite :=
    ((finite_translate_locallyConstant R P C).comp_continuous continuous_subtype_val).range_finite
  apply hfin.subset
  rintro _ ⟨k, rfl⟩
  obtain ⟨u, hu, he⟩ := k.property
  refine ⟨⟨FiniteSourceTopology.finiteQuotient F ζ hζ u, ⟨u, hu, rfl⟩⟩, ?_⟩
  funext g
  change f (g * (FiniteSourceTopology.finiteQuotient F ζ hζ u).val) = f (g*k.val)
  rw [← he]
  exact (compact_translate_finite R P C u hu g).symm

 theorem scalar_kfinite : KPLiteralRaw.KFinite F ζ hζ (ThetaExpansion.fullProductCompact R) f := by
  let O := Set.range (fun k : ThetaExpansion.fullProductCompact R => KPLiteralRaw.rightAction F ζ hζ k.val f)
  let W := Submodule.span ℂ O
  have hfin : Module.Finite ℂ W := Module.Finite.of_fg (Submodule.fg_span (orbit_finite R P C))
  refine ⟨W, hfin, ?_, ?_⟩
  · have h : KPLiteralRaw.rightAction F ζ hζ (1 : ThetaExpansion.fullProductCompact R).val f ∈ W :=
      Submodule.subset_span ⟨1, rfl⟩
    simpa using h
  · intro k v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      apply Submodule.subset_span
      refine ⟨k*l, ?_⟩
      change KPLiteralRaw.rightAction F ζ hζ (k.val*l.val) f =
        KPLiteralRaw.rightAction F ζ hζ k.val (KPLiteralRaw.rightAction F ζ hζ l.val f)
      rw [map_mul, Module.End.mul_apply]
    | zero => simpa using W.zero_mem
    | add x y hx hy hix hiy => simpa using W.add_mem hix hiy
    | smul c x hx hi => simpa using W.smul_mem c hi

end DedekindZetaZeroFree.EisensteinReferenceSections.SourceKFinite

end

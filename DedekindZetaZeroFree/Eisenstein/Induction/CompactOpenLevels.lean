module

public import DedekindZetaZeroFree.Eisenstein.Induction.AdelicSectionDescent
public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicMaximalCompactSubgroup

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.SourceLevels
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
attribute [local instance] KPAdelicCoverRestrictedProduct.pglLocalTopology

theorem finite_eq : ActualFiniteFactor.finiteSubgroup F ζ hζ =
    KPGlobalTorusFunctionData.finitePart F ζ hζ := by
  rw [ActualFiniteFactor.finiteSubgroup_eq_tupleFactor]
  unfold ActualFiniteFactor.tupleFactor PGLComplex.AdelicSlicesRaw.finiteSubgroup
    KPGlobalTorusFunctionData.finitePart
  congr 1
  ext x
  simp [PGLComplex.AdelicSlicesRaw.finiteTuples, Subgroup.mem_iInf]

def refined : ActualFiniteFactor.ProductLevelData F ζ hζ where
  localLevel q :=
    ⟨(FiniteLevels.localLevel F ζ hζ P C q).toOpenSubgroup ⊓
      ⟨pglCompact F ζ hζ (Sum.inr q),
        (ActualFiniteFactor.pgl_standard_compact_open F ζ hζ q).2⟩,
      (FiniteLevels.localLevel F ζ hζ P C q).isCompact.inter_right
        (Subgroup.isClosed_of_isOpen _
          (ActualFiniteFactor.pgl_standard_compact_open F ζ hζ q).2)⟩
  cofinally_standard := by
    filter_upwards [FiniteLevels.localLevel_standard F ζ hζ P C] with q hq
    change (FiniteLevels.localLevel F ζ hζ P C q).toOpenSubgroup.toSubgroup ⊓
      pglCompact F ζ hζ (Sum.inr q) = _
    rw [hq, inf_idem]

theorem refined_le : ActualFiniteFactor.productSubgroup F ζ hζ (refined F ζ hζ P C) ≤
    ActualFiniteFactor.productSubgroup F ζ hζ (FiniteLevels.productLevel F ζ hζ P C) := by
  apply Subgroup.map_mono
  intro x hx
  refine ⟨hx.1, Subgroup.mem_iInf.mpr (fun q => ?_)⟩
  exact ((Subgroup.mem_iInf.mp hx.2) q).1

variable {F ζ hζ}
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem refined_compact_le (R : PrincipalMellin.ActualRecipe S η)
    (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
    (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P) :
    ActualFiniteFactor.productSubgroup F R.A.zeta12 R.A.primitive_zeta12
      (refined F R.A.zeta12 R.A.primitive_zeta12 P C) ≤ ThetaExpansion.fullProductCompact R := by
  intro u hu
  obtain ⟨x, hx, hxu⟩ := hu
  have hq (q : HeightOneSpectrum (𝓞 F)) :
      KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
        (x (Sum.inr q)) ∈ pglCompact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) :=
    ((Subgroup.mem_iInf.mp hx.2) q).2
  choose y hy he using hq
  let raw : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 :=
    ⟨fun v => match v with | Sum.inl _ => 1 | Sum.inr q => y q,
      Filter.Eventually.of_forall (by intro v; cases v with
        | inl w => trivial
        | inr q => exact hy q)⟩
  refine Subgroup.mem_map.mpr ⟨raw, ?_, ?_⟩
  · intro v
    cases v with
    | inl w => exact Subgroup.one_mem _
    | inr q => exact ThetaExpansion.finite_compact_le_iwasawa_compact_factor R q (hy q)
  · change scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (amalgamation F R.A.zeta12 R.A.primitive_zeta12 raw) = u
    change scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (amalgamation F R.A.zeta12 R.A.primitive_zeta12 x) = u at hxu
    rw [← hxu]
    obtain ⟨e, _, _, herule⟩ := scalar_quotient_commutes_with_amalgamation
      F R.A.zeta12 R.A.primitive_zeta12
    apply e.injective
    rw [herule, herule]
    congr 1
    ext v
    cases v with
    | inl w =>
      change KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) 1 =
        KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) (x (Sum.inl w))
      rw [hx.1 w]
    | inr q => exact he q

variable (F ζ hζ)

def level : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ := by
  let J := ActualFiniteFactor.productSubgroup F ζ hζ (refined F ζ hζ P C)
  have hc := ActualFiniteFactor.productSubgroup_compact_open F ζ hζ (refined F ζ hζ P C)
  rw [finite_eq F ζ hζ] at hc
  exact ⟨⟨J.comap (KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype, hc.2⟩, hc.1⟩

theorem globalLevel_eq : KPGlobalTorusFunctionData.globalLevel F ζ hζ (level F ζ hζ P C) =
    ActualFiniteFactor.productSubgroup F ζ hζ (refined F ζ hζ P C) := by
  change ((ActualFiniteFactor.productSubgroup F ζ hζ (refined F ζ hζ P C)).comap
      (KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype).map
        (KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype = _
  rw [Subgroup.map_comap_eq]
  apply inf_eq_right.mpr
  rw [Subgroup.range_subtype, ← finite_eq F ζ hζ]
  exact ActualFiniteFactor.productSubgroup_le_finite F ζ hζ _

theorem scalar_fixed (g u : KPGlobalTorusFunctionData.G F ζ hζ)
    (hu : u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ (level F ζ hζ P C)) :
    RawSource.scalarValue F ζ hζ P C (g * u) = RawSource.scalarValue F ζ hζ P C g := by
  rw [globalLevel_eq] at hu
  exact RawSource.scalarValue_right_product F ζ hζ P C g u (refined_le F ζ hζ P C hu)

end DedekindZetaZeroFree.EisensteinReferenceSections.SourceLevels

end

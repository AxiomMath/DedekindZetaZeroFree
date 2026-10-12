module

public import DedekindZetaZeroFree.Eisenstein.Induction.CompactOpenLevels

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.FiniteSourceTopology
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

 def finiteProjection : RestrictedCover F ζ hζ →* RestrictedCover F ζ hζ :=
  RestrictedProduct.mapAlongMonoidHom
    (KPLocalCover.CubicGL2Raw F ζ hζ) (KPLocalCover.CubicGL2Raw F ζ hζ)
    id Filter.tendsto_id
    (fun v => match v with | Sum.inl _ => 1 | Sum.inr _ => MonoidHom.id _)
    (Filter.Eventually.of_forall (by intro v a ha; cases v <;> simpa using ha))

 theorem finiteProjection_continuous : Continuous (finiteProjection F ζ hζ) := by
  unfold finiteProjection RestrictedProduct.mapAlongMonoidHom
  exact RestrictedProduct.mapAlong_continuous _ _ id Filter.tendsto_id _
    (Filter.Eventually.of_forall (by intro v a ha; cases v <;> simpa using ha))
    (fun v => by cases v <;> first | exact continuous_const | exact continuous_id)

 def finiteQuotient (g : RestrictedCover F ζ hζ) :
    KPGlobalTorusFunctionData.finitePart F ζ hζ :=
  ⟨scalarQuotient F ζ hζ (amalgamation F ζ hζ (finiteProjection F ζ hζ g)), by
    refine Subgroup.mem_map.mpr ⟨finiteProjection F ζ hζ g, ?_, rfl⟩
    simp only [Subgroup.mem_iInf, MonoidHom.mem_ker]
    intro w
    rfl⟩

 theorem finiteQuotient_continuous : Continuous (finiteQuotient F ζ hζ) := by
  exact ((QuotientGroup.continuous_mk.comp QuotientGroup.continuous_mk).comp
    (finiteProjection_continuous F ζ hζ)).subtype_mk _

 theorem finite_scalar_locallyConstant : IsLocallyConstant
    (fun g : KPGlobalTorusFunctionData.finitePart F ζ hζ => RawSource.scalarValue F ζ hζ P C g.val) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  let U := SourceLevels.level F ζ hζ P C
  have hc : Continuous (fun y : KPGlobalTorusFunctionData.finitePart F ζ hζ => g⁻¹*y) :=
    continuous_const.mul continuous_id
  have he : ∀ᶠ y in nhds g, g⁻¹*y ∈ U.toOpenSubgroup :=
    hc.continuousAt.preimage_mem_nhds (by simpa using U.toOpenSubgroup.isOpen.mem_nhds U.toOpenSubgroup.one_mem)
  filter_upwards [he] with y hy
  have hmem : (g⁻¹*y).val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U :=
    Subgroup.mem_map.mpr ⟨g⁻¹*y, hy, rfl⟩
  have hf := SourceLevels.scalar_fixed F ζ hζ P C g.val (g⁻¹*y).val hmem
  simpa using hf

 theorem finite_scalar_continuous : Continuous
    (fun g : KPGlobalTorusFunctionData.finitePart F ζ hζ => RawSource.scalarValue F ζ hζ P C g.val) :=
  (finite_scalar_locallyConstant F ζ hζ P C).continuous

 theorem value_factor (g : RestrictedCover F ζ hζ) :
    RawSource.value F ζ hζ P C g = RawSource.archProduct F ζ hζ g •
      RawSource.value F ζ hζ P C (finiteProjection F ζ hζ g) := by
  have ht : SourceTensor.evaluatedTensor F ζ hζ P C g =
      SourceTensor.evaluatedTensor F ζ hζ P C (finiteProjection F ζ hζ g) := by
    apply SourceTensor.evaluatedTensor_congr
    intro q
    rfl
  have ha : RawSource.archProduct F ζ hζ (finiteProjection F ζ hζ g) = 1 := by
    unfold RawSource.archProduct
    simp only [show ∀ w, (finiteProjection F ζ hζ g) (Sum.inl w) = 1 from fun _ => rfl,
      LocalCovariance.arch_one, Finset.prod_const_one]
  rw [RawSource.value, RawSource.value, ht, ha, one_smul]

 theorem scalar_raw_factor (g : RestrictedCover F ζ hζ) :
    RawSource.scalarValue F ζ hζ P C (scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) =
      RawSource.archProduct F ζ hζ g * RawSource.scalarValue F ζ hζ P C (finiteQuotient F ζ hζ g).val := by
  unfold RawSource.scalarValue
  rw [RawSource.quotientValue_raw, value_factor, map_smul]
  rfl

end DedekindZetaZeroFree.EisensteinReferenceSections.FiniteSourceTopology

end

module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicMaximalCompactness
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RationalPeriodization.NormalizedInduction

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

theorem scalarSource_finiteTranslate_locallyConstant (x : PlusCore R N P C) :
    IsLocallyConstant (fun b : KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12 =>
      KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 b.val (scalarSourceEvaluator R N P C x)) := by
  obtain ⟨U, hU⟩ := scalarSource_has_level R N P C x
  rw [IsLocallyConstant.iff_eventually_eq]
  intro b
  have hc : Continuous (fun y : KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12 => b⁻¹ * y) :=
    continuous_const.mul continuous_id
  have he : ∀ᶠ y in nhds b, b⁻¹ * y ∈ U.toOpenSubgroup :=
    hc.continuousAt.preimage_mem_nhds (by simpa using U.toOpenSubgroup.isOpen.mem_nhds U.toOpenSubgroup.one_mem)
  filter_upwards [he] with y hy
  funext g
  have hm : (b⁻¹ * y).val ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 U :=
    Subgroup.mem_map.mpr ⟨b⁻¹ * y, hy, rfl⟩
  simpa [KPLiteralRaw.rightAction, mul_assoc] using hU (g * b.val) (b⁻¹ * y).val hm

theorem finiteProjectionCompact : IsCompact
    (EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient F R.A.zeta12 R.A.primitive_zeta12 ''
      (ThetaExpansion.fullProductCompactPreimage R : Set _)) :=
  (ThetaExpansion.full_product_compact_preimage_is_compact R).image
    (EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient_continuous F R.A.zeta12 R.A.primitive_zeta12)

theorem scalarSource_finiteOrbit_finite (x : PlusCore R N P C) :
    (Set.range (fun b : EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient F R.A.zeta12 R.A.primitive_zeta12 ''
      (ThetaExpansion.fullProductCompactPreimage R : Set _) =>
        KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 b.val.val (scalarSourceEvaluator R N P C x))).Finite := by
  let J := EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient F R.A.zeta12 R.A.primitive_zeta12 ''
      (ThetaExpansion.fullProductCompactPreimage R : Set _)
  letI : CompactSpace J := isCompact_iff_compactSpace.mp (finiteProjectionCompact R)
  exact ((scalarSource_finiteTranslate_locallyConstant R N P C x).comp_continuous continuous_subtype_val).range_finite

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end

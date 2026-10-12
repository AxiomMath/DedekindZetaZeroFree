module

public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.WordCompactBounds

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open MomentSources KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12

include N in
theorem restrictedSlot_actual_word_compact_bound

    (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
    (x : ∀j : s.val, LiteralSource.Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val)
    (b : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))
    (K : Set (KPLiteralRaw.G F ζ hζ)) (hK : IsCompact K) :
    ∃orders : Finset ℕ, ∃B : ℝ, 0<B ∧ ∀v : complexCore, ∀g∈K,
      ‖KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ b
        (LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v)) g‖ ≤
        B*(orders.sup coreSeminorm) v := by
  letI : T2Space (KPLiteralRaw.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI : LocallyCompactSpace (KPLiteralRaw.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.1
  letI : IsTopologicalGroup (KPLiteralRaw.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨HR,_,_,HP,⟨HH⟩⟩ := kp_ms_fixed_haar_disintegration F ζ hζ
    (Measure.haar : Measure (KPLiteralRaw.G F ζ hζ)) inferInstance
  obtain ⟨M⟩ := exists_native_measured_source F ζ hζ HR HP
  obtain ⟨L⟩ := KPGlobalProductPolarizationCharacter.exists_compatible_local_data F ζ hζ
  obtain ⟨D,_⟩ := KPGlobalTorusFiniteStages.compatibleModelData_exists F ζ hζ L
  letI : CompactSpace compactSubgroup := isCompact_iff_compactSpace.mp compactSubgroup_isCompact
  let KD : TopologicalSpace.PositiveCompacts (KPMsGreenFlux.K F) :=
    ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩
  let dk := Measure.haarMeasure KD
  letI : IsProbabilityMeasure dk := ⟨Measure.haarMeasure_self⟩
  exact restrictedSlot_residue_word_compact_bound R N P C D HR HP M  dk s x w hw b K hK

include N in
theorem restrictedSlot_actual_compact_bound

    (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
    (x : ∀j : s.val, LiteralSource.Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val)
    (K : Set (KPLiteralRaw.G F ζ hζ)) (hK : IsCompact K) :
    ∃orders : Finset ℕ, ∃B : ℝ, 0<B ∧ ∀v : complexCore, ∀g∈K,
      ‖LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v) g‖ ≤
        B*(orders.sup coreSeminorm) v := by
  exact restrictedSlot_actual_word_compact_bound R N P C  s x w hw [] K hK
end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end

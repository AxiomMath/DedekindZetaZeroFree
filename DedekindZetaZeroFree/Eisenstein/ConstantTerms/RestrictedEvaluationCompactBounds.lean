module

public import DedekindZetaZeroFree.Eisenstein.Residues.UpperSlotBounds

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open MomentSources KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts
open CurrentRepairedLocalBinding
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

include N in
theorem restrictedSlot_upper_compact_bound
    (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
    (x : ∀ j : s.val, LiteralSource.Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (K : Set (LiteralSource.Raw R.A)) (hK : IsCompact K) :
    ∃ orders : Finset ℕ, ∃ B : ℝ≥0, B ≠ 0 ∧
      ∀ (v : complexCore) (a : LiteralSource.Raw R.A), a ∈ K →
        ‖∫ u : KPAdditiveQuotient F,
          LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v)
            (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out u) *
              KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
                (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 a))
          ∂KPWildKernelUpperBound.quotientHaar F‖ ≤
        B * (orders.sup coreSeminorm) v := by
  let sr : RestrictedTensorSimple.Level (FaithfulSource.RepairedInducing.bad R P C) :=
    ⟨s.val, by
      rw [show FaithfulSource.RepairedInducing.bad R P C = LiteralSource.bad R.A P C from
        PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.badSet_eq_fullBad
          F R.A.zeta12 R.A.primitive_zeta12 P C]
      exact s.property⟩
  have hs : sourceLevel R P C sr = s := Subtype.ext rfl
  have hpin (v : complexCore) :
      coreEquiv R N P C (sourceSlot R N P C sr x w hw v) =
        restrictedSlotTensor R.A P C s x w hw v := by
    unfold sourceSlot
    rw [coreEquiv_stage]
    change RestrictedTensorSimple.stageInclusion _ _ _ (sourceLevel R P C sr) _ =
      RestrictedTensorSimple.stageInclusion _ _ _ s _
    congr 1
  obtain ⟨orders,B,hB,hb⟩ := current_upper_residue_slot_bound R N P C sr x  w hw K hK
  refine ⟨orders,B,hB,?_⟩
  intro v a ha
  have hh := hb v a ha
  rw [hpin] at hh
  have he : (orders.sup coreSeminorm) v =
      (orders.sup (chartSeminorm negativeParameter)) v.val := by
    change (orders.sup (SeminormFamily.comp (chartSeminorm negativeParameter) complexCore.subtype)) v = _
    rw [← SeminormFamily.finset_sup_comp, Seminorm.comp_apply]
    rfl
  simpa only [he] using hh
end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end

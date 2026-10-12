module

public import DedekindZetaZeroFree.Theta.Periods.Wild.FiniteExteriorComparison

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly
open MomentSources WildCurrentReindex
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem exists_detected_stage (D : TensorDetected R N) (T : Finset (KPFinitePlace F)) :
    ∃s : RestrictedTensorSimple.Level D.bad, places T ⊆ s.val ∧
      ∃x : ∀p:s.val,actualLocal R D.finiteData p,
      coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0 := by
  obtain ⟨v,hv⟩ := D.detected
  obtain ⟨s,x,hs,hx⟩ := D.selected_frozen_stage v
  have hd : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0 := by
    change fourier R D.sources.dq
      (D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s (PiTensorProduct.tprod ℂ x))) 1 ≠ 0
    rw [←hx,D.selected_eq]
    exact hv
  let t : RestrictedTensorSimple.Level D.bad := ⟨s.val ∪ places T,s.property.trans Finset.subset_union_left⟩
  refine ⟨t,Finset.subset_union_right,extendTuple D.toTensorActions s t x,?_⟩
  rw [stage_extend D.toTensorActions s t Finset.subset_union_left x]
  exact hd

end DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly

end

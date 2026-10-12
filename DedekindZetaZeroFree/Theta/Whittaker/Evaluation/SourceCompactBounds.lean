module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.RestrictedSourceMatrixSmoothness

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

theorem restrictedSlot_source_compact_bound
    (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
    (x : ∀ j : s.val, LiteralSource.Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (K : Set (LiteralSource.Raw R.A)) (hK : IsCompact K) :
    ∃ orders : Finset ℕ, ∃ B : ℝ≥0, B ≠ 0 ∧
      ∀ (v : complexCore) (g : LiteralSource.Raw R.A), g ∈ K →
        ‖LiteralSource.rawCoreInsertion R.A P C
          (restrictedSlotTensor R.A P C s x w hw v) g‖ ≤ B * (orders.sup coreSeminorm) v := by
  obtain ⟨orders,B,hB,hb⟩ := wholeRawSlot_compact_bound R.A P C s x w hw K hK
  refine ⟨orders,B,hB,?_⟩
  intro v g hg
  have h := hb v.val g hg
  rw [wholeRawSlot_core R.A P C s x w hw g v] at h
  have he : (orders.sup coreSeminorm) v =
      (orders.sup (chartSeminorm negativeParameter)) v.val := by
    change (orders.sup (SeminormFamily.comp (chartSeminorm negativeParameter) complexCore.subtype)) v = _
    rw [←SeminormFamily.finset_sup_comp,Seminorm.comp_apply]
    rfl
  simpa only [he] using h
end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end

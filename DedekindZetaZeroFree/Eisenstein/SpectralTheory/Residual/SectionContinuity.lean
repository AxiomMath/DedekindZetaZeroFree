module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.TranslatedBigCellCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open KPCplxCharacterHaar KPAdelicCoverRestrictedProduct KPLiteralChamber
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
theorem sectionTuple_continuous : Continuous (sectionTuple F ζ hζ) := by
  let f : (InfinitePlace F → ComplexGL2) → ∀v, compact F ζ hζ v :=
    fun a v => ⟨sectionTuple F ζ hζ a v, by cases v <;> simp [sectionTuple,compact]⟩
  have hf : Continuous f := by
    apply continuous_pi
    intro v
    apply Continuous.subtype_mk
    cases v with
    | inr q => exact continuous_const
    | inl w =>
      letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
      apply continuous_induced_rng.mpr
      change Continuous (fun a : InfinitePlace F → ComplexGL2 =>
        (Matrix.GeneralLinearGroup.map
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom (a w), (1 : rootsOfUnity 3 F)))
      apply Continuous.prodMk _ continuous_const
      have hc : Continuous (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom :=
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm.continuous
      exact hc.generalLinearGroup_map.comp (continuous_apply w)
  exact (RestrictedProduct.isEmbedding_structureMap.continuous.comp hf)
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end

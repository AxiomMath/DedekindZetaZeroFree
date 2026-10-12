module

public import DedekindZetaZeroFree.Metaplectic.Kubota.Complex.SU2CompactLift
public import DedekindZetaZeroFree.Theta.Periods.Cusps.CompactRightNormalization
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.SectionContinuity

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualFiniteAnchor
open KPCplxCharacterHaar KPAdelicCoverRestrictedProduct KPLiteralChamber
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming sectionTuple_insertion → sectionTuple_insertion
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem exists_compact_raw_anchors {ι : Type*} [Fintype ι]
    (c : ι → KPLiteralRaw.G F ζ hζ) :
    ∃K : Set (RestrictedCover F ζ hζ), IsCompact K ∧
      ∀i (k : KPMsGreenFlux.K F), ∃a∈K,
        scalarQuotient F ζ hζ (amalgamation F ζ hζ a) =
          KPMsGreenFlux.compactInsertion F ζ hζ k * c i := by
  letI : TopologicalSpace ι := ⊥
  letI : DiscreteTopology ι := ⟨rfl⟩
  have hs : Function.Surjective ((scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ)) :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  choose r hr using fun i => hs (c i)
  let f : ι × (InfinitePlace F → ComplexSU2) → RestrictedCover F ζ hζ := fun p =>
    sectionTuple F ζ hζ (fun w => complexSU2Embedding (p.2 w)) * r p.1
  have hf : Continuous f := by
    apply continuous_prod_of_discrete_left.mpr
    intro i
    dsimp only [f]
    apply Continuous.mul_const
    apply (ResidualPrincipalSlices.sectionTuple_continuous F ζ hζ).comp
    exact continuous_pi (fun w => KPActualReflectionData.StandardLocalSource.complexSU2Embedding_continuous.comp (continuous_apply w))
  refine ⟨Set.range f, isCompact_range hf, ?_⟩
  intro i k
  have hk (w : InfinitePlace F) : ∃q : ComplexSU2,
      Matrix.ProjGenLinGroup.mk (complexSU2Embedding q) = (k w).val := (k w).property
  choose q hq using hk
  refine ⟨f (i,q), ⟨(i,q),rfl⟩, ?_⟩
  simp only [f,map_mul,sectionTuple_insertion,show scalarQuotient F ζ hζ
    (amalgamation F ζ hζ (r i)) = c i from hr i]
  congr 1
  change KPSmoothActualFlowData.archimedeanInsertion F ζ hζ _ =
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ _
  congr 1
  exact funext hq

end DedekindZetaZeroFree.FourierContinuation.ResidualFiniteAnchor

end

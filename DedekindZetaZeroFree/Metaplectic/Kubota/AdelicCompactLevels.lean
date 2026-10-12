module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicRationalSplitting
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RepresentationsAndFixedLevels

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ActualQuotientTopology.Cover
open Topology
open scoped Pointwise
open scoped NumberField Classical

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev RawCover := KPAdelicCoverRestrictedProduct.CubicPGL2Adelic F ζ hζ

open NumberField IsDedekindDomain
open KPAdelicCoverRestrictedProduct
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
set_option maxHeartbeats 800000

set_option backward.isDefEq.respectTransparency false in
private theorem local_secondCountable (v : KPHilbert.Place F) :
    SecondCountableTopology (KPLocalCover.CubicGL2Raw F ζ hζ v) := by
  cases v with
  | inl w =>
    letI : SecondCountableTopology w.Completion := by
      rcases w.isReal_or_isComplex with hv | hv
      · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.isEmbedding.secondCountableTopology
      · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.isEmbedding.secondCountableTopology
    letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) w.Completion) := by
      change SecondCountableTopology (Fin 2 → Fin 2 → w.Completion)
      infer_instance
    letI : SecondCountableTopology (KPHilbert.Completion F (Sum.inl w)) := by
      change SecondCountableTopology w.Completion
      infer_instance
    letI : SecondCountableTopology (KPLocalCover.LocalGL2 F (Sum.inl w)) := by
      haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inl w))) := by
        change SecondCountableTopology (Fin 2 → Fin 2 → KPHilbert.Completion F (Sum.inl w))
        infer_instance
      letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inl w)))ᵐᵒᵖ :=
        MulOpposite.opHomeomorph.symm.secondCountableTopology
      exact Units.isEmbedding_embedProduct.secondCountableTopology
    letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
    have hi : Topology.IsEmbedding (KPLocalChartTopology.complexCoordinates F ζ hζ w) :=
      ⟨⟨rfl⟩, (KPLocalChartTopology.complexCoordinates F ζ hζ w).injective⟩
    exact hi.secondCountableTopology
  | inr q =>
    letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
    letI : TopologicalSpace.SeparableSpace (q.adicCompletion F) :=
      ⟨⟨Set.range (algebraMap F (q.adicCompletion F)), Set.countable_range _,
        HeightOneSpectrum.denseRange_algebraMap F q⟩⟩
    letI : SecondCountableTopology (q.adicCompletion F) := inferInstance
    letI : SecondCountableTopology (KPHilbert.Completion F (Sum.inr q)) := by
      change SecondCountableTopology (q.adicCompletion F)
      infer_instance
    letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inr q))) := by
      change SecondCountableTopology (Fin 2 → Fin 2 → KPHilbert.Completion F (Sum.inr q))
      infer_instance
    letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inr q)))ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.secondCountableTopology
    letI : SecondCountableTopology (KPLocalCover.LocalGL2 F (Sum.inr q)) :=
      Units.isEmbedding_embedProduct.secondCountableTopology
    letI : SecondCountableTopology (KPLocalCube.LocalGL2 F q) := by
      letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (KPLocalCube.LocalField F q)) := by
        change SecondCountableTopology (Fin 2 → Fin 2 → q.adicCompletion F)
        infer_instance
      letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (KPLocalCube.LocalField F q))ᵐᵒᵖ :=
        MulOpposite.opHomeomorph.symm.secondCountableTopology
      exact Units.isEmbedding_embedProduct.secondCountableTopology
    let m := depth F ζ hζ q
    have hm := depth_admissible F ζ hζ q
    let U (g : KPLocalCover.LocalGL2 F (Sum.inr q)) : Set (KPLocalCover.LocalGL2 F (Sum.inr q)) :=
      Set.range ((Homeomorph.mulLeft g) ∘ (Subtype.val : KPLocalCube.Gamma F q m → _))
    have hU (g : KPLocalCover.LocalGL2 F (Sum.inr q)) : U g ∈ 𝓝 g := by
      have ho : Topology.IsOpenEmbedding ((Homeomorph.mulLeft g) ∘
          (Subtype.val : KPLocalCube.Gamma F q m → _)) := (Homeomorph.mulLeft g).isOpenEmbedding.comp
        (KPLocalCube.Gamma_compact_open F q m hm.1).2.isOpenEmbedding_subtypeVal
      have heq : (Homeomorph.mulLeft g : _ → _) ∘ (Subtype.val : KPLocalCube.Gamma F q m → _) =
          (fun k : KPLocalCube.Gamma F q m => g * k.val) := rfl
      have hopen : IsOpen (U g) := by
        simpa only [U, Set.image_univ, heq] using ho.isOpen_range
      apply hopen.mem_nhds
      exact ⟨1, mul_one g⟩
    obtain ⟨s, hs, hcover⟩ := LindelofSpace.elim_nhds_subcover U hU
    letI : Countable s := hs.to_subtype
    let V (g : s) : Set (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :=
      {x | x.g ∈ U g.val}
    have hV (g : s) : IsOpen (V g) := by
      have ho := (Homeomorph.mulLeft g.val).isOpenEmbedding.comp
        (KPLocalCube.Gamma_compact_open F q m hm.1).2.isOpenEmbedding_subtypeVal
      exact ho.isOpen_range.preimage
        (KPLocalChartTopology.finite_projection F ζ hζ q m hm).1.continuous
    letI : ∀ g : s, SecondCountableTopology (V g) := fun g => by
      letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
      letI : SecondCountableTopology (KPLocalCube.Gamma F q m) :=
        Topology.IsEmbedding.subtypeVal.secondCountableTopology
      letI : SecondCountableTopology (rootsOfUnity 3 F) := inferInstance
      obtain ⟨e, _⟩ := KPLocalChartTopology.finite_three_sheet_trivialization F ζ hζ q m hm g.val
      have heq : V g = {x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q) |
          x.g ∈ (fun k : KPLocalCube.Gamma F q m => g.val * k.val) '' Set.univ} := by
        ext x
        simp only [V, U, Set.mem_setOf_eq, Set.image_univ]
        rfl
      rw [heq]
      exact e.symm.secondCountableTopology
    apply TopologicalSpace.secondCountableTopology_of_countable_cover hV
    apply Set.eq_univ_of_forall
    intro x
    have hx : x.g ∈ ⋃ g ∈ s, U g := by rw [hcover]; trivial
    obtain ⟨g, hg, hx⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion.mpr ⟨⟨g, hg⟩, hx⟩

set_option backward.isDefEq.respectTransparency false in
private theorem restricted_secondCountable : SecondCountableTopology (RestrictedCover F ζ hζ) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable (𝓞 F) := Function.Injective.countable RingOfIntegers.coe_injective
  letI : Countable (Ideal (𝓞 F)) := by
    have h : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (↑s : Set (𝓞 F))) := by
      intro I
      exact IsNoetherian.noetherian I
    exact h.countable
  letI : Countable (HeightOneSpectrum (𝓞 F)) :=
    Function.Injective.countable (fun _ _ h => HeightOneSpectrum.ext h)
  letI : ∀ v : KPHilbert.Place F, SecondCountableTopology
      (KPLocalCover.CubicGL2Raw F ζ hζ v) := local_secondCountable F ζ hζ
  let X := fun v : KPHilbert.Place F => KPLocalCover.CubicGL2Raw F ζ hζ v
  let C := fun v : KPHilbert.Place F => (compact F ζ hζ v : Set (X v))
  let f (s : Finset (KPHilbert.Place F)) :=
    RestrictedProduct.inclusion X C (Filter.le_principal_iff.mpr s.finite_toSet.compl_mem_cofinite)
  let U (s : Finset (KPHilbert.Place F)) : Set (RestrictedCover F ζ hζ) := Set.range (f s)
  have hf (s : Finset (KPHilbert.Place F)) : Topology.IsOpenEmbedding (f s) :=
    RestrictedProduct.isOpenEmbedding_inclusion_principal (compact_open F ζ hζ) _
  letI (s : Finset (KPHilbert.Place F)) :
      SecondCountableTopology (RestrictedProduct X C (Filter.principal (↑s : Set _)ᶜ)) :=
    RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
  letI : ∀ s : Finset (KPHilbert.Place F), SecondCountableTopology (U s) :=
    fun s => (hf s).toIsEmbedding.toHomeomorph.symm.secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (U := U) (fun s => (hf s).isOpen_range)
  apply Set.eq_univ_of_forall
  intro a
  have ha : {v | a v ∉ compact F ζ hζ v}.Finite := a.2
  apply Set.mem_iUnion_of_mem ha.toFinset
  refine Set.mem_range.mpr ⟨⟨a.1, ?_⟩, rfl⟩
  intro v hv
  change a v ∈ compact F ζ hζ v
  simpa using hv

theorem rawCover_secondCountable : SecondCountableTopology (RawCover F ζ hζ) := by
  letI : SecondCountableTopology (RestrictedCover F ζ hζ) := restricted_secondCountable F ζ hζ
  letI : ∀ v : KPHilbert.Place F, IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
    fun v => by
      cases v with
      | inl w => exact (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.1
      | inr q => exact (KPLocalChartTopology.finite_topological_group F ζ hζ q
          (depth F ζ hζ q) (depth_admissible F ζ hζ q)).2.2
  letI : Fact (∀ v, IsOpen (compact F ζ hζ v : Set (KPLocalCover.CubicGL2Raw F ζ hζ v))) :=
    ⟨compact_open F ζ hζ⟩
  haveI : IsTopologicalGroup (RestrictedCover F ζ hζ) := inferInstance
  haveI : SecondCountableTopology (CubicGL2Adelic F ζ hζ) := inferInstance
  infer_instance

end DedekindZetaZeroFree.ActualQuotientTopology.Cover

end

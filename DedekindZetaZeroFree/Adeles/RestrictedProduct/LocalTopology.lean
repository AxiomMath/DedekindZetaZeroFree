module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact

@[expose] public section

/-
The separability and restricted-product countability recipes are adapted from
ImperialCollegeLondon/FLT, commit `f6c6a2fe9796d6d89cd2a0d24e8a453729d881ff`,
`FLT/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` (Kevin Buzzard and
Salvatore Mercuri, copyright 2025) and
`FLT/Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean`
(Matthew Jasper et al., copyright 2025), released under Apache 2.0.
-/

noncomputable section
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPAdelicTopology

variable (F : Type) [Field F] [NumberField F]

abbrev FiniteAdeles := FiniteAdeleRing (RingOfIntegers F) F
abbrev Adeles := AdeleRing (RingOfIntegers F) F

def integralAdeles : AddSubgroup (FiniteAdeles F) where
  carrier := {a | ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F}
  zero_mem' := by intro v; exact (v.adicCompletionIntegers F).zero_mem
  add_mem' := by
    intro a b ha hb v
    exact (v.adicCompletionIntegers F).toSubring.add_mem (ha v) (hb v)
  neg_mem' := by
    intro a ha v
    exact (v.adicCompletionIntegers F).toSubring.neg_mem (ha v)

@[simp]
theorem integralAdeles_mem_iff (a : FiniteAdeles F) :
    a ∈ integralAdeles F ↔
      ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F := Iff.rfl

theorem completionIntegers_isCompact (v : HeightOneSpectrum (RingOfIntegers F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  change IsCompact ((Valued.integer (v.adicCompletion F)) : Set (v.adicCompletion F))
  exact isCompact_iff_compactSpace.mpr
    (Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance)

theorem completionIntegers_isOpen (v : HeightOneSpectrum (RingOfIntegers F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  exact Valued.isOpen_valuationSubring _

set_option backward.isDefEq.respectTransparency false in
theorem integralAdeles_isCompact : IsCompact (integralAdeles F : Set (FiniteAdeles F)) := by
  letI : ∀ v : HeightOneSpectrum (RingOfIntegers F), CompactSpace (v.adicCompletionIntegers F) :=
    fun v => isCompact_iff_compactSpace.mp (completionIntegers_isCompact F v)
  change IsCompact {a : RestrictedProduct
    (fun v : HeightOneSpectrum (RingOfIntegers F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set _)) Filter.cofinite | ∀ v, a.1 v ∈ v.adicCompletionIntegers F}
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (RingOfIntegers F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set _)) (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  convert h using 1 <;> rfl

theorem integralAdeles_isOpen : IsOpen (integralAdeles F : Set (FiniteAdeles F)) := by
  exact RestrictedProduct.isOpen_forall_mem (completionIntegers_isOpen F)

instance finiteAdeles_t2Space : T2Space (FiniteAdeles F) := by
  exact inferInstanceAs (T2Space (RestrictedProduct
    (fun v : HeightOneSpectrum (RingOfIntegers F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))

instance finiteAdeles_locallyCompactSpace : LocallyCompactSpace (FiniteAdeles F) := by
  letI : Fact (∀ v : HeightOneSpectrum (RingOfIntegers F),
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨completionIntegers_isOpen F⟩
  letI : IsTopologicalAddGroup (FiniteAdeles F) := inferInstanceAs
    (IsTopologicalAddGroup (RestrictedProduct
      (fun v : HeightOneSpectrum (RingOfIntegers F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set _)) Filter.cofinite))
  exact (integralAdeles_isCompact F).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((integralAdeles_isOpen F).mem_nhds (integralAdeles F).zero_mem)

instance finiteAdeles_secondCountableTopology : SecondCountableTopology (FiniteAdeles F) := by
  classical
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable (RingOfIntegers F) :=
    Function.Injective.countable RingOfIntegers.coe_injective
  letI : Countable (Ideal (RingOfIntegers F)) := by
    have h : Function.Surjective (fun s : Finset (RingOfIntegers F) =>
        Ideal.span (↑s : Set (RingOfIntegers F))) := by
      intro I
      exact IsNoetherian.noetherian I
    exact h.countable
  letI : Countable (HeightOneSpectrum (RingOfIntegers F)) :=
    Function.Injective.countable (fun _ _ h => HeightOneSpectrum.ext h)
  letI : ∀ v : HeightOneSpectrum (RingOfIntegers F),
      SecondCountableTopology (v.adicCompletion F) := fun v => by
    letI : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
      ⟨⟨Set.range (algebraMap F (v.adicCompletion F)), Set.countable_range _,
        HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
    infer_instance
  let X := fun v : HeightOneSpectrum (RingOfIntegers F) => v.adicCompletion F
  let C := fun v : HeightOneSpectrum (RingOfIntegers F) => (v.adicCompletionIntegers F : Set (X v))
  let f (s : Finset (HeightOneSpectrum (RingOfIntegers F))) :=
    RestrictedProduct.inclusion X C (Filter.le_principal_iff.mpr s.finite_toSet.compl_mem_cofinite)
  change SecondCountableTopology (RestrictedProduct X C Filter.cofinite)
  let U (s : Finset (HeightOneSpectrum (RingOfIntegers F))) : Set (RestrictedProduct X C Filter.cofinite) :=
    Set.range (f s)
  have hf (s : Finset (HeightOneSpectrum (RingOfIntegers F))) : Topology.IsOpenEmbedding (f s) :=
    RestrictedProduct.isOpenEmbedding_inclusion_principal (completionIntegers_isOpen F) _
  letI (s : Finset (HeightOneSpectrum (RingOfIntegers F))) :
      SecondCountableTopology (RestrictedProduct X C (Filter.principal (↑s : Set _)ᶜ)) :=
    RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
  letI : ∀ s : Finset (HeightOneSpectrum (RingOfIntegers F)), SecondCountableTopology (U s) :=
    fun s => (hf s).toIsEmbedding.toHomeomorph.symm.secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (U := U) (fun s => (hf s).isOpen_range)
  apply Set.eq_univ_of_forall
  intro a
  have ha : {v | a v ∉ v.adicCompletionIntegers F}.Finite := a.2
  apply Set.mem_iUnion_of_mem ha.toFinset
  refine Set.mem_range.mpr ⟨⟨a.1, ?_⟩, rfl⟩
  intro v hv
  change a v ∈ v.adicCompletionIntegers F
  simpa using hv

instance adeles_t2Space : T2Space (Adeles F) := by
  letI : T2Space (InfiniteAdeleRing F) := inferInstanceAs
    (T2Space ((v : InfinitePlace F) → v.Completion))
  exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeles F))

instance adeles_locallyCompactSpace : LocallyCompactSpace (Adeles F) := by
  exact inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeles F))

instance adeles_secondCountableTopology : SecondCountableTopology (Adeles F) := by
  letI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v => by
    rcases v.isReal_or_isComplex with hv | hv
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.isEmbedding.secondCountableTopology
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (InfiniteAdeleRing F) := inferInstanceAs
    (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))
  exact inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeles F))

instance finiteAdeles_measurableSpace : MeasurableSpace (FiniteAdeles F) := borel _

instance finiteAdeles_borelSpace : BorelSpace (FiniteAdeles F) := ⟨rfl⟩

instance adeles_measurableSpace : MeasurableSpace (Adeles F) := borel _

instance adeles_borelSpace : BorelSpace (Adeles F) := ⟨rfl⟩

instance completion_measurableSpace (v : HeightOneSpectrum (RingOfIntegers F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

instance completion_borelSpace (v : HeightOneSpectrum (RingOfIntegers F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

end DedekindZetaZeroFree.KPAdelicTopology

end

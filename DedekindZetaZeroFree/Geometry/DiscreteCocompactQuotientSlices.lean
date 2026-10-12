module

public import Mathlib.Topology.Covering.Quotient

@[expose] public section

namespace DedekindZetaZeroFree

theorem exists_finite_relativelyCompact_quotient_slices
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ (n : ℕ) (V : Fin n → Set G),
      (∀ i, IsOpen (V i) ∧ IsCompact (closure (V i)) ∧
        Set.InjOn (QuotientGroup.mk : G → G ⧸ Γ) (V i)) ∧
      (⋃ i : Fin n, (QuotientGroup.mk : G → G ⧸ Γ) '' V i) = Set.univ := by
  classical
  have hlocal := (Γ.isQuotientCoveringMap_of_comm
    (isDiscrete_iff_discreteTopology.mpr inferInstance)).isLocalHomeomorph.isLocallyInjective
  have hslices : ∀ g : G, ∃ U : Set G, IsOpen U ∧ g ∈ U ∧
      IsCompact (closure U) ∧ Set.InjOn (QuotientGroup.mk : G → G ⧸ Γ) U := by
    intro g
    obtain ⟨U, hU, hgU, hinj⟩ := hlocal g
    obtain ⟨T, hT, hgT, hcT⟩ := exists_isOpen_mem_isCompact_closure g
    refine ⟨U ∩ T, hU.inter hT, ⟨hgU, hgT⟩, ?_, hinj.mono Set.inter_subset_left⟩
    exact hcT.of_isClosed_subset isClosed_closure (closure_mono Set.inter_subset_right)
  choose U hopen hmem hcompact hinj using hslices
  have hcover : Set.univ ⊆ ⋃ g : G, (QuotientGroup.mk : G → G ⧸ Γ) '' U g := by
    intro x _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact Set.mem_iUnion.mpr ⟨g, Set.mem_image_of_mem _ (hmem g)⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun g : G => (QuotientGroup.mk : G → G ⧸ Γ) '' U g)
    (fun g => QuotientGroup.isOpenMap_coe _ (hopen g)) hcover
  let e := s.equivFin
  refine ⟨s.card, fun i => U (e.symm i), ?_, ?_⟩
  · intro i
    exact ⟨hopen _, hcompact _, hinj _⟩
  · apply Set.Subset.antisymm (Set.subset_univ _)
    intro x hx
    obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨e ⟨g, hg⟩, by simpa using hxg⟩

end DedekindZetaZeroFree

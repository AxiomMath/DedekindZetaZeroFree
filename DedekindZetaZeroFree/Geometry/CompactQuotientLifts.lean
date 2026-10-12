module

public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

namespace DedekindZetaZeroFree

theorem exists_compact_leftOrbit_lifts
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] (L : Subgroup G)
    [CompactSpace (Quotient (MulAction.orbitRel L G))] :
    ∃ K : Set G, IsCompact K ∧
      (Quotient.mk (MulAction.orbitRel L G)) '' K = Set.univ := by
  classical
  have hq : IsOpenMap (Quotient.mk (MulAction.orbitRel L G)) :=
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  choose V hVopen hgV hVcomp using fun g : G => exists_isOpen_mem_isCompact_closure g
  have hcover : (Set.univ : Set (Quotient (MulAction.orbitRel L G))) ⊆
      ⋃ g, Quotient.mk (MulAction.orbitRel L G) '' V g := by
    intro y _
    obtain ⟨x, rfl⟩ := MulAction.isOpenQuotientMap_quotientMk.surjective y
    exact Set.mem_iUnion.2 ⟨x, x, hgV x, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _
    (fun g => hq _ (hVopen g)) hcover
  refine ⟨⋃ g ∈ t, closure (V g), t.isCompact_biUnion fun g _ => hVcomp g, ?_⟩
  rw [Set.eq_univ_iff_forall]
  intro y
  obtain ⟨x, rfl⟩ := MulAction.isOpenQuotientMap_quotientMk.surjective y
  have hx : Quotient.mk (MulAction.orbitRel L G) x ∈
      ⋃ g ∈ t, Quotient.mk (MulAction.orbitRel L G) '' V g := ht (Set.mem_univ _)
  obtain ⟨g, hg⟩ := Set.mem_iUnion.1 hx
  obtain ⟨hgt, hv⟩ := Set.mem_iUnion.1 hg
  obtain ⟨v, hvV, hvq⟩ := hv
  exact ⟨v, Set.mem_iUnion.2 ⟨g, Set.mem_iUnion.2 ⟨hgt, subset_closure hvV⟩⟩, hvq⟩

theorem exists_compact_subgroup_left_translates
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] (L : Subgroup G)
    [CompactSpace (Quotient (MulAction.orbitRel L G))] :
    ∃ K : Set G, IsCompact K ∧ ∀ g : G, ∃ l : L, (l : G) * g ∈ K := by
  obtain ⟨K, hKc, hK⟩ := exists_compact_leftOrbit_lifts L
  refine ⟨K, hKc, fun g => ?_⟩
  have hmem : Quotient.mk (MulAction.orbitRel L G) g ∈
      Quotient.mk (MulAction.orbitRel L G) '' K := by rw [hK]; exact Set.mem_univ _
  obtain ⟨k, hkK, hkq⟩ := hmem
  have hrel : MulAction.orbitRel L G k g := Quotient.exact hkq
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨l, hl⟩ := hrel
  have : (l : G) * g = k := (show (l : G) * g = l • g from rfl).trans hl
  exact ⟨l, this ▸ hkK⟩

end DedekindZetaZeroFree

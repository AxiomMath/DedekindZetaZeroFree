module

public import DedekindZetaZeroFree.Adeles.Lattices.SupportedPrincipalIntersection

@[expose] public section

namespace DedekindZetaZeroFree
namespace SArithmeticData

noncomputable section

variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)

private theorem principalIntersection_closed :
    IsClosed (A.principalIntersection : Set A.H) :=
  (IdeleGroup.principalSubgroup_isClosed (K := F)).preimage
    (continuous_subtype_val.comp continuous_subtype_val)

private theorem principalIntersection_discrete :
    IsDiscrete (A.principalIntersection : Set A.H) := by
  have hd : IsDiscrete (IdeleGroup.principalSubgroup F : Set (IdeleGroup F)) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  exact hd.preimage
    (continuous_subtype_val.comp continuous_subtype_val).continuousOn
    (Subtype.val_injective.comp Subtype.val_injective)

private theorem Lambda_closed_discrete :
    IsClosed (A.Lambda : Set (A.G1 × A.C)) ∧
      IsDiscrete (A.Lambda : Set (A.G1 × A.C)) := by
  obtain ⟨e, he⟩ := A.exists_supportedChart
  have hset : e '' (A.principalIntersection : Set A.H) =
      (A.Lambda : Set (A.G1 × A.C)) := by
    rw [← A.principalIntersection_map_supportedChart e he]
    rfl
  constructor
  · rw [← hset]
    exact e.toHomeomorph.isClosedMap _ (principalIntersection_closed A)
  · rw [← hset]
    exact (principalIntersection_discrete A).image e.toHomeomorph.isInducing

 theorem finite_L_inter_compact (K : Set A.G1) (hK : IsCompact K) :
    Set.Finite {l : A.L | (l : A.G1) ∈ K} := by
  obtain ⟨hc, hd⟩ := Lambda_closed_discrete A
  have hfin : Set.Finite ((K ×ˢ Set.univ) ∩ (A.Lambda : Set (A.G1 × A.C))) :=
    ((hK.prod isCompact_univ).inter_right hc).finite (hd.mono Set.inter_subset_right)
  have him : Set.Finite (K ∩ (A.L : Set A.G1)) := by
    apply (hfin.image Prod.fst).subset
    rintro l ⟨hlK, hlL⟩
    obtain ⟨u, rfl⟩ := hlL
    refine ⟨A.unitGraph u, ⟨⟨hlK, Set.mem_univ _⟩, ?_⟩, rfl⟩
    exact ⟨u, rfl⟩
  exact (him.preimage (f := fun l : A.L => (l : A.G1))
    Subtype.val_injective.injOn).subset (fun l hl => ⟨hl, l.prop⟩)

instance discreteTopology_L : DiscreteTopology A.L := by
  apply continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact
  exact tendsto_cofinite_cocompact_iff.mpr (finite_L_inter_compact A)

instance discreteTopology_Gamma1 : DiscreteTopology A.Gamma1 := by
  letI : DiscreteTopology (A.L : Set A.G1) := A.discreteTopology_L
  exact (Topology.IsEmbedding.inclusion A.Gamma1_le_L).discreteTopology

instance countable_Gamma1 : Countable A.Gamma1 := by
  letI : Countable F := (Module.finBasis ℚ F).repr.injective.countable
  letI : Countable Fˣ := Units.val_injective.countable
  letI : Countable A.L := (Set.countable_range A.diagonalS).to_subtype
  exact (Set.inclusion_injective A.Gamma1_le_L).countable

end
end SArithmeticData
end DedekindZetaZeroFree

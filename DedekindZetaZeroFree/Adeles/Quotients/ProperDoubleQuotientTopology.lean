module

public import Mathlib

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.ActualQuotientTopology.Generic

open Topology

open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G]

abbrev RawDoubleQuotient (Γ K : Subgroup G) :=
  DoubleCoset.Quotient (Γ : Set G) (K : Set G)

instance (Γ K : Subgroup G) : TopologicalSpace (RawDoubleQuotient Γ K) :=
  inferInstanceAs (TopologicalSpace (_root_.Quotient _))

end DedekindZetaZeroFree.ActualQuotientTopology.Generic

end

section

noncomputable section
namespace DedekindZetaZeroFree.ActualQuotientTopology.Generic
open Topology
open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G]

abbrev rawQuotientMap (Γ K : Subgroup G) : G → RawDoubleQuotient Γ K :=
  DoubleCoset.mk Γ K

abbrev rawActionCorrespondence (Γ K : Subgroup G) : (Γ × K) × G → G × G :=
  fun p => ((p.1.1 : G) * p.2 * (p.1.2 : G)⁻¹, p.2)

theorem proper_rawActionCorrespondence [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (Γ K : Subgroup G)
    (hΓ : IsClosed (Γ : Set G)) (dΓ : IsDiscrete (Γ : Set G))
    (hK : IsCompact (K : Set G)) :
    IsProperMap (rawActionCorrespondence Γ K) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (rawActionCorrespondence Γ K) := by
    fun_prop
  refine isProperMap_iff_isCompact_preimage.mpr ⟨hc, ?_⟩
  intro C hC
  have hB : IsCompact ((Prod.fst '' C) * (K : Set G) * (Prod.snd '' C)⁻¹) :=
    ((hC.image continuous_fst).mul hK).mul (hC.image continuous_snd).inv
  have hΓB := hΓ.isProperMap_subtypeVal.isCompact_preimage hB
  refine ((hΓB.prod (isCompact_univ : IsCompact (Set.univ : Set K))).prod (hC.image continuous_snd)).of_isClosed_subset
    (hC.isClosed.preimage hc) ?_
  rintro ⟨⟨γ, k⟩, x⟩ hx
  refine ⟨⟨?_, Set.mem_univ k⟩, ⟨_, hx, rfl⟩⟩
  change (γ : G) ∈ (Prod.fst '' C) * (K : Set G) * (Prod.snd '' C)⁻¹
  refine Set.mem_mul.mpr ⟨(γ : G) * x, ?_, x⁻¹, ?_, by simp⟩
  · refine Set.mem_mul.mpr ⟨(γ : G) * x * (k : G)⁻¹, ⟨_, hx, rfl⟩,
      (k : G), k.property, by simp⟩
  · exact Set.mem_inv.mpr ⟨_, hx, by simp⟩

theorem locallyCompact_secondCountable_polish (Y : Type*)
    [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  letI : MetricSpace Y := TopologicalSpace.metrizableSpaceMetric Y
  let e : Y → UniformSpace.Completion Y := fun x => x
  have he : IsDenseEmbedding e := UniformSpace.Completion.isDenseEmbedding_coe
  have ho : IsOpen (Set.range e) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, rfl⟩
    obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
    have hc : IsClosed (e '' C) := (hC.image he.continuous).isClosed
    have hn := he.isDenseInducing.closure_image_mem_nhds hx
    rw [hc.closure_eq] at hn
    exact Filter.mem_of_superset hn (Set.image_subset_range e C)
  letI : PolishSpace (Set.range e) := ho.polishSpace
  exact he.isEmbedding.toHomeomorph.isClosedEmbedding.polishSpace

theorem proper_rawDoubleQuotient_topology [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (Γ K : Subgroup G)
    (hp : IsProperMap (rawActionCorrespondence Γ K)) :
    LocallyCompactSpace (RawDoubleQuotient Γ K) ∧
      T2Space (RawDoubleQuotient Γ K) ∧
      SecondCountableTopology (RawDoubleQuotient Γ K) ∧
      Continuous (rawQuotientMap Γ K) ∧
      IsOpenMap (rawQuotientMap Γ K) ∧
      IsQuotientMap (rawQuotientMap Γ K) := by
  have hq : IsQuotientMap (rawQuotientMap Γ K) := isQuotientMap_quotient_mk'
  have ho : IsOpenMap (rawQuotientMap Γ K) := by
    intro U hU
    apply hq.isOpen_preimage.mp
    have he : rawQuotientMap Γ K ⁻¹' (rawQuotientMap Γ K '' U) =
        ⋃ (γ : Γ) (k : K), (fun x : G => (γ : G) * x * (k : G)) '' U := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
      constructor
      · rintro ⟨y, hy, he⟩
        obtain ⟨γ, hγ, k, hk, rfl⟩ := DoubleCoset.eq.mp he
        exact ⟨⟨γ, hγ⟩, ⟨k, hk⟩, y, hy, rfl⟩
      · rintro ⟨γ, k, y, hy, rfl⟩
        exact ⟨y, hy, DoubleCoset.eq.mpr ⟨γ, γ.property, k, k.property, rfl⟩⟩
    rw [he]
    exact isOpen_iUnion fun γ => isOpen_iUnion fun k =>
      ((Homeomorph.mulLeft (γ : G)).trans (Homeomorph.mulRight (k : G))).isOpenMap U hU
  have h := IsOpenQuotientMap.of_isOpenMap_isQuotientMap ho hq
  have hr : Set.range (rawActionCorrespondence Γ K) =
      {p : G × G | rawQuotientMap Γ K p.1 = rawQuotientMap Γ K p.2} := by
    ext p
    constructor
    · rintro ⟨⟨⟨γ, k⟩, x⟩, rfl⟩
      change DoubleCoset.mk Γ K ((γ : G) * x * (k : G)⁻¹) = DoubleCoset.mk Γ K x
      exact DoubleCoset.eq.mpr ⟨(γ : G)⁻¹, Γ.inv_mem γ.property,
        (k : G), k.property, by simp [mul_assoc]⟩
    · intro he
      obtain ⟨γ, hγ, k, hk, he⟩ := DoubleCoset.eq.mp he.symm
      exact ⟨((⟨γ, hγ⟩, ⟨k⁻¹, K.inv_mem hk⟩), p.2), by
        simp only [rawActionCorrespondence, Subgroup.coe_mk, inv_inv]
        exact Prod.ext he.symm rfl⟩
  have ht : T2Space (RawDoubleQuotient Γ K) :=
    (t2Space_iff_of_isOpenQuotientMap h).mpr (hr ▸ hp.isClosed_range)
  exact ⟨h.locallyCompactSpace, ht, h.secondCountableTopology,
    h.continuous, ho, hq⟩

end DedekindZetaZeroFree.ActualQuotientTopology.Generic

end
end

module

public import DedekindZetaZeroFree.Adeles.Archimedean.MixedEmbeddingComparison

@[expose] public section

noncomputable section

open scoped NumberField

namespace DedekindZetaZeroFree

 def archHomeomorph (F : Type*) [Field F] [NumberField F] :
    NumberField.InfiniteAdeleRing F ≃ₜ NumberField.mixedEmbedding.mixedSpace F :=
  { (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).toEquiv with
    continuous_toFun := (sArchModel_comparison F).1
    continuous_invFun := (sArchModel_comparison F).2.1 }

private theorem mixedInteger_mem (F : Type*) [Field F] [NumberField F]
    (x : NumberField.mixedEmbedding.mixedSpace F) :
    x ∈ NumberField.mixedEmbedding.integerLattice F ↔
      ∃ a : 𝓞 F, NumberField.mixedEmbedding F (a : F) = x := by
  rfl

theorem sArchDomain_exists (F : Type*) [Field F] [NumberField F] :
    ∃ B W : Set (NumberField.InfiniteAdeleRing F),
      IsCompact B ∧ IsOpen W ∧ (0 : NumberField.InfiniteAdeleRing F) ∈ W ∧
      (∀ x : NumberField.InfiniteAdeleRing F, ∃ a : 𝓞 F,
        x - algebraMap F (NumberField.InfiniteAdeleRing F) (a : F) ∈ B) ∧
      (∀ a : 𝓞 F,
        algebraMap F (NumberField.InfiniteAdeleRing F) (a : F) ∈ W ↔ a = 0) := by
  classical
  let e := archHomeomorph F
  let L := NumberField.mixedEmbedding.integerLattice F
  have hzero : IsOpen ({0} : Set L) := isOpen_discrete _
  obtain ⟨U, hU, hUzero⟩ := isOpen_induced_iff.mp hzero
  refine ⟨e.symm '' parallelepiped (NumberField.mixedEmbedding.latticeBasis F),
    e ⁻¹' U, ?_, hU.preimage e.continuous, ?_, ?_, ?_⟩
  · exact (NumberField.mixedEmbedding.latticeBasis F).parallelepiped.isCompact.image
      e.symm.continuous
  · have hz : (0 : NumberField.mixedEmbedding.mixedSpace F) ∈ U := by
      have : (0 : L) ∈ Subtype.val ⁻¹' U := by
        rw [hUzero]
        exact Set.mem_singleton 0
      exact this
    change NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F 0 ∈ U
    rw [map_zero]
    exact hz
  · intro x
    obtain ⟨v, hv, _⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain
      (NumberField.mixedEmbedding.latticeBasis F) (e x)
    have hvL : (v : NumberField.mixedEmbedding.mixedSpace F) ∈ L :=
      (NumberField.mixedEmbedding.mem_span_latticeBasis F).mp v.property
    obtain ⟨a, ha⟩ := (mixedInteger_mem F _).mp hvL
    refine ⟨-a, ?_⟩
    refine ⟨(v : NumberField.mixedEmbedding.mixedSpace F) + e x,
      ZSpan.fundamentalDomain_subset_parallelepiped _ hv, ?_⟩
    apply e.injective
    rw [e.apply_symm_apply]
    change _ = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F
      (x - algebraMap F (NumberField.InfiniteAdeleRing F) ((-a : 𝓞 F) : F))
    change _ = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F
      (x - algebraMap F (NumberField.InfiniteAdeleRing F)
        (algebraMap (𝓞 F) F (-a)))
    rw [map_neg, map_neg, sub_neg_eq_add, map_add,
      ← NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    rw [ha, add_comm]
    rfl
  · intro a
    have haL : NumberField.mixedEmbedding F (a : F) ∈ L :=
      (mixedInteger_mem F _).mpr ⟨a, rfl⟩
    have hiff : NumberField.mixedEmbedding F (a : F) ∈ U ↔
        NumberField.mixedEmbedding F (a : F) = 0 := by
      change (⟨NumberField.mixedEmbedding F (a : F), haL⟩ : L) ∈
          Subtype.val ⁻¹' U ↔ _
      rw [hUzero]
      simp only [Set.mem_singleton_iff, Subtype.ext_iff, ZeroMemClass.coe_zero]
    change NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F
      (algebraMap F (NumberField.InfiniteAdeleRing F) (a : F)) ∈ U ↔ _
    rw [← NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, hiff]
    rw [map_eq_zero_iff _ (NumberField.mixedEmbedding_injective F)]
    change algebraMap (𝓞 F) F a = 0 ↔ a = 0
    exact map_eq_zero_iff _ NumberField.RingOfIntegers.coe_injective

end DedekindZetaZeroFree

end

module

public import DedekindZetaZeroFree.Adeles.RestrictedProduct.LocalTopology
public import DedekindZetaZeroFree.Adeles.Lattices.FractionalIdealTraceDual

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPAdelicDiagonal

open NumberField
open KPAdelicTopology

variable (F : Type) [Field F] [NumberField F]

abbrev principalSubgroup : AddSubgroup (Adeles F) :=
  AdeleRing.principalSubgroup (RingOfIntegers F) F

def diagonalAddEquiv : F ≃+ principalSubgroup F :=
  AddMonoidHom.ofInjective
    (f := (algebraMap F (Adeles F)).toAddMonoidHom)
    (AdeleRing.algebraMap_injective (RingOfIntegers F) F)

theorem exists_open_diag_preimage_zero :
    ∃ U : Set (Adeles F), IsOpen U ∧ (0 : Adeles F) ∈ U ∧
      (algebraMap F (Adeles F)) ⁻¹' U = ({0} : Set F) := by
  classical
  let L := mixedEmbedding.integerLattice F
  obtain ⟨W, hW, hWL⟩ :=
    (isOpen_induced_iff.mp (isOpen_discrete ({0} : Set L)))
  have hW0 : (0 : mixedEmbedding.mixedSpace F) ∈ W := by
    have h : (0 : L) ∈ Subtype.val ⁻¹' W := by
      rw [hWL]
      exact Set.mem_singleton 0
    exact h
  have hc : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply v.1)
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply v.1)
  let U : Set (Adeles F) :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F ⁻¹' W) ×ˢ
      (integralAdeles F : Set (FiniteAdeles F))
  refine ⟨U, (hW.preimage hc).prod (integralAdeles_isOpen F), ?_, ?_⟩
  · constructor
    · change InfiniteAdeleRing.ringEquiv_mixedSpace F 0 ∈ W
      simpa only [map_zero] using hW0
    · exact (integralAdeles F).zero_mem
  · ext x
    constructor
    · intro hx
      have hfinite : ∀ v : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers F),
          v.valuation F x ≤ 1 := by
        intro v
        have hv := hx.2 v
        change (x : v.adicCompletion F) ∈ v.adicCompletionIntegers F at hv
        simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
          IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe] using hv
      obtain ⟨r, hr⟩ :=
        IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F x hfinite
      have hL : mixedEmbedding F x ∈ L := by
        exact ⟨r, congrArg (mixedEmbedding F) hr⟩
      have hsmall : mixedEmbedding F x ∈ W := by
        rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
        exact hx.1
      have hz : (⟨mixedEmbedding F x, hL⟩ : L) = 0 := by
        have hm : (⟨mixedEmbedding F x, hL⟩ : L) ∈ Subtype.val ⁻¹' W := hsmall
        rwa [hWL, Set.mem_singleton_iff] at hm
      apply Set.mem_singleton_iff.mpr
      apply NumberField.mixedEmbedding_injective
      simpa using congrArg Subtype.val hz
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      simp only [Set.mem_preimage, map_zero]
      constructor
      · change InfiniteAdeleRing.ringEquiv_mixedSpace F 0 ∈ W
        simpa only [map_zero] using hW0
      · exact (integralAdeles F).zero_mem

theorem principalSubgroup_discrete : DiscreteTopology (principalSubgroup F) := by
  obtain ⟨U, hU, hU0, hdiag⟩ := exists_open_diag_preimage_zero F
  apply discreteTopology_of_isOpen_singleton_zero
  have heq : (Subtype.val : principalSubgroup F → Adeles F) ⁻¹' U = {0} := by
    ext a
    constructor
    · intro ha
      obtain ⟨x, hx⟩ := a.property
      have hx0 : x = 0 := by
        have hm : x ∈ (algebraMap F (Adeles F)) ⁻¹' U := by
          change algebraMap F (Adeles F) x ∈ U
          rwa [hx]
        rwa [hdiag, Set.mem_singleton_iff] at hm
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      change (a : Adeles F) = 0
      simpa only [hx0, map_zero] using hx.symm
    · intro ha
      rcases Set.mem_singleton_iff.mp ha with rfl
      exact hU0
  rw [← heq]
  exact hU.preimage continuous_subtype_val

theorem principalSubgroup_isClosed :
    IsClosed (principalSubgroup F : Set (Adeles F)) := by
  letI := principalSubgroup_discrete F
  exact AddSubgroup.isClosed_of_discreteTopology

end DedekindZetaZeroFree.KPAdelicDiagonal

end

module

public import DedekindZetaZeroFree.Adeles.Lattices.PrincipalAdeleDiscreteness
public import DedekindZetaZeroFree.Adeles.Approximation.FiniteAdeleDensity
public import DedekindZetaZeroFree.Adeles.Characters.ArchimedeanAdditiveCharacters

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPAdelicQuotient

open NumberField KPAdelicTopology KPAdelicDiagonal

variable (F : Type) [Field F] [NumberField F]

def quotientMap : Adeles F →+ (Adeles F ⧸ principalSubgroup F) :=
  QuotientAddGroup.mk' (principalSubgroup F)

instance quotient_t2Space : T2Space (Adeles F ⧸ principalSubgroup F) := by
  letI : IsClosed (principalSubgroup F : Set (Adeles F)) := principalSubgroup_isClosed F
  infer_instance

theorem exists_compact_infinite_cover :
    ∃ C : Set (InfiniteAdeleRing F), IsCompact C ∧
      (quotientMap F) ''
        (C ×ˢ (integralAdeles F : Set (FiniteAdeles F))) = Set.univ := by
  classical
  let b := mixedEmbedding.latticeBasis F
  let e : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
    (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.trans
      (mixedEmbedding.euclidean.toMixed F).toHomeomorph
  have he (x : InfiniteAdeleRing F) :
      e x = InfiniteAdeleRing.ringEquiv_mixedSpace F x :=
    PoissonArch.infiniteAdeleToSpace_coordinates F x
  let C : Set (InfiniteAdeleRing F) := e ⁻¹' (b.parallelepiped : Set _)
  refine ⟨C, e.isCompact_preimage.mpr b.parallelepiped.isCompact, ?_⟩
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (principalSubgroup F) q
  obtain ⟨r, hr⟩ := exists_integral_remainder F a.2
  let y := e (a.1 - algebraMap F (InfiniteAdeleRing F) r)
  have hf : (ZSpan.floor b y : mixedEmbedding.mixedSpace F) ∈
      mixedEmbedding.integerLattice F :=
    (mixedEmbedding.mem_span_latticeBasis F).mp (ZSpan.floor b y).property
  obtain ⟨s, hs⟩ := hf
  let z : F := r + (s : F)
  refine ⟨a - algebraMap F (Adeles F) z, ⟨?_, ?_⟩, ?_⟩
  · change e (a.1 - algebraMap F (InfiniteAdeleRing F) z) ∈
      (b.parallelepiped : Set _)
    have hs' : mixedEmbedding F (s : F) = (ZSpan.floor b y : mixedEmbedding.mixedSpace F) := hs
    have hmap (x : InfiniteAdeleRing F) (t : F) :
        e (x - algebraMap F (InfiniteAdeleRing F) t) = e x - mixedEmbedding F t := by
      simp only [he, map_sub, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    have hfrac : e (a.1 - algebraMap F (InfiniteAdeleRing F) z) = ZSpan.fract b y := by
      rw [ZSpan.fract_apply, ← hs']
      change e (a.1 - algebraMap F (InfiniteAdeleRing F) (r + (s : F))) =
        e (a.1 - algebraMap F (InfiniteAdeleRing F) r) - mixedEmbedding F (s : F)
      rw [hmap, hmap, map_add]
      abel
    rw [hfrac]
    exact ZSpan.fundamentalDomain_subset_parallelepiped b
      (ZSpan.fract_mem_fundamentalDomain b y)
  · change a.2 - algebraMap F (FiniteAdeles F) z ∈ integralAdeles F
    have hsfin : algebraMap F (FiniteAdeles F) (s : F) ∈ integralAdeles F := by
      intro v
      exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (RingOfIntegers F) F v s
    dsimp [z]
    rw [map_add, ← sub_sub]
    exact (integralAdeles F).sub_mem hr hsfin
  · change QuotientAddGroup.mk (a - algebraMap F (Adeles F) z) = QuotientAddGroup.mk a
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    have hz : algebraMap F (Adeles F) z ∈ principalSubgroup F := ⟨z, rfl⟩
    simpa only [sub_sub_cancel_left] using (principalSubgroup F).neg_mem hz

instance quotient_compactSpace : CompactSpace (Adeles F ⧸ principalSubgroup F) := by
  obtain ⟨C, hC, hcover⟩ := exists_compact_infinite_cover F
  apply isCompact_univ_iff.mp
  rw [← hcover]
  exact (hC.prod (integralAdeles_isCompact F)).image QuotientAddGroup.continuous_mk

end DedekindZetaZeroFree.KPAdelicQuotient

end

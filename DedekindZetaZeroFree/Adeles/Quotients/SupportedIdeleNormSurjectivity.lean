module

public import ClassFieldTheory.All

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField

namespace DedekindZetaZeroFree

theorem supportedAt_le_relativeNorm_range
    (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] [IsAbelianGalois F L]
    (S_f : Finset (HeightOneSpectrum (𝓞 F)))
    (hSplit : ∀ v ∈ S_f, _root_.FinitePlaceSplitsCompletely (K := F) (L := L) v)
    (hAway : ∀ v ∉ S_f, _root_.ChosenFinitePlaceIsUnramified (K := F) (L := L) v)
    (hInf : ∀ w : InfinitePlace F,
      _root_.infiniteTensorNormSubgroup (K := F) (L := L) w = ⊤) :
    IdeleGroup.supportedAt (K := F) (S_f : Set (HeightOneSpectrum (𝓞 F))) ≤
      (RelativeIdeleGroup.norm F L).range := by
  intro u hu
  apply (_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms
    (K := F) (L := L) u).2
  constructor
  · intro w
    rw [hInf w]
    exact Subgroup.mem_top _
  · intro v
    rw [_root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
      (K := F) (L := L) v]
    by_cases hv : v ∈ S_f
    · rw [_root_.chosenFinitePlaceLocalNormSubgroup_eq_top_of_splitsCompletely
        (K := F) (L := L) v (hSplit v hv)]
      exact Subgroup.mem_top _
    · apply _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
        (K := F) (L := L) v (hAway v hv)
      exact (IdeleGroup.mem_supportedAt_iff
        (K := F) (S_f : Set (HeightOneSpectrum (𝓞 F))) u).mp hu v
          (by simpa using hv)

theorem ideleClassNorm_range_top_and_finrank_eq_one_of_supportedAt
    (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] [IsAbelianGalois F L]
    (S_f : Finset (HeightOneSpectrum (𝓞 F)))
    (hSplit : ∀ v ∈ S_f, _root_.FinitePlaceSplitsCompletely (K := F) (L := L) v)
    (hAway : ∀ v ∉ S_f, _root_.ChosenFinitePlaceIsUnramified (K := F) (L := L) v)
    (hInf : ∀ w : InfinitePlace F,
      _root_.infiniteTensorNormSubgroup (K := F) (L := L) w = ⊤)
    (hLarge :
      IdeleGroup.supportedAt (K := F) (S_f : Set (HeightOneSpectrum (𝓞 F))) ⊔
        IdeleGroup.principalSubgroup F = ⊤) :
    (_root_.ideleClassNorm F L).range = ⊤ ∧ Module.finrank F L = 1 := by
  have hRelative :
      (RelativeIdeleGroup.Cohomology.ideleClassNorm F L).range = ⊤ := by
    apply top_unique
    intro c _
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
      (IdeleGroup.principalSubgroup F) c
    have ha : a ∈
        IdeleGroup.supportedAt (K := F) (S_f : Set (HeightOneSpectrum (𝓞 F))) ⊔
          IdeleGroup.principalSubgroup F := by
      rw [hLarge]
      exact Subgroup.mem_top _
    rcases Subgroup.mem_sup.mp ha with ⟨u, hu, q, hq, huq⟩
    obtain ⟨z, hz⟩ := supportedAt_le_relativeNorm_range
      F L S_f hSplit hAway hInf hu
    refine ⟨QuotientGroup.mk' (RelativeIdeleGroup.principalSubgroup F L) z, ?_⟩
    rw [RelativeIdeleGroup.Cohomology.ideleClassNorm_mk, hz]
    change QuotientGroup.mk' (IdeleGroup.principalSubgroup F) u =
      QuotientGroup.mk' (IdeleGroup.principalSubgroup F) a
    have hqOne : QuotientGroup.mk' (IdeleGroup.principalSubgroup F) q = 1 :=
      (QuotientGroup.eq_one_iff q).mpr hq
    rw [← huq, map_mul, hqOne]
    exact (mul_one (QuotientGroup.mk' (IdeleGroup.principalSubgroup F) u :
      IdeleClassGroup F)).symm
  have hOrdinary : (_root_.ideleClassNorm F L).range = ⊤ := by
    rw [_root_.ordinaryIdeleClassNorm_range_eq_relative (K := F) (L := L)]
    exact hRelative
  refine ⟨hOrdinary, ?_⟩
  rw [← GlobalClassFieldTheory.Reciprocity.ideleClassNorm_index_eq_finrank_abelian F L,
    hOrdinary, Subgroup.index_top]

end DedekindZetaZeroFree

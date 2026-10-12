module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/Algebra/Group/NormalizerQuotient/Basic.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
-/

@[expose] public section

namespace Subgroup

variable {G : Type*} [Group G]

abbrev normalizerQuotient (H : Subgroup G) : Type _ :=
  normalizer (H : Set G) ⧸
    H.subgroupOf (normalizer (H : Set G))

abbrev normalizerQuotientMk (H : Subgroup G) :
    normalizer (H : Set G) →* H.normalizerQuotient :=
  QuotientGroup.mk' (H.subgroupOf (normalizer (H : Set G)))

@[simp]
lemma normalizerQuotientMk_apply (H : Subgroup G) (g : normalizer (H : Set G)) :
    H.normalizerQuotientMk g = (g : H.normalizerQuotient) :=
  rfl

lemma normalizerQuotientMk_eq_one_iff (H : Subgroup G)
    (g : normalizer (H : Set G)) :
    H.normalizerQuotientMk g = 1 ↔ (g : G) ∈ H := by
  simp [normalizerQuotientMk, normalizerQuotient, mem_subgroupOf,
    QuotientGroup.eq_one_iff]

lemma normalizerQuotientMk_surjective (H : Subgroup G) :
    Function.Surjective H.normalizerQuotientMk :=
  QuotientGroup.mk'_surjective
    (H.subgroupOf (normalizer (H : Set G)))

end Subgroup

module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.Transport
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassFieldNaturality
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Big Hilbert reciprocity over the realized base field

This leaf specializes the shared reciprocity transport to the actual base
field of the selected big Hilbert class field.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

variable {K : Type} [Field K] [NumberField K]

local instance
    bigHilbertClassFieldReciprocityIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  hilbertClassFieldReciprocityIdeleClassGroupIsMulCommutative

/-- The actual norm range of the selected big Hilbert class field is
the intrinsic big-Hilbert norm subgroup of its actual base field. -/
theorem bigHilbertClassField_ideleClassNorm_range_eq_intrinsic :
    (_root_.ideleClassNorm
      (bigHilbertClassFieldBase K)
      (bigHilbertClassField K)).range =
      bigHilbertClassFieldNormSubgroup
        (K := bigHilbertClassFieldBase K) := by
  rw [bigHilbertClassField_ideleClassNorm_range]
  exact
    bigHilbertClassFieldNormSubgroup_map_ideleClassCongr
      (bigHilbertClassFieldBaseEquiv (K := K))

/-- Global reciprocity identifies the genuine Galois group of the
selected big Hilbert class field with the narrow ideal class group of
the original number field. -/
 noncomputable def bigHilbertClassFieldReciprocityData :
    {e : Gal((bigHilbertClassField K) /
          (bigHilbertClassFieldBase K)) ≃*
        RayClass.NarrowClassGroup K //
      ∀ c : IdeleClassGroup (bigHilbertClassFieldBase K),
        e (globalNormResidueMonoidHom
            (bigHilbertClassFieldBase K)
            (bigHilbertClassField K) c) =
          bigHilbertNarrowClassGroupCongr
            (bigHilbertClassFieldBaseEquiv (K := K)).symm
            (bigHilbertClassFieldQuotientEquivNarrowClassGroup
              (K := bigHilbertClassFieldBase K)
              (QuotientGroup.mk'
                (bigHilbertClassFieldNormSubgroup
                  (K := bigHilbertClassFieldBase K)) c))} := by
  let d := hilbertClassFieldGlobalReciprocityTransportData
    (F := bigHilbertClassFieldBase K)
    (E := bigHilbertClassField K)
    (I := RayClass.NarrowClassGroup K)
    (bigHilbertClassFieldNormSubgroup
      (K := bigHilbertClassFieldBase K))
    (bigHilbertClassField_ideleClassNorm_range_eq_intrinsic
      (K := K))
    ((bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := bigHilbertClassFieldBase K)).trans
      (bigHilbertNarrowClassGroupCongr
        (bigHilbertClassFieldBaseEquiv (K := K)).symm))
  refine ⟨d.1, ?_⟩
  intro c
  exact d.2 c

/-- The reciprocity equivalence from the actual big Hilbert Galois group
to the narrow class group of the original number field. -/
noncomputable def bigHilbertClassFieldGaloisEquivNarrowClassGroup :
    Gal((bigHilbertClassField K) /
        (bigHilbertClassFieldBase K)) ≃*
      RayClass.NarrowClassGroup K :=
  (bigHilbertClassFieldReciprocityData (K := K)).1

/-- Under big-Hilbert reciprocity, the actual global norm-residue
symbol is the narrow ideal class of its idèle-class representative,
transported back to the original number field. -/
@[simp]
theorem bigHilbertClassFieldGaloisEquivNarrowClassGroup_globalNormResidue
    (c : IdeleClassGroup (bigHilbertClassFieldBase K)) :
    bigHilbertClassFieldGaloisEquivNarrowClassGroup (K := K)
        (globalNormResidueMonoidHom
          (bigHilbertClassFieldBase K)
          (bigHilbertClassField K) c) =
      bigHilbertNarrowClassGroupCongr
        (bigHilbertClassFieldBaseEquiv (K := K)).symm
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := bigHilbertClassFieldBase K)
          (QuotientGroup.mk'
            (bigHilbertClassFieldNormSubgroup
              (K := bigHilbertClassFieldBase K)) c)) := by
  exact (bigHilbertClassFieldReciprocityData (K := K)).2 c

/-- Representative form of big-Hilbert reciprocity: the global
norm-residue symbol of an actual idèle maps to its narrow ideal
class, with only the canonical base-field transport remaining. -/
@[simp]
theorem bigHilbertClassFieldGaloisEquivNarrowClassGroup_idele
    (a : IdeleGroup (bigHilbertClassFieldBase K)) :
    bigHilbertClassFieldGaloisEquivNarrowClassGroup (K := K)
        (globalNormResidueMonoidHom
          (bigHilbertClassFieldBase K)
          (bigHilbertClassField K)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup
              (bigHilbertClassFieldBase K)) a)) =
      bigHilbertNarrowClassGroupCongr
        (bigHilbertClassFieldBaseEquiv (K := K)).symm
        (QuotientGroup.mk'
          (RayClass.narrowDenominator
            (K := bigHilbertClassFieldBase K)) a) := by
  calc
    _ = bigHilbertNarrowClassGroupCongr
          (bigHilbertClassFieldBaseEquiv (K := K)).symm
          (bigHilbertClassFieldQuotientEquivNarrowClassGroup
            (K := bigHilbertClassFieldBase K)
            (QuotientGroup.mk'
              (bigHilbertClassFieldNormSubgroup
                (K := bigHilbertClassFieldBase K))
              (QuotientGroup.mk'
                (IdeleGroup.principalSubgroup
                  (bigHilbertClassFieldBase K)) a))) :=
      (bigHilbertClassFieldReciprocityData (K := K)).2 _
    _ = _ :=
      congrArg
        (bigHilbertNarrowClassGroupCongr
          (bigHilbertClassFieldBaseEquiv (K := K)).symm)
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk
          (K := bigHilbertClassFieldBase K) a)

end GlobalClassFields
end GlobalClassFieldTheory

end

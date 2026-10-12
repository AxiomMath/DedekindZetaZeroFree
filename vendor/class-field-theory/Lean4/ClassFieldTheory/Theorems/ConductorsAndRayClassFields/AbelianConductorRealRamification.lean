module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.EmbedsInRayClassFieldIffConductorLe
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.IsAbelianConductorUnique
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Real places in the public abelian conductor
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- A real place belongs to the public conductor precisely when it ramifies
(complexifies) in the extension. -/
theorem IsAbelianConductor.mem_infinitePart_iff_realRamified
    {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    {c : RayClassModulus K}
    (hc : IsAbelianConductor K L c)
    (v : RayClassRealPlace K) :
    v ∈ c.infinitePart ↔ ¬ v.1.IsUnramifiedIn L := by
  let H := GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
    (K := K) (L := L)
  have heq : c =
      ({ finitePart := H.fullConductor.finitePart
         infinitePart := H.fullConductor.infinitePart } : RayClassModulus K) :=
    hc.unique (normFullConductor_isAbelianConductor K L)
  rw [heq]
  change v ∈ H.fullConductor.infinitePart ↔ _
  rw [GlobalClassFieldTheory.GlobalClassFields.ideleClassNormFullConductor_infinitePart_eq_realRamificationLocus]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end ClassFieldTheory

end

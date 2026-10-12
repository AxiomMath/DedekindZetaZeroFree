module

public import ClassFieldTheory.Definitions.LocalClassFieldTheory.TopologicalProfiniteCompletion
public import ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteLocalReciprocity
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.LocalField.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Profinite local reciprocity

For a nonarchimedean local field `K`, the profinite completion of `Kˣ` with
respect to its open finite-index normal subgroups is continuously
multiplicatively equivalent to the topological abelianization of Mathlib's
absolute Galois group of `K`.
-/

noncomputable section

namespace ClassFieldTheory

/-- **Profinite local reciprocity.** The topological profinite completion of
the multiplicative group of a nonarchimedean local field is continuously
multiplicatively equivalent to its absolute Galois abelianization. -/
theorem profiniteLocalReciprocity
    (K : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Nonempty
      (LocalClassFieldTheory.TopologicalProfiniteCompletion Kˣ ≃ₜ*
        _root_.Field.absoluteGaloisGroupAbelianization K) := by
  exact ⟨LocalClassFieldTheory.profiniteLocalReciprocity K⟩

end ClassFieldTheory

end

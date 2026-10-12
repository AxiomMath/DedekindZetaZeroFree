module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# The ray Artin map
-/

noncomputable section

namespace ClassFieldTheory.RayClassFieldRealization

universe u

/-- The Frobenius-normalized ray Artin map. -/
def rayArtin
    {K : Type u} [Field K] [NumberField K]
    {m : RayClassModulus K}
    (R : RayClassFieldRealization K m) :
    RayClassGroup m →* (R.extension ≃ₐ[K] R.extension) :=
  R.artinEquiv.toMonoidHom

end ClassFieldTheory.RayClassFieldRealization

end

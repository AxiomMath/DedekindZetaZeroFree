module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Comparison of public and idelic higher-unit groups

The reader-facing higher-unit group agrees with the group used in the
existing ray-class and idelic implementation. Keep this definitional
comparison at the boundary between the two APIs.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- The public local higher-unit group is the same subgroup as the one used
by the existing ray-class implementation. -/
theorem rayLocalHigherUnitGroup_eq_rayClass
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    rayLocalHigherUnitGroup v n = RayClass.localHigherUnitGroup v n := by
  rfl

end ClassFieldTheory

end

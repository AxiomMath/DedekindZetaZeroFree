module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Monotonicity of local higher-unit groups
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

open NumberField IsDedekindDomain

/-- Deeper local congruence conditions give smaller higher-unit groups. -/
theorem rayLocalHigherUnitGroup_antitone
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    {m n : ℕ} (hmn : m ≤ n) :
    rayLocalHigherUnitGroup v n ≤ rayLocalHigherUnitGroup v m := by
  change RayClass.localHigherUnitGroup v n ≤
    RayClass.localHigherUnitGroup v m
  exact RayClass.localHigherUnitGroup_antitone v hmn

end ClassFieldTheory

end

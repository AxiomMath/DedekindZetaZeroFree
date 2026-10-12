module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# The connected-component quotient of the idèle class group

For a number field `K`, Mathlib's idèle class group is the unit group of
the adele ring modulo principal idèles. Its quotient by the connected
component of `1` is the group appearing in topological global reciprocity.
-/

open scoped NumberField

namespace ClassFieldTheory

universe u

/-- The idèle class group modulo its identity component. -/
abbrev IdeleClassConnectedQuotient (K : Type u) [Field K] [NumberField K] :=
  NumberField.IdeleClassGroup (𝓞 K) K ⧸
    Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K)

end ClassFieldTheory

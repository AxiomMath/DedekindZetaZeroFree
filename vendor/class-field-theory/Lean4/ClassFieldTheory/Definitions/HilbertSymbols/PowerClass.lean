module

public import ClassFieldTheory.Definitions.HilbertSymbols.PowerClassGroup

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Canonical power classes
-/

namespace ClassFieldTheory

universe u

/-- The canonical class of a nonzero field element modulo `n`-th powers. -/
def powerClass (K : Type u) [Field K] (n : ℕ+) : Kˣ →* PowerClassGroup K n := by
  unfold PowerClassGroup
  exact QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range

end ClassFieldTheory

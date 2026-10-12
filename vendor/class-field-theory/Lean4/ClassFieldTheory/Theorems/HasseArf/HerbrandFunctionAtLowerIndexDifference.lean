module

public import ClassFieldTheory.Definitions.HasseArf.HerbrandFunctionAtLowerIndex
public import ClassFieldTheory.HasseArf

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Herbrand-function increment at integral lower indices

The sum starts at index one: the increment from `n` to `n + 1` is the
cardinality of the next lower group divided by that of the zeroth group.
-/

namespace ClassFieldTheory

universe u v

/-- The difference of successive rational Herbrand values is the
normalized size of the next lower ramification group. -/
theorem herbrandFunctionAtLowerIndex_difference
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (n : ℕ) :
    herbrandFunctionAtLowerIndex K A (n + 1) -
        herbrandFunctionAtLowerIndex K A n =
      (Nat.card (lowerRamificationGroup K A (n + 1)) : ℚ) /
        Nat.card (lowerRamificationGroup K A 0) := by
  rw [herbrandFunctionAtLowerIndex_succ]
  ring

end ClassFieldTheory

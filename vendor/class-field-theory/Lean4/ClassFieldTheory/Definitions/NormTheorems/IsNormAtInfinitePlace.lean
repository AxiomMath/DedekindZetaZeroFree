module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Norms at infinite places
-/

open scoped NumberField TensorProduct
open NumberField

namespace ClassFieldTheory

universe u v

/-- A unit of `K` is a norm at an infinite place `w` if its image in the
completion `K_w` is a determinant norm from `K_w ⊗_K L`. -/
def IsNormAtInfinitePlace
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    (w : InfinitePlace K) (x : Kˣ) : Prop :=
  ∃ y : (w.Completion ⊗[K] L)ˣ,
    Algebra.norm w.Completion (y : w.Completion ⊗[K] L) =
      algebraMap K w.Completion (x : K)

end ClassFieldTheory

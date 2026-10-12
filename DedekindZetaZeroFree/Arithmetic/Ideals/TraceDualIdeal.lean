module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Mechanical port of `LeanPool/Odlyzko/Theta/TraceDualIdeal.lean` from
https://github.com/LeanPool/lean-pool at commit
`68aa6ee63d20ad76bcc15f595adfc72949991f06` (Lean 4.35.0-rc3), adapted to rc2.
The original copyright and Apache-2.0 license are retained above; the full
license is included in the repository root `LICENSE`.
Only the namespace, imports and module-visibility syntax have been changed.
-/

noncomputable section

open scoped nonZeroDivisors

open NumberField

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

noncomputable def traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0
    (FractionalIdeal.dual ℤ ℚ
      (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ (Units.ne_zero I))

@[simp]
theorem coe_traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdealUnit K I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ
        (I : FractionalIdeal (𝓞 K)⁰ K) :=
  rfl

@[simp]
theorem traceDualIdealUnit_traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    traceDualIdealUnit K (traceDualIdealUnit K I) = I := by
  ext
  simp

theorem coe_traceDualIdealUnit_eq_dual_one_mul_inv
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdealUnit K I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ
          (1 : FractionalIdeal (𝓞 K)⁰ K) *
        (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [coe_traceDualIdealUnit,
    FractionalIdeal.dual_eq_mul_inv]

theorem absNorm_traceDualIdealUnit
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    FractionalIdeal.absNorm
        (traceDualIdealUnit K I :
          FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.absNorm
          (FractionalIdeal.dual ℤ ℚ
            (1 : FractionalIdeal (𝓞 K)⁰ K)) *
        (FractionalIdeal.absNorm
          (I : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [coe_traceDualIdealUnit_eq_dual_one_mul_inv,
    map_mul, map_inv₀]

theorem absNorm_traceDual_one :
    FractionalIdeal.absNorm
        (FractionalIdeal.dual ℤ ℚ
          (1 : FractionalIdeal (𝓞 K)⁰ K)) =
      ((|(discr K : ℤ)| : ℚ))⁻¹ := by
  have hdifferent :=
    congrArg FractionalIdeal.absNorm
      (coeIdeal_differentIdeal ℤ ℚ K (𝓞 K))
  rw [map_inv₀, FractionalIdeal.coeIdeal_absNorm,
    NumberField.absNorm_differentIdeal K] at hdifferent
  simp_all

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

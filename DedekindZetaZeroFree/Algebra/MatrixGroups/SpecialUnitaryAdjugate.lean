module

public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/LinearAlgebra/UnitaryGroup.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

namespace DedekindZetaZeroFree.TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n] {α : Type*} [CommRing α] [StarRing α]

theorem _root_.Matrix.specialUnitaryGroup.star_eq_adjugate (g : Matrix.specialUnitaryGroup n α) :
    star (g : Matrix n n α) = (g : Matrix n n α).adjugate := by
  have hmem := Matrix.mem_specialUnitaryGroup_iff.mp g.2
  have hmul : (g : Matrix n n α) * star (g : Matrix n n α) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hmem.1
  calc star (g : Matrix n n α)
      = (g : Matrix n n α).adjugate * (g : Matrix n n α) * star (g : Matrix n n α) := by
        rw [Matrix.adjugate_mul, hmem.2, one_smul, Matrix.one_mul]
    _ = (g : Matrix n n α).adjugate := by
        rw [Matrix.mul_assoc, hmul, Matrix.mul_one]

end DedekindZetaZeroFree.TauCeti

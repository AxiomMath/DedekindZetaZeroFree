module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

/-
Copyright (c) 2026 Imperial College London. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Vendored from https://github.com/LeanPool/lean-pool,
commit 68aa6ee63d20ad76bcc15f595adfc72949991f06.
Original source: LeanPool/Odlyzko/DedekindZeta/LocalFactor.lean.
Port to Lean 4.35.0-rc2: local imports and namespace renamed; module visibility syntax removed.
The full upstream Apache-2.0 license is included in LICENSE.
-/

open NumberField

namespace DedekindZetaZeroFree.Odlyzko

noncomputable def inverseNormPower (q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-s)

noncomputable def localFactor (q : ℕ) (s : ℂ) : ℂ :=
  (1 - inverseNormPower q s)⁻¹

lemma norm_inverseNormPower (q : ℕ) (hq : 0 < q) (s : ℂ) :
    ‖inverseNormPower q s‖ = (q : ℝ) ^ (-s.re) := by
  simp [inverseNormPower, Complex.norm_natCast_cpow_of_pos hq]

end DedekindZetaZeroFree.Odlyzko

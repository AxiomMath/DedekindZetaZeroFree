module

public import DedekindZetaZeroFree.Algebra.SymmetricPower.BasisAndTrace
public import DedekindZetaZeroFree.RepresentationTheory.ClassicalGroups.StandardDiagonalAction
public import DedekindZetaZeroFree.RepresentationTheory.SymmetricPowers.Functoriality
public import DedekindZetaZeroFree.Algebra.SymmetricPolynomials.CompleteHomogeneous

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RepresentationTheory/ClassicalGroups/SymmetricPower.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

open Matrix
open scoped TensorProduct

namespace DedekindZetaZeroFree.TauCeti

variable (k : Type) (n d : ℕ)

section CommRing

variable [CommRing k]

noncomputable abbrev symPowerRep :
    Representation k (GL (Fin n) k) (Sym[k]^d (Fin n → k)) :=
  (stdRep k n).symmetricPower d

end CommRing

section Field

variable [Field k]

@[simp]
theorem char_symPowerRep_diagonal (t : Fin n → kˣ) : (symPowerRep k n d).character (diagGL t) =
      MvPolynomial.eval (fun i => (t i : k)) (MvPolynomial.hsymm (Fin n) k d) := by
  rw [Representation.character, Representation.symmetricPower_apply,
    Module.Basis.trace_map_symmetricPower_of_apply (Pi.basisFun k (Fin n))
      (stdRep k n (diagGL t)) (fun i => (t i : k)) d (stdRep_diagGL_apply_basisFun t)]

  rw [eval_hsymm]

end Field

end DedekindZetaZeroFree.TauCeti

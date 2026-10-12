module

public import DedekindZetaZeroFree.RepresentationTheory.Continuous.Characters
public import DedekindZetaZeroFree.RepresentationTheory.Continuous.ConjugateRepresentations
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import DedekindZetaZeroFree.RepresentationTheory.Continuous.TransportOfStructure

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Continuous/Representative.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

open _root_.ContRepresentation

open scoped InnerProductSpace

namespace DedekindZetaZeroFree.TauCeti

open _root_.DedekindZetaZeroFree.TauCeti.ContRepresentation

section Defs

variable {𝕜 G : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]

def IsRepresentative (f : C(G, 𝕜)) : Prop :=
  ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n))) (hπ : Continuous π)
    (v w : EuclideanSpace 𝕜 (Fin n)), f = matrixCoeff π hπ v w

theorem isRepresentative_iff {f : C(G, 𝕜)} :
    IsRepresentative f ↔ ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n)))
      (hπ : Continuous π) (v w : EuclideanSpace 𝕜 (Fin n)), f = matrixCoeff π hπ v w :=
  (Iff.rfl)

variable (𝕜 G) in

def representativeSubmodule : Submodule 𝕜 C(G, 𝕜) :=
  Submodule.span 𝕜 {f : C(G, 𝕜) | IsRepresentative f}

variable (𝕜 G) in

theorem representativeSubmodule_eq_span :
    representativeSubmodule 𝕜 G = Submodule.span 𝕜 {f : C(G, 𝕜) | IsRepresentative f} :=
  (rfl)

theorem mem_representativeSubmodule_of_isRepresentative {f : C(G, 𝕜)} (hf : IsRepresentative f) :
    f ∈ representativeSubmodule 𝕜 G :=
  Submodule.subset_span hf

end Defs

section Membership

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

theorem isRepresentative_matrixCoeff (π : ContRepresentation 𝕜 G V)
    (hπ : Continuous π) (v w : V) :
    IsRepresentative (matrixCoeff π hπ v w) :=
  ⟨Module.finrank 𝕜 V,
    ContRepresentation.congr (stdOrthonormalBasis 𝕜 V).repr.toContinuousLinearEquiv π,
    continuous_congr _ hπ, _, _,
    (matrixCoeff_congr (stdOrthonormalBasis 𝕜 V).repr (continuous_congr _ hπ) v w).symm⟩

end Membership

section Algebra

variable {𝕜 G : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]

variable (𝕜 G) in

theorem isRepresentative_zero : IsRepresentative (0 : C(G, 𝕜)) := by
  simpa only [matrixCoeff_zero_left (ContRepresentation.trivial 𝕜 G 𝕜) continuous_const] using
    isRepresentative_matrixCoeff (ContRepresentation.trivial 𝕜 G 𝕜) continuous_const
      (0 : 𝕜) (0 : 𝕜)

theorem IsRepresentative.star {a : C(G, 𝕜)} (ha : IsRepresentative a) :
    IsRepresentative (star a) := by
  obtain ⟨n, π, hπ, v, w, rfl⟩ := ha
  rw [star_matrixCoeff_eq_matrixCoeff_conjugate (EuclideanSpace.basisFun (Fin n) 𝕜) π hπ v w]
  exact isRepresentative_matrixCoeff _ _ _ _

end Algebra

end DedekindZetaZeroFree.TauCeti

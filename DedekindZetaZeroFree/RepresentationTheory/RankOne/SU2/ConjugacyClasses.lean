module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.TorusConjugacy

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/SU2/ConjugacyClasses.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

namespace DedekindZetaZeroFree.TauCeti

namespace SU2

theorem isConj_iff_trace_eq {g h : SU2} :
    IsConj g h ↔ Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨trace_eq_of_isConj, fun htr => ?_⟩
  obtain ⟨z, hz⟩ := exists_isConj_torusHom g
  obtain ⟨w, hw⟩ := exists_isConj_torusHom h
  have hg := trace_eq_of_isConj hz
  have hh := trace_eq_of_isConj hw
  rw [coe_torusHom] at hg hh
  refine hz.trans (IsConj.trans (isConj_torusHom_iff.mpr ?_) hw.symm)
  exact eq_or_eq_inv_of_trace_torusMatrix_eq (by rw [← hg, ← hh]; exact htr.symm)

theorem isConj_torusExp_iff_cos_eq {θ φ : ℝ} :
    IsConj (torusExp θ) (torusExp φ) ↔ Real.cos φ = Real.cos θ := by
  rw [isConj_iff_trace_eq, trace_torusExp, trace_torusExp]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  exact_mod_cast (mul_left_cancel₀ (a := (2 : ℂ)) (by norm_num) h).symm

theorem exists_isConj_torusExp_mem_Icc (g : SU2) :
    ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi, IsConj g (torusExp θ) := by
  obtain ⟨φ, hφ⟩ := exists_isConj_torusExp g
  refine ⟨Real.arccos (Real.cos φ), ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩, ?_⟩
  exact hφ.trans (isConj_torusExp_iff_cos_eq.mpr
    (Real.cos_arccos (Real.neg_one_le_cos φ) (Real.cos_le_one φ)))

end SU2

end DedekindZetaZeroFree.TauCeti

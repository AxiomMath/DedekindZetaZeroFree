module

public import DedekindZetaZeroFree.Algebra.SymmetricPower.Coordinates
public import DedekindZetaZeroFree.RepresentationTheory.Irreducible.SubrepresentationsAndEigenvectors
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SU2.Weights

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RepresentationTheory/SU2/Irreducible.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

open Finset Matrix Module
open scoped TensorProduct

namespace DedekindZetaZeroFree.TauCeti

namespace SU2

variable (d : ℕ)

noncomputable def mixMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![3 / 5, -(4 / 5); 4 / 5, 3 / 5]

private theorem mixMatrix_apply_ne_zero (i j : Fin 2) : mixMatrix i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [mixMatrix]

theorem mixMatrix_mem : mixMatrix ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mixMatrix, Matrix.mul_apply, Fin.sum_univ_two, map_ofNat] <;> norm_num
  · rw [mixMatrix, Matrix.det_fin_two_of]
    norm_num

noncomputable def mixElement : SU2 := ⟨mixMatrix, mixMatrix_mem⟩

private theorem coe_mixElement :
    (mixElement : Matrix (Fin 2) (Fin 2) ℂ) = mixMatrix := (rfl)

private theorem repr_mulVec_basisFun (A : Matrix (Fin 2) (Fin 2) ℂ) (k l : Fin 2) :
    (Pi.basisFun ℂ (Fin 2)).repr (A *ᵥ Pi.basisFun ℂ (Fin 2) k) l = A l k := by
  simp [Matrix.mulVec_single]

private theorem weightBasis_eq_reindex :
    weightBasis d = ((Pi.basisFun ℂ (Fin 2)).symmetricPower d).reindex (symFinTwoEquiv d) :=
  DFunLike.coe_injective (funext fun i => (weightBasis_apply d i).trans
    (Basis.reindex_apply _ _ i).symm)

private theorem symFinTwoEquiv_symm_last :
    (symFinTwoEquiv d).symm (Fin.last d) = DedekindZetaZeroFree.TauCeti.Sym.ofFn fun _ : Fin d => (0 : Fin 2) := by
  refine Sym.coe_injective ?_
  rw [coe_symFinTwoEquiv_symm_apply, DedekindZetaZeroFree.TauCeti.Sym.coe_ofFn, List.ofFn_const, Multiset.coe_replicate]
  simp

private theorem repr_symPower_mixElement_weightBasis_last_ne_zero (i : Fin (d + 1)) :
    (weightBasis d).repr (symPower d mixElement (weightBasis d i)) (Fin.last d) ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_weightBasis_eq_tprod d i
  rw [hf, weightBasis_eq_reindex, Basis.repr_reindex_apply, symFinTwoEquiv_symm_last,
    symPower_apply_tprod, coe_mixElement, SymmetricPower.repr_basis_symmetricPower_tprod_ofFn_const]
  exact Finset.prod_ne_zero_iff.2 fun j _ => by
    rw [repr_mulVec_basisFun]; exact mixMatrix_apply_ne_zero 0 (f j)

private theorem repr_symPower_mixElement_weightBasis_last_ne_zero' (i : Fin (d + 1)) :
    (weightBasis d).repr (symPower d mixElement (weightBasis d (Fin.last d))) i ≠ 0 := by
  have hf : weightBasis d (Fin.last d) =
      ⨂ₛ[ℂ] (_ : Fin d), Pi.basisFun ℂ (Fin 2) 0 := by
    rw [weightBasis_apply, symFinTwoEquiv_symm_last, Basis.symmetricPower_apply,
      SymmetricPower.tprodOfSym_ofFn]
  rw [hf, weightBasis_eq_reindex, Basis.repr_reindex_apply, symPower_apply_tprod, coe_mixElement]
  exact SymmetricPower.repr_basis_symmetricPower_tprod_const_ne_zero _
    (fun l => by rw [repr_mulVec_basisFun]; exact mixMatrix_apply_ne_zero l 0) _

theorem isIrreducible_symPower : Representation.IsIrreducible (symPower d) := by
  have hnt : Nontrivial (Sym[ℂ]^d(Fin 2 → ℂ)) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [finrank_symPower]; omega)
  refine { eq_bot_or_eq_top := fun σ => ?_ }
  rcases eq_or_ne σ ⊥ with hσ | hσ
  · exact Or.inl hσ
  refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
  rw [Subrepresentation.toSubmodule_top]
  have hW : ∀ (z : Circle) (v : Sym[ℂ]^d(Fin 2 → ℂ)), v ∈ σ.toSubmodule →
      symPower d (torusHom z) v ∈ σ.toSubmodule :=
    fun z _ hv => σ.apply_mem_toSubmodule (torusHom z) hv

  have hex : ∃ i, weightBasis d i ∈ σ.toSubmodule := by
    by_contra hcon

    have hempty : {v : Sym[ℂ]^d(Fin 2 → ℂ) | ∃ i, weightBasis d i = v ∧ v ∈ σ.toSubmodule} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 (by rintro v ⟨i, rfl, hv⟩; exact hcon ⟨i, hv⟩)
    refine hσ (Subrepresentation.toSubmodule_injective ?_)
    rw [Subrepresentation.toSubmodule_bot, eq_span_weightBasis_mem hW, hempty,
      Submodule.span_empty]

  obtain ⟨i, hi⟩ := hex
  have hlast : weightBasis d (Fin.last d) ∈ σ.toSubmodule :=
    weightBasis_mem_of_repr_ne_zero hW (σ.apply_mem_toSubmodule mixElement hi)
      (repr_symPower_mixElement_weightBasis_last_ne_zero d i)
  have hall : ∀ i, weightBasis d i ∈ σ.toSubmodule := fun i =>
    weightBasis_mem_of_repr_ne_zero hW (σ.apply_mem_toSubmodule mixElement hlast)
      (repr_symPower_mixElement_weightBasis_last_ne_zero' d i)
  rw [eq_top_iff, ← (weightBasis d).span_eq]
  exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hall i)

@[simp]
theorem nonempty_equiv_symPower_iff (e : ℕ) :
    Nonempty ((symPower d).Equiv (symPower e)) ↔ d = e := by
  refine ⟨fun ⟨f⟩ => ?_, fun h => h ▸ ⟨Representation.Equiv.refl _⟩⟩
  have hrank : Module.finrank ℂ (Sym[ℂ]^d(Fin 2 → ℂ)) = Module.finrank ℂ (Sym[ℂ]^e(Fin 2 → ℂ)) :=
    f.toLinearEquiv.finrank_eq
  rw [finrank_symPower, finrank_symPower] at hrank
  omega

end SU2

end DedekindZetaZeroFree.TauCeti

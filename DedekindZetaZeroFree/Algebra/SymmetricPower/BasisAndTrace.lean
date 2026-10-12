module

public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Trace
public import DedekindZetaZeroFree.Algebra.SymmetricTuples.Enumeration
public import DedekindZetaZeroFree.Algebra.SymmetricPower.UniversalProperty

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/LinearAlgebra/SymmetricPower/Basis.lean`. Original Apache-2.0 copyright and authors retained.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: import/module surface and TauCeti-owned namespace references only;
root Mathlib extensions are retained. Proof bodies otherwise unchanged.
License: vendor root LICENSE.
-/

open Module
open scoped TensorProduct

universe v w

variable {R : Type} {M : Type v} {κ : Type w} {n : ℕ}

namespace SymmetricPower

noncomputable def orderOfSym (s : Sym κ n) : Fin n → κ :=
  Function.surjInv DedekindZetaZeroFree.TauCeti.Sym.ofFn_surjective s

theorem ofFn_orderOfSym (s : Sym κ n) : DedekindZetaZeroFree.TauCeti.Sym.ofFn (orderOfSym s) = s :=
  Function.surjInv_eq DedekindZetaZeroFree.TauCeti.Sym.ofFn_surjective s

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable (R) in

noncomputable def tprodOfSym (v : κ → M) (s : Sym κ n) : Sym[R]^n M :=
  ⨂ₛ[R] i, v (orderOfSym s i)

@[simp]
theorem tprodOfSym_ofFn (v : κ → M) (f : Fin n → κ) :
    tprodOfSym R v (DedekindZetaZeroFree.TauCeti.Sym.ofFn f) = ⨂ₛ[R] i, v (f i) := by
  obtain ⟨σ, hσ⟩ := DedekindZetaZeroFree.TauCeti.Sym.ofFn_eq_ofFn_iff.1 (ofFn_orderOfSym (DedekindZetaZeroFree.TauCeti.Sym.ofFn f))
  conv_rhs => rw [← hσ]
  exact (tprod_equiv (R := R) σ fun i => v (orderOfSym (DedekindZetaZeroFree.TauCeti.Sym.ofFn f) i)).symm

variable (b : Basis κ R M)

noncomputable def toFinsuppAux : (⨂[R] (_ : Fin n), M) →ₗ[R] (Sym κ n →₀ R) :=
  (Basis.piTensorProduct fun _ : Fin n => b).constr R
    fun f => Finsupp.single (DedekindZetaZeroFree.TauCeti.Sym.ofFn f) 1

private theorem toFinsuppAux_tprod_basis (f : Fin n → κ) :
    toFinsuppAux b (⨂ₜ[R] i, b (f i)) = Finsupp.single (DedekindZetaZeroFree.TauCeti.Sym.ofFn f) 1 := by
  rw [toFinsuppAux, ← Basis.piTensorProduct_apply, Basis.constr_basis]

private theorem toFinsuppAux_reindex (e : Equiv.Perm (Fin n)) :
    (toFinsuppAux b) ∘ₗ (PiTensorProduct.reindex R (fun _ : Fin n => M) e).toLinearMap =
      toFinsuppAux b := by
  refine (Basis.piTensorProduct fun _ : Fin n => b).ext fun f => ?_
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.piTensorProduct_apply,
    PiTensorProduct.reindex_tprod, toFinsuppAux_tprod_basis b fun i => f (e.symm i),
    toFinsuppAux_tprod_basis b f]
  exact congrArg (Finsupp.single · (1 : R)) (DedekindZetaZeroFree.TauCeti.Sym.ofFn_comp_perm e.symm f)

noncomputable def toFinsuppMultilinear :
    MultilinearMap R (fun _ : Fin n ↦ M) (Sym κ n →₀ R) :=
  (toFinsuppAux b).compMultilinearMap (PiTensorProduct.tprod R)

theorem toFinsuppMultilinear_domDomCongr (e : Equiv.Perm (Fin n)) :
    (toFinsuppMultilinear b).domDomCongr e = toFinsuppMultilinear b := by
  refine MultilinearMap.ext fun m => ?_
  have h := congrFun (congrArg DFunLike.coe (toFinsuppAux_reindex b e.symm)) (⨂ₜ[R] i, m i)
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod] at h
  simpa [toFinsuppMultilinear] using h

variable (n) in

noncomputable def toFinsupp : Sym[R]^n M →ₗ[R] (Sym κ n →₀ R) :=
  lift (toFinsuppMultilinear b) (toFinsuppMultilinear_domDomCongr b)

theorem toFinsupp_tprod_basis (f : Fin n → κ) :
    toFinsupp n b (⨂ₛ[R] i, b (f i)) = Finsupp.single (DedekindZetaZeroFree.TauCeti.Sym.ofFn f) 1 := by
  rw [toFinsupp, lift_tprod, toFinsuppMultilinear, LinearMap.compMultilinearMap_apply,
    toFinsuppAux_tprod_basis]

variable (n) in

noncomputable def linearEquivFinsupp : Sym[R]^n M ≃ₗ[R] (Sym κ n →₀ R) :=
  LinearEquiv.ofLinearMap (toFinsupp n b) (Finsupp.linearCombination R (tprodOfSym R b))
    (by
      refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.id_apply]
      rw [Finsupp.linearCombination_single, one_smul, ← ofFn_orderOfSym s, tprodOfSym_ofFn,
        toFinsupp_tprod_basis, ofFn_orderOfSym])
    (by
      apply (LinearMap.cancel_right (LinearMap.range_eq_top.1 (range_mk R (Fin n) M))).1
      refine (Basis.piTensorProduct fun _ : Fin n => b).ext fun f => ?_

      have hmk : mk R (Fin n) M (⨂ₜ[R] i, b (f i)) = ⨂ₛ[R] i, b (f i) := by
        rw [tprod, LinearMap.compMultilinearMap_apply]
      simp [hmk, toFinsupp_tprod_basis, tprodOfSym_ofFn])

private theorem linearEquivFinsupp_symm_single (s : Sym κ n) :
    (linearEquivFinsupp n b).symm (Finsupp.single s 1) = tprodOfSym R b s := by
  rw [linearEquivFinsupp, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    Finsupp.linearCombination_single, one_smul]

variable (n) in

noncomputable def _root_.Module.Basis.symmetricPower : Basis (Sym κ n) R (Sym[R]^n M) :=
  Basis.ofRepr (linearEquivFinsupp n b)

@[simp]
theorem _root_.Module.Basis.symmetricPower_apply (s : Sym κ n) :
    b.symmetricPower n s = tprodOfSym R b s :=
  linearEquivFinsupp_symm_single b s

theorem _root_.Module.Basis.map_symmetricPower_of_apply (f : M →ₗ[R] M) (a : κ → R)
    (hf : ∀ i, f (b i) = a i • b i) (s : Sym κ n) :
    map (ι := Fin n) f (b.symmetricPower n s) =
      ((s : Multiset κ).map a).prod • b.symmetricPower n s := by
  obtain ⟨p, rfl⟩ := DedekindZetaZeroFree.TauCeti.Sym.ofFn_surjective s
  simp [hf, (tprod R).map_smul_univ, List.prod_ofFn]

instance free [Module.Free R M] : Module.Free R (Sym[R]^n M) :=
  Module.Free.of_basis ((Module.Free.chooseBasis R M).symmetricPower n)

theorem finrank_eq [StrongRankCondition R] [Module.Free R M] [Module.Finite R M] :
    Module.finrank R (Sym[R]^n M) = Nat.multichoose (Module.finrank R M) n := by
  classical
  rw [Module.finrank_eq_card_basis ((Module.Free.chooseBasis R M).symmetricPower n),
    Sym.card_sym_eq_multichoose, Module.finrank_eq_card_chooseBasisIndex]

theorem _root_.Module.Basis.trace_map_symmetricPower_of_apply [Fintype κ] [DecidableEq κ]
    (b : Basis κ R M) (f : M →ₗ[R] M) (a : κ → R) (n : ℕ) (hf : ∀ i, f (b i) = a i • b i) :
    LinearMap.trace R (Sym[R]^n M) (map (ι := Fin n) f) =
      ∑ s : Sym κ n, ((s : Multiset κ).map a).prod := by
  classical
  rw [LinearMap.trace_eq_matrix_trace R (b.symmetricPower n), Matrix.trace]
  simp_rw [Matrix.diag_apply, LinearMap.toMatrix_apply,
    Basis.map_symmetricPower_of_apply b f a hf]
  simp only [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]

end CommSemiring

end SymmetricPower

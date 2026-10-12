module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Basic.Complex.Basic

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPWildActualExteriorFactorization.FiniteComparison

theorem slot_eq_normalized
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (P : Submodule ℂ (V →ₗ[ℂ] ℂ)) (hP : Module.finrank ℂ P = 1)
    (ell L : V →ₗ[ℂ] ℂ) (hell : ell ∈ P) (hL : L ∈ P)
    (x₀ : V) (hx₀ : ell x₀ = 1) (y : V) :
    L y = L x₀ * ell y := by
  have hne : (⟨ell, hell⟩ : P) ≠ 0 := by
    intro h
    have he : ell = 0 := congrArg Subtype.val h
    have hx := hx₀
    rw [he, LinearMap.zero_apply] at hx
    exact zero_ne_one hx
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hP
    (x := (⟨ell, hell⟩ : P)) hne (⟨L, hL⟩ : P)
  have hc' : c • ell = L := congrArg Subtype.val hc
  have hc₀ : c = L x₀ := by
    have h := LinearMap.congr_fun hc' x₀
    simpa only [LinearMap.smul_apply, smul_eq_mul, hx₀, mul_one] using h
  calc
    L y = c * ell y := by rw [← hc', LinearMap.smul_apply, smul_eq_mul]
    _ = L x₀ * ell y := by rw [hc₀]

theorem replace_eq_product_of_slot_comparison
    {J : Type*} [DecidableEq J] {V : J → Type*}
    [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (L : MultilinearMap ℂ V ℂ) (S : Finset J)
    (x y : ∀ j, V j) (ell : ∀ j, V j →ₗ[ℂ] ℂ)
    (hnorm : ∀ j ∈ S, ell j (x j) = 1)
    (hslot : ∀ j ∈ S, ∀ z : ∀ i, V i, ∀ u : V j,
      L (Function.update z j u) =
        L (Function.update z j (x j)) * ell j u) :
    L (S.piecewise y x) = L x * ∏ j ∈ S, ell j (y j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    have hnormS : ∀ i ∈ S, ell i (x i) = 1 :=
      fun i hi => hnorm i (Finset.mem_insert_of_mem hi)
    have hslotS : ∀ i ∈ S, ∀ z : ∀ k, V k, ∀ u : V i,
        L (Function.update z i u) =
          L (Function.update z i (x i)) * ell i u :=
      fun i hi => hslot i (Finset.mem_insert_of_mem hi)
    have hbase : Function.update (S.piecewise y x) j (x j) = S.piecewise y x := by
      apply Function.update_eq_self_iff.mpr
      exact (Finset.piecewise_eq_of_notMem S y x hj).symm
    rw [Finset.piecewise_insert, hslot j (Finset.mem_insert_self j S), hbase,
      ih hnormS hslotS, Finset.prod_insert hj]
    ring

end DedekindZetaZeroFree.KPWildActualExteriorFactorization.FiniteComparison

end

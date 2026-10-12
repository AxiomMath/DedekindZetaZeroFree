module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.TameWhittakerSteps.Uniqueness
noncomputable section
set_option autoImplicit false

theorem rank_le_of_surjective_zero_composition
    {k U V W : Type*} [DivisionRing k]
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (i : U →ₗ[k] V) (p : V →ₗ[k] W) (hp : Function.Surjective p)
    (hzero : p.comp i = 0) (a b : ℕ)
    (hV : Module.rank k V ≤ (a + b : ℕ))
    (hi : (b : Cardinal) ≤ Module.rank k (LinearMap.range i)) :
    Module.rank k W ≤ (a : Cardinal) := by
  have hVlt : Module.rank k V < Cardinal.aleph0 :=
    hV.trans_lt Cardinal.natCast_lt_aleph0
  haveI : Module.Finite k V := Module.rank_lt_aleph0_iff.mp hVlt
  haveI : Module.Finite k W := Module.Finite.of_surjective p hp
  have hrank_i_lt : Module.rank k (LinearMap.range i) < Cardinal.aleph0 :=
    (Submodule.rank_le (LinearMap.range i)).trans_lt hVlt
  have hb : b ≤ Module.finrank k (LinearMap.range i) := by
    haveI : Module.Finite k ↥(LinearMap.range i) := Module.rank_lt_aleph0_iff.mp hrank_i_lt
    have h := hi.trans_eq (Module.finrank_eq_rank k ↥(LinearMap.range i)).symm
    exact_mod_cast h
  have hker : Module.finrank k (LinearMap.range i) ≤ Module.finrank k (LinearMap.ker p) :=
    Submodule.finrank_mono (LinearMap.range_le_ker_iff.mpr hzero)
  have hrange : Module.finrank k (LinearMap.range p) = Module.finrank k W := by
    rw [LinearMap.range_eq_top.mpr hp]
    exact finrank_top k W
  have hrn := LinearMap.finrank_range_add_finrank_ker p
  have hfinV : Module.finrank k V ≤ a + b := Module.finrank_le_of_rank_le hV
  have hW : Module.finrank k W ≤ a := by
    have h1 : Module.finrank k W + Module.finrank k (LinearMap.ker p) = Module.finrank k V := by
      rw [← hrange]; exact hrn
    have h2 : b ≤ Module.finrank k (LinearMap.ker p) := hb.trans hker
    omega
  have hcast : (Module.finrank k W : Cardinal) ≤ (a : Cardinal) := by exact_mod_cast hW
  rwa [Module.finrank_eq_rank k W] at hcast

end
end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.TameWhittakerSteps.Uniqueness

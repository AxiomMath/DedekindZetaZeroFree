module

public import Mathlib.Algebra.Module.Lattice
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations

@[expose] public section

namespace DedekindZetaZeroFree

def FullLattice (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :=
  {M : Submodule R (K × K) // Submodule.IsLattice K M}

abbrev RationalLine (K : Type*) [Field K] := Projectivization K (K × K)

def det₂ (K : Type*) [Field K] (x y : K × K) : K :=
  x.1 * y.2 - x.2 * y.1

def determinantSubmodule (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : Submodule R (K × K)) : Submodule R K :=
  Submodule.span R {d : K | ∃ x ∈ M, ∃ y ∈ M, d = det₂ K x y}

def coefficientSubmodule (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : Submodule R (K × K)) (v : K × K) : Submodule R K where
  carrier := {t : K | t • v ∈ M}
  zero_mem' := by simp
  add_mem' := by
    intro s t hs ht
    change (s + t) • v ∈ M
    simpa only [add_smul] using M.add_mem hs ht
  smul_mem' := by
    intro r t ht
    change (r • t) • v ∈ M
    simpa only [smul_assoc] using M.smul_mem r ht

def coordinateLattice (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (I J : FractionalIdeal (nonZeroDivisors R) K) : Submodule R (K × K) :=
  (I : Submodule R K).prod (J : Submodule R K)

def latticeEquivalent (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M N : Submodule R (K × K)) : Prop :=
  ∃ g : (K × K) ≃ₗ[K] (K × K),
    Submodule.map (g.toLinearMap.restrictScalars R) M = N

def lineEquivalent (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : Submodule R (K × K)) (q q' : RationalLine K) : Prop :=
  ∃ g : (K × K) ≃ₗ[K] (K × K),
    Submodule.map (g.toLinearMap.restrictScalars R) M = M ∧
      Projectivization.map g.toLinearMap g.injective q = q'

def latticeSetoid (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    Setoid (FullLattice R K) where
  r M N := latticeEquivalent R K M.val N.val
  iseqv := {
    refl := by
      intro M
      refine ⟨LinearEquiv.refl K (K × K), ?_⟩
      change Submodule.map LinearMap.id M.val = M.val
      exact Submodule.map_id _
    symm := by
      intro M N h
      obtain ⟨g, hg⟩ := h
      refine ⟨g.symm, ?_⟩
      exact (Submodule.map_symm_eq_iff (g.restrictScalars R)).mpr hg
    trans := by
      intro M N P h₁ h₂
      obtain ⟨g, hg⟩ := h₁
      obtain ⟨h, hh⟩ := h₂
      refine ⟨g.trans h, ?_⟩
      change Submodule.map ((h.toLinearMap.restrictScalars R).comp
        (g.toLinearMap.restrictScalars R)) M.val = P.val
      rw [Submodule.map_comp, hg, hh]
  }

def lineSetoid (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : Submodule R (K × K)) : Setoid (RationalLine K) where
  r := lineEquivalent R K M
  iseqv := {
    refl := by
      intro q
      refine ⟨LinearEquiv.refl K (K × K), ?_, ?_⟩
      · change Submodule.map LinearMap.id M = M
        exact Submodule.map_id _
      · exact congrFun Projectivization.map_id q
    symm := by
      intro q q' h
      obtain ⟨g, hg, hq⟩ := h
      refine ⟨g.symm, ?_, ?_⟩
      · exact (Submodule.map_symm_eq_iff (g.restrictScalars R)).mpr hg
      · rw [← hq]
        have hi := congrFun (Projectivization.map_comp g.toLinearMap g.injective
          g.symm.toLinearMap g.symm.injective) q
        simpa only [LinearEquiv.symm_comp, Projectivization.map_id,
          id_eq, Function.comp_apply] using hi.symm
    trans := by
      intro q q' q'' h₁ h₂
      obtain ⟨g, hg, hq⟩ := h₁
      obtain ⟨h, hh, hq'⟩ := h₂
      refine ⟨g.trans h, ?_, ?_⟩
      · change Submodule.map ((h.toLinearMap.restrictScalars R).comp
          (g.toLinearMap.restrictScalars R)) M = M
        rw [Submodule.map_comp, hg, hh]
      · change Projectivization.map (h.toLinearMap.comp g.toLinearMap) _ q = q''
        rw [Projectivization.map_comp g.toLinearMap g.injective
          h.toLinearMap h.injective, Function.comp_apply, hq, hq']
  }

end DedekindZetaZeroFree

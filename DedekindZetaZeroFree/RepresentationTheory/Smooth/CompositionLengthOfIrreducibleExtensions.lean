module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.Length

@[expose] public section

namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps

theorem length_two_of_short_exact
    {k G V W U : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup U] [Module k U]
    (ρ : Representation k G V) (σ : Representation k G W)
    (τ : Representation k G U) [σ.IsIrreducible] [τ.IsIrreducible]
    (i : σ.IntertwiningMap ρ) (p : ρ.IntertwiningMap τ)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (he : Function.Exact i p) :
    Module.length (MonoidAlgebra k G) ρ.asModule = 2 := by
  haveI : IsSimpleModule (MonoidAlgebra k G) σ.asModule := inferInstance
  haveI : IsSimpleModule (MonoidAlgebra k G) τ.asModule := inferInstance

  let i' : σ.asModule →ₗ[MonoidAlgebra k G] ρ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule σ ρ i
  let p' : ρ.asModule →ₗ[MonoidAlgebra k G] τ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule ρ τ p
  have hi' : Function.Injective i' := hi
  have hp' : Function.Surjective p' := hp
  have he' : Function.Exact i' p' := he
  have h := Module.length_eq_add_of_exact i' p' hi' hp' he'
  rw [Module.length_eq_one (MonoidAlgebra k G) σ.asModule,
    Module.length_eq_one (MonoidAlgebra k G) τ.asModule] at h
  rw [h]
  norm_num

end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps

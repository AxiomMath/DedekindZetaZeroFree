module

public import DedekindZetaZeroFree.Analysis.ModifiedBesselKOneThird
public import DedekindZetaZeroFree.Theta.Whittaker.NormalizedFiniteTensorProducts

@[expose] public section

namespace DedekindZetaZeroFree

abbrev KPAdeles (F : Type*) [Field F] [NumberField F] :=
  NumberField.AdeleRing (NumberField.RingOfIntegers F) F

abbrev KPAdditiveQuotient (F : Type*) [Field F] [NumberField F] :=
  KPAdeles F ⧸
    NumberField.AdeleRing.principalSubgroup (NumberField.RingOfIntegers F) F

structure ContinuousAddChar (A : Type*) [AddMonoid A] [TopologicalSpace A]
    extends AddChar A ℂ where
  continuous_toFun : Continuous toFun
  unitary : ∀ a, ‖toFun a‖ = 1

namespace KPReflectionSpec

def NontrivialCharacter {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) : Prop :=
  ∃ a, ψ.toAddChar a ≠ 1

end KPReflectionSpec
end DedekindZetaZeroFree

section

namespace DedekindZetaZeroFree

namespace KPReflectionSpec

def LocalWhittakerLine {N V : Type*} [Group N] [AddCommGroup V]
    [Module ℂ V] [TopologicalSpace V]
    (ρ : Representation ℂ N V) (ψ : N →* ℂ) : Prop :=
  Module.finrank ℂ (localWhittakerSpace N V ρ ψ) = 1

end KPReflectionSpec
end DedekindZetaZeroFree

end

module

public import DedekindZetaZeroFree.Adeles.Characters.RationalNormalizationAndIntegralModels
public import Mathlib.Algebra.Order.Archimedean.Real.Hom

@[expose] public section

noncomputable section

open scoped NumberField BigOperators Classical TensorProduct

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

instance instFactPrimeTracePullbackNatPrimes (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

end DedekindZetaZeroFree

end

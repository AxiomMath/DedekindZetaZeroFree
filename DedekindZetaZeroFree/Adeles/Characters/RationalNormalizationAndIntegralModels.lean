module

public import DedekindZetaZeroFree.Adeles.Characters.TraceCharacter

@[expose] public section

section

noncomputable section

open scoped RestrictedProduct

open IsDedekindDomain

namespace DedekindZetaZeroFree.RationalCharacterNormalization

instance instFactPrimeIntegralModelComparisonNatPrimes (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

end DedekindZetaZeroFree.RationalCharacterNormalization

end

end

section

noncomputable section

open scoped NumberField Classical

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

instance instFactPrimeRationalNormalizationNatPrimes (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

end DedekindZetaZeroFree

end

end

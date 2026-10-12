module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceCharacterConductor
public import DedekindZetaZeroFree.Adeles.Lattices.CompactOpenLevelLattices
public import DedekindZetaZeroFree.Adeles.Characters.TraceCharacterNondegeneracy
public import DedekindZetaZeroFree.Adeles.Characters.TracePairingNondegeneracy
public import DedekindZetaZeroFree.Adeles.Characters.RationalTracePullback

@[expose] public section

noncomputable section

open scoped NumberField BigOperators Classical

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

instance instFactPrimeTraceCharacterSpecNatPrimes (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

end DedekindZetaZeroFree

end

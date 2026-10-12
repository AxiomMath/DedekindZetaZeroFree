module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.IdeleUnitValuationPairing

@[expose] public section

open scoped NumberField Classical BigOperators

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.RepresentationTheory.KPGlobalCubicIdelePairingRaw

noncomputable section

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] exteriorValuationsTopology

namespace CubicIdeleDecomposition

variable (S : Finset (KPHilbert.Place F))

abbrev Out := {v : KPHilbert.Place F // v ∉ S}

variable (e : ∀ v : Out F S, LocalD F v.val ≃* (U F v.val × Multiplicative (ZMod 3)))

variable (he : ∀ v x, (e v x).2 = 1 ↔ x ∈ U F v.val)

attribute [local instance] exteriorValuationsTopology

end CubicIdeleDecomposition

end

end DedekindZetaZeroFree.RepresentationTheory.KPGlobalCubicIdelePairingRaw

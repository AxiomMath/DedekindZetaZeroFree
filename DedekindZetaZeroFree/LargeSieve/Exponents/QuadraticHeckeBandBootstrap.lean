module

public import DedekindZetaZeroFree.LargeSieve.Exponents.ConductorControlledTransfer

@[expose] public section

open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Sieve

theorem hasSieveExponent_one_of_band
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) :
    HasSieveExponent F c Q 1 := by
  exact hasSieveExponent_one_of_core_transfer F hF c Q

end DedekindZetaZeroFree.LargeSieve.Sieve

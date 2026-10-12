module

public import DedekindZetaZeroFree.LargeSieve.Exponents.QuadraticHeckeBandBootstrap

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve

theorem hasSieveExponent_one
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) :
    HasSieveExponent F c Q 1 :=
  hasSieveExponent_one_of_band F hF c Q

end DedekindZetaZeroFree.LargeSieve.Sieve

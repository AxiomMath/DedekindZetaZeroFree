module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section

namespace DedekindZetaZeroFree

theorem primitive12_totallyComplex
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : NumberField.IsTotallyComplex F :=
  NumberField.nrRealPlaces_eq_zero_iff.mp
    (NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by norm_num) hζ)

end DedekindZetaZeroFree

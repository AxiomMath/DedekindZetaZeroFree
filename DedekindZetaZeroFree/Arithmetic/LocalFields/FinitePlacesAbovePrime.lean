module

public import ClassFieldTheory.All

@[expose] public section

set_option autoImplicit false

namespace DedekindZetaZeroFree

open NumberField IsDedekindDomain
open scoped NumberField

abbrev FinitePlacesAbove (K : Type*) (L : Type*)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 K)) :=
  {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = w}

noncomputable def finitePlacesAboveFintype (K : Type*) (L : Type*)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (w : HeightOneSpectrum (𝓞 K)) :
    Fintype (FinitePlacesAbove K L w) := by
  letI := AlgebraicNumberTheory.Valuations.completionTensorDecomposition_extensionFintype
    (K := K) (L := L) (HeightOneSpectrum.adicAbv K w)
    (RayClass.adicAbv_isNontrivial w)
  exact Fintype.ofEquiv _ (finitePlaceExtensionEquivAbove (K := K) (L := L) w)

noncomputable def finitePlacesAboveRationalPrimeFintype (L : Type*)
    [Field L] [NumberField L] (p : Nat.Primes) :
    Fintype (FinitePlacesAbove ℚ L (Rat.HeightOneSpectrum.primesEquiv.symm p)) :=
  finitePlacesAboveFintype ℚ L (Rat.HeightOneSpectrum.primesEquiv.symm p)

end DedekindZetaZeroFree

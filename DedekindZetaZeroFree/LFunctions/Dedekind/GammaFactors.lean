module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

noncomputable section

def zetaGammaFactor (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) *
    Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K *
    Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K

def zetaGammaReciprocal (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (((|NumberField.discr K| : ℤ) : ℂ) ^ (-s / 2)) *
    (Complex.Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K *
    (Complex.Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K

end

end DedekindZetaZeroFree.AbelianQuotient

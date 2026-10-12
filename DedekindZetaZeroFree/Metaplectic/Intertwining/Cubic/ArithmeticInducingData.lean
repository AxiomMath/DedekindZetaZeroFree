module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInductionAndBorelRetraction

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPActualScalarBinding

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

abbrev ActualKPBinding := KPExceptionalRaw.RawFiniteInducingData F ζ hζ q

end
end DedekindZetaZeroFree.KPActualScalarBinding

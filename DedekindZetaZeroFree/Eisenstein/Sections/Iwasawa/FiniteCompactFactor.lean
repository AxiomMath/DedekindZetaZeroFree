module

public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.FullCompactProduct

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalOfKP

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance instCubicRawTopFinite (v : KPHilbert.Place F) :
    TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
  KPAdelicCoverRestrictedProduct.localTopology F ζ hζ v

theorem localCompactFactor_compact_finite (q : HeightOneSpectrum (𝓞 F)) :
    IsCompact (localCompactFactor F ζ hζ (Sum.inr q) :
      Set (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))) := by
  simpa [localCompactFactor] using
    (KPAdelicCoverRestrictedProduct.finiteCompact_compact_open F ζ hζ q).1

end DedekindZetaZeroFree.PrincipalOfKP

end

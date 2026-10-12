module

public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.FullCompactProduct

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalOfKP

open KPAdelicCoverRestrictedProduct

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem continuous_scalarQuotient_comp_amalgamation :
    Continuous ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ)) :=
  (QuotientGroup.continuous_mk).comp QuotientGroup.continuous_mk

end DedekindZetaZeroFree.PrincipalOfKP

end

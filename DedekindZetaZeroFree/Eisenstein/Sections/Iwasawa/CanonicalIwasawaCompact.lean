module

public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.MaximalCompactDecomposition
public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.MaximalCompactness

@[expose] public section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.PrincipalOfKP

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem iwasawaCompactSubgroupMax_isIwasawa :
    KPLiteralRaw.IwasawaCompact F ζ hζ (iwasawaCompactSubgroupMax F ζ hζ) :=
  ⟨iwasawaCompactSubgroupMax_compact F ζ hζ,
    iwasawaCompactSubgroupMax_decomposition F ζ hζ,
    complexCompactLift_mem_iwasawaCompactSubgroupMax F ζ hζ⟩

end DedekindZetaZeroFree.PrincipalOfKP

end

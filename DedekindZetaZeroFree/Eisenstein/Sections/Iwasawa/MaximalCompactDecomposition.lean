module

public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.AdelicPGLDecomposition
public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.BorelSplitting

@[expose] public section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.PrincipalOfKP

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem iwasawaCompactSubgroupMax_decomposition (g : KPLiteralRaw.G F ζ hζ) :
    ∃ (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F)
      (k : iwasawaCompactSubgroupMax F ζ hζ),
      g = (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val := by
  obtain ⟨b,k,hbk⟩ := base_pgl_iwasawa_max F ζ hζ
    (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ g)
  have hmem : g * k.val⁻¹ ∈ KPGlobalTorusFunctionData.borel F ζ hζ := by
    rw [KPGlobalTorusFunctionData.borel, Subgroup.mem_comap]
    rw [map_mul, map_inv, hbk, mul_assoc, mul_inv_cancel, mul_one]
    exact b.property
  obtain ⟨t,x,htx⟩ := borel_lift_splitting F ζ hζ ⟨g * k.val⁻¹,hmem⟩
  refine ⟨t,x,k,?_⟩
  rw [← htx, mul_assoc, inv_mul_cancel, mul_one]

end DedekindZetaZeroFree.PrincipalOfKP

end

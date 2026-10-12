module

public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.FullCompactProduct
public import DedekindZetaZeroFree.Eisenstein.Induction.IwasawaNormTransport

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalOfKP

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem borel_lift_splitting (b : KPGlobalTorusFunctionData.borel F ζ hζ) :
    ∃ (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F),
      b.val = t.val * KPGlobalTorusFunctionData.N F ζ hζ x := by
  exact KPGlobalTorusBorelNormTwistTransport.actual_borel_factorization F ζ hζ b

end DedekindZetaZeroFree.PrincipalOfKP

end

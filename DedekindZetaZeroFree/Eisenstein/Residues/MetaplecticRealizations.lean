module

public import DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree
namespace KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def period (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (μ : Measure (KPAdditiveQuotient F)) (f : Functions F ζ hζ) : ℂ :=
  ∫ x, f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x)) * star (ψ.toAddChar x) ∂μ

end KPLiteralRaw

end DedekindZetaZeroFree

end

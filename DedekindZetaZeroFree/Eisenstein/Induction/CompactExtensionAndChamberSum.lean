module

public import DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def iwasawaTriple (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (g : G F ζ hζ) :
    KPGlobalTorusFunctionData.E F ζ hζ × KPAdeles F × K :=
  let t := Classical.choose (hK.2.1 g)
  let x := Classical.choose (Classical.choose_spec (hK.2.1 g))
  let k := Classical.choose (Classical.choose_spec
    (Classical.choose_spec (hK.2.1 g)))
  (t, x, k)

def compactExtension (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (v : Functions F ζ hζ)
    (s : ℂ) (g : G F ζ hζ) : ℂ :=
  let p := iwasawaTriple F ζ hζ K hK g
  KPGlobalExceptionalParameter.realLogPower
    (((KPGlobalTorusFunctionData.delta F ζ hζ p.1 : NNReal) : ℝ)) s *
    v (p.1.val * p.2.2.val)

end DedekindZetaZeroFree.KPLiteralChamber

end

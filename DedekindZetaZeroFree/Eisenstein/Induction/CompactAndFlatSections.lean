module

public import DedekindZetaZeroFree.Eisenstein.Induction.CompactExtensionAndChamberSum
public import DedekindZetaZeroFree.Eisenstein.Induction.UnipotentInvariance
public import DedekindZetaZeroFree.Metaplectic.Torus.UpperRootNormalization

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem compactExtension_eq_flat
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (s : ℂ) (g : G F ζ hζ) :
    compactExtension F ζ hζ K hK (f.val 0) s g = f.val s g := by
  let t := Classical.choose (hK.2.1 g)
  let x := Classical.choose (Classical.choose_spec (hK.2.1 g))
  let k := Classical.choose (Classical.choose_spec
    (Classical.choose_spec (hK.2.1 g)))
  have hg : g = (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hK.2.1 g)))
  have hv : f.val s g = f.val s (t.val * k.val) := by
    rw [hg, coveredTorus_normalizes_upperRoot, mul_assoc]
    exact literal_unipotent_invariance F ζ hζ K f s _ _
  change KPGlobalExceptionalParameter.realLogPower
    (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) s *
      f.val 0 (t.val * k.val) = _
  rw [hv]
  exact (f.property.2.1 s t k).symm

end DedekindZetaZeroFree.KPLiteralChamber

end

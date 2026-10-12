module

public import DedekindZetaZeroFree.Metaplectic.Kubota.Cubic.ArithmeticCentralEmbedding

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalPrincipalSeries
variable (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))

def actualShell (m : ℤ) : Set (LocalField F q) :=
  {x | (residueCardinality (LocalField F q) : ℝ) ^ (m - 1) <
      KPCubicHaar.abs (LocalField F q) x ∧
    KPCubicHaar.abs (LocalField F q) x ≤ (residueCardinality (LocalField F q) : ℝ) ^ m}

theorem actualAbs_units (v : (LocalField F q)ˣ) :
    localAbs (LocalField F q) v = KPCubicHaar.abs (LocalField F q) (v : LocalField F q) := by
  simp only [localAbs, KPCubicHaar.abs, if_neg v.ne_zero]
  rw [Real.rpow_intCast]
  rfl

end DedekindZetaZeroFree.KPRankOneShellRepair

end

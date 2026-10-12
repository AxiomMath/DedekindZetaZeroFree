module

public import DedekindZetaZeroFree.CharacterSums.Gauss.WeightedUnitShellIntegrals
public import DedekindZetaZeroFree.Algebra.ThreePeriodicBasisCoordinates

@[expose] public section

open scoped NumberField Valued ValuativeRel BigOperators
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPExteriorActualJacquetShellsRaw

open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPExteriorUnitShellIntegrals

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F))

def uniformizerUnit (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π) :
    (LocalField F v)ˣ :=
  Units.mk0 (π : LocalField F v) (by
    intro h
    apply hπ.ne_zero
    exact Subtype.ext h)

def truncationBall (π : (valuation (LocalField F v)).integer) (R : ℕ) : Set (LocalField F v) :=
  {x | ∃ u : (valuation (LocalField F v)).integer,
    x = (π : LocalField F v) ^ (-(R : ℤ)) * (u : LocalField F v)}

def sphericalBall (π : (valuation (LocalField F v)).integer) (e : ℕ) : Set (LocalField F v) :=
  {x | ∃ u : (valuation (LocalField F v)).integer,
    x = (π : LocalField F v) ^ e * (u : LocalField F v)}

def sphericalShell (π : (valuation (LocalField F v)).integer) (e : ℕ) (l : ℤ) :
    Set (LocalField F v) :=
  {x | ∃ u ∈ KPTameGauss.integerUnitShell (LocalField F v),
    x = (π : LocalField F v) ^ ((e : ℤ) - l) * u}

end
end DedekindZetaZeroFree.KPExteriorActualJacquetShellsRaw

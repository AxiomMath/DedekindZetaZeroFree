module

public import DedekindZetaZeroFree.Theta.Periods.NondegenerateCovariantTensorSource

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.FourierContinuation.DetectedDictionary
open MomentSources NonDegenerate
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

def probeSources (D : PeriodSource R N) : AdmissibleFlatSources R :=
  { D.sources with
    flat := fun _ => D.sources.flat D.probe
    common_level := fun _ => D.sources.common_level D.probe
    ordinary := fun _ => D.sources.ordinary D.probe
    exterior_spherical := fun _ => D.sources.exterior_spherical D.probe }

def probeRealization (D : PeriodSource R N) : Realization R (probeSources D) :=
  { D.realization with
    E := fun _ => D.realization.E D.probe
    meromorphic := fun _ => D.realization.meromorphic D.probe
    chamber := fun _ => D.realization.chamber D.probe
    cleared := fun _ => D.realization.cleared D.probe
    clears := fun _ => D.realization.clears D.probe
    smooth := fun _ => D.realization.smooth D.probe
    common_cleared_level := fun _ => D.realization.common_cleared_level D.probe
    analytic := fun _ => D.realization.analytic D.probe
    coefficients := fun _ => D.realization.coefficients D.probe
    coefficients_smooth := fun _ => D.realization.coefficients_smooth D.probe
    compact_smooth_taylor := fun _ => D.realization.compact_smooth_taylor D.probe
    automorphic := fun _ => D.realization.automorphic D.probe }

def repeatedProbe (D : PeriodSource R N) : PeriodSource R N :=
  { D with
    sources := probeSources D
    realization := probeRealization D }

@[simp] theorem repeatedProbe_theta (D : PeriodSource R N) (v : R.A.UnitQuotient) :
    (repeatedProbe D).realization.theta v = D.realization.theta D.probe := rfl

end DedekindZetaZeroFree.FourierContinuation.DetectedDictionary

end

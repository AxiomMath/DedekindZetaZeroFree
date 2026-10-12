module

public import DedekindZetaZeroFree.Eisenstein.Induction.Borel.TwistedAveragingContinuity

@[expose] public section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.TorusChartTransport
open KPGlobalTorusBorelNormTwistTransport
open KPGlobalTorusBorelTwistCompatibilityBorelInduction
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rationalRep (C : ModelData F ζ hζ) :
    KPGlobalTorusPeriodizationInverse.PeriodizationRepresentatives F ζ hζ C :=
  Classical.choose (KPGlobalTorusPeriodizationInverse.rational_representatives_exist F ζ hζ C)

theorem rationalRep_rational (C : ModelData F ζ hζ) :
    ∀ a, ∃ y : Fˣ, (rationalRep F ζ hζ C).lift a =
      KPGlobalTorusPeriodizationInverse.rationalLift F ζ hζ y :=
  Classical.choose_spec
    (KPGlobalTorusPeriodizationInverse.rational_representatives_exist F ζ hζ C)

def chartTerm (C : ModelData F ζ hζ) (s : ℂ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s))
    (g : G F ζ hζ)
    (a : KPGlobalTorusPeriodizationInverse.PeriodizationIndex F ζ hζ C) :
    GroupArch F → ℂ :=
  fun z => (f.val (groupArchChart F ζ hζ z * g)).val.val ((rationalRep F ζ hζ C).lift a).val

end
end DedekindZetaZeroFree.TorusChartTransport

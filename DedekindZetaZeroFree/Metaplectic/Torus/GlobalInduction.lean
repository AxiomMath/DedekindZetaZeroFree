module

public import DedekindZetaZeroFree.Metaplectic.Torus.BorelTwistCompatibility

@[expose] public section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusInducingPlan
noncomputable section
set_option autoImplicit false
attribute [local instance] KPGlobalProductPolarizationCharacter.localCoverTopology

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev ModelData := KPGlobalTorusPeriodizationInverse.ModelData F ζ hζ

local instance torusTop (H : KPGlobalTorusFunctionData.Polarization F ζ hζ) :
    TopologicalSpace (KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ H) :=
  KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ H

local instance compactTop (H : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (K : Subgroup (KPGlobalTorusFunctionData.G F ζ hζ)) :
    TopologicalSpace (KPGlobalTorusBorelTwistCompatibility.CompactLevel F ζ hζ H J K) :=
  KPGlobalTorusBorelTwistCompatibility.compactLevelTopology F ζ hζ H J K

end
end DedekindZetaZeroFree.KPGlobalTorusInducingPlan

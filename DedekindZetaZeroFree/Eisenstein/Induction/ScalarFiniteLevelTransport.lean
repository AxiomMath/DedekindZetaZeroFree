module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.FiniteCoverLevelIdentification

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
def atlasLevel : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ →
    KPMsFixedHaarDisintegration.Level F ζ hζ :=
  (KPMsAngularSourceRecipe.matching_levels F ζ hζ).choose

theorem level_matching (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.globalLevel F ζ hζ U =
      (atlasLevel F ζ hζ U).toOpenSubgroup.toSubgroup.map
        (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype :=
  (KPMsAngularSourceRecipe.matching_levels F ζ hζ).choose_spec U
end DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource

end

module

public import DedekindZetaZeroFree.Eisenstein.Sections.FullProductFlatFamily
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.AngularCoordinates

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField NNReal Topology BigOperators
namespace DedekindZetaZeroFree.KPMsAngularSourceRecipe
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
abbrev G := KPGlobalTorusFunctionData.G F ζ hζ
abbrev Level := KPGlobalTorusFunctionData.FiniteLevel F ζ hζ
abbrev D := KPContFlatFullProductIwasawa.iwasawaData F ζ hζ

def finiteComponent (g : G F ζ hζ) : G F ζ hζ :=
  (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
    (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g))⁻¹ * g

def finiteOffset (σ f : G F ζ hζ) : KPMsFixedHaarDisintegration.Radius :=
  ⟨((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (D F ζ hζ)
    (finiteComponent F ζ hζ (σ⁻¹ * f)) : ℝ≥0) : ℝ),
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))⟩

def frame (a : KPSmoothActualFlowData.GInfinity F) (f : G F ζ hζ) : G F ζ hζ :=
  KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * f

variable {F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

structure OffsetSourceRecipe (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) where
  atlasLevel : Level F ζ hζ → KPMsFixedHaarDisintegration.Level F ζ hζ
  level_matching : ∀ U, KPGlobalTorusFunctionData.globalLevel F ζ hζ U =
    (atlasLevel U).toOpenSubgroup.toSubgroup.map (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype
  height_normalized : ∀ U
    (j : KPMsFixedHaarDisintegration.CuspIndex (H.atlas (atlasLevel U)))
    (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
    (t : ℝ) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
    KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F (((H.atlas (atlasLevel U)).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p,t)) →
    let σ := KPMsActualCuspSource.rationalLift F ζ hζ
      (((H.atlas (atlasLevel U)).cuspAtlas j.1).representative j.2)
    let f := ((H.atlas (atlasLevel U)).representative j.1).val *
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val
    ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (D F ζ hζ)
      (σ⁻¹ * frame F ζ hζ a f) : ℝ≥0) : ℝ) =
      (finiteOffset F ζ hζ σ f).val * Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t)

end DedekindZetaZeroFree.KPMsAngularSourceRecipe

end

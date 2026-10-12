module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.Cusps.AngularShellLaw
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.Cusps.WeightedShapeIntegration
public import DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.CoherentLevelsAndNormInvariance
public import DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.FiniteOffsetConstruction

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DedekindZetaZeroFree.KPMsNativeOffsetMass
open KPMsActualAngularSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)

abbrev nativeFamily := KPMsActualNativeHaarFamily.family F ζ hζ R P

abbrev NativeRecipe := KPMsAngularSourceRecipe.OffsetSourceRecipe F ζ hζ R P
  (nativeFamily F ζ hζ R P)

def nativeRecipe : NativeRecipe F ζ hζ R P :=
  Classical.choice (KPMsAngularSourceRecipe.exists_offset_source_recipe F ζ hζ R P
    (nativeFamily F ζ hζ R P))

abbrev cofinalLevel (V : Level F ζ hζ) := KPShift81CoherentLevel.level F ζ hζ V

abbrev nativeDatum := KPMsAngularSourceRecipe.D F ζ hζ

variable (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ)

abbrev nativeAtlas := (nativeFamily F ζ hζ R P).atlas
  (S.atlasLevel (cofinalLevel F ζ hζ V))
abbrev nativeDisintegration := (nativeFamily F ζ hζ R P).disintegration
  (S.atlasLevel (cofinalLevel F ζ hζ V))
abbrev NativeCusp := KPMsFixedHaarDisintegration.CuspIndex (nativeAtlas F ζ hζ R P S V)

def cuspOffset (j : NativeCusp F ζ hζ R P S V) : KPMsFixedHaarDisintegration.Radius :=
  KPMsAngularSourceRecipe.finiteOffset F ζ hζ
    (KPMsActualCuspSource.rationalLift F ζ hζ
      (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2))
    ((nativeAtlas F ζ hζ R P S V).representative j.1).val

def OffsetAdmissible (Y : ℝ) : Prop :=
  ∀ j : NativeCusp F ζ hζ R P S V,
    KPMsFixedHaarDisintegration.AdmissibleCutoff (nativeAtlas F ζ hζ R P S V)
      (Y / (cuspOffset F ζ hζ R P S V j).val)

def cuspShell (j : NativeCusp F ζ hζ R P S V) (Y : ℝ) :
    Set (KPSmoothLocalQuotientCharts.X F ζ hζ) :=
  KPMsActualCuspSource.cuspEnd (H := nativeFamily F ζ hζ R P)
      (S.atlasLevel (cofinalLevel F ζ hζ V)) j
      (Y / (cuspOffset F ζ hζ R P S V j).val) ∩
    {x | Y / (cuspOffset F ζ hζ R P S V j).val <
      (nativeDisintegration F ζ hζ R P S V).modulus
        (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) x) ∧
      (nativeDisintegration F ζ hζ R P S V).modulus
        (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) x) ≤
          2 * Y / (cuspOffset F ζ hζ R P S V j).val}

def actualFrame (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (x : KPSmoothLocalQuotientCharts.X F ζ hζ) : G F ζ hζ :=
  if hx : x ∈ KPMsActualCuspSource.cuspEnd (H := nativeFamily F ζ hζ R P)
      (S.atlasLevel (cofinalLevel F ζ hζ V)) j
      (Y / (cuspOffset F ζ hζ R P S V j).val) then
    Classical.choose (KPMsActualCuspSource.cusp_lift_exists
      (H := nativeFamily F ζ hζ R P)
      (S.atlasLevel (cofinalLevel F ζ hζ V)) (S.level_matching _) j
      (Y / (cuspOffset F ζ hζ R P S V j).val) x hx)
  else Quotient.out x

def fullCoordinate (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (x : KPSmoothLocalQuotientCharts.X F ζ hζ) : FullOmega F ζ hζ (nativeDatum F ζ hζ) :=
  Quotient.mk _ (⟨framedNormalization F ζ hζ (nativeDatum F ζ hζ)
    (nativeDisintegration F ζ hζ R P S V).radial
    (KPMsActualCuspSource.rationalLift F ζ hζ
      (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2))
    (actualFrame F ζ hζ R P S V j Y x),
    (framedNormalization_normOne_continuous F ζ hζ (nativeDatum F ζ hζ)
      (nativeDisintegration F ζ hζ R P S V).radial _).1 _⟩ :
        NormOne F ζ hζ (nativeDatum F ζ hζ))

def fullShell (Y : ℝ) : Measure (FullOmega F ζ hζ (nativeDatum F ζ hζ)) :=
  ∑ j : NativeCusp F ζ hζ R P S V,
    ENNReal.ofReal (2 * Y) • Measure.map (fullCoordinate F ζ hζ R P S V j Y)
      (R.quotientHaar.restrict (cuspShell F ζ hζ R P S V j Y))

def weightedBeta : Measure (KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)) :=
  (nativeDisintegration F ζ hζ R P S V).beta.withDensity
    (fun ω => ENNReal.ofReal (cuspOffset F ζ hζ R P S V ω.1).val)

end DedekindZetaZeroFree.KPMsNativeOffsetMass

end

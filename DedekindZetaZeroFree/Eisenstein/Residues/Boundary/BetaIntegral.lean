module

public import DedekindZetaZeroFree.Adeles.Quotients.Residual.LevelDisintegration
public import DedekindZetaZeroFree.Eisenstein.Residues.Spherical.BoundaryBetaProjection
public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.Definitions

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualNativeBetaBinding
open KPMsNativeOffsetMass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (D : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

theorem finiteRepresentative_one
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (j : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ D R P H U) :
    KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ D R P H U j 1 =
      KPBoundedCuspFrames.actualFiniteRepresentative
        (KPContFlatCuspIncomingEvaluation.atlas F ζ hζ D R P H U) j := by
  simp only [KPContFlatCuspIncomingEvaluation.finiteRepresentative, map_one, one_mul,
    KPBoundedCuspFrames.actualFiniteRepresentative,
    KPContFlatCuspIncomingEvaluation.sigma, map_inv]

theorem native_beta_integral (hU : cofinalLevel F ζ hζ U = U)
    (φ : KPGlobalTorusFunctionData.G F ζ hζ → ℂ) :
    (∫ω, φ (KPBoundedCuspFrames.actualFiniteRepresentative
      (nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) U) ω.1).val
      ∂(nativeDisintegration F ζ hζ R P (nativeRecipe F ζ hζ R P) U).beta) =
    ∫ω, φ (KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ D R P
      (nativeFamily F ζ hζ R P) U ω.1 1).val
      ∂((nativeFamily F ζ hζ R P).disintegration
        (EisensteinSmoothGerms.ScalarSource.atlasLevel F ζ hζ U)).beta := by
  have he : (nativeRecipe F ζ hζ R P).atlasLevel (cofinalLevel F ζ hζ U) =
      EisensteinSmoothGerms.ScalarSource.atlasLevel F ζ hζ U := by
    rw [hU]
    exact ResidualNativeLevel.atlasLevel_eq F ζ hζ R P (nativeFamily F ζ hζ R P)
      (nativeRecipe F ζ hζ R P) U
  calc
    _ = ∫ω, φ (KPBoundedCuspFrames.actualFiniteRepresentative
          ((nativeFamily F ζ hζ R P).atlas (EisensteinSmoothGerms.ScalarSource.atlasLevel F ζ hζ U)) ω.1).val
          ∂((nativeFamily F ζ hζ R P).disintegration
            (EisensteinSmoothGerms.ScalarSource.atlasLevel F ζ hζ U)).beta :=
      congrArg (fun L : KPMsFixedHaarDisintegration.Level F ζ hζ =>
        ∫ω, φ (KPBoundedCuspFrames.actualFiniteRepresentative
          ((nativeFamily F ζ hζ R P).atlas L) ω.1).val
          ∂((nativeFamily F ζ hζ R P).disintegration L).beta) he
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [finiteRepresentative_one F ζ hζ D R P U]

end DedekindZetaZeroFree.FourierContinuation.ResidualNativeBetaBinding

end

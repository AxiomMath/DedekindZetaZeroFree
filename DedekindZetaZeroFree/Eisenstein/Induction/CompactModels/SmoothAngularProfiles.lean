module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Topology
open MeasureTheory
open DedekindZetaZeroFree.KPMsRationalCompactCrossPairing
namespace DedekindZetaZeroFree.KPMsRationalCompactCrossPairingProof
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem scalarSmooth_continuous
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (f : KPGlobalTorusFunctionData.BorelFunctions F ζ hζ Q)
    (hf : f ∈ scalarSmooth F ζ hζ Q) : Continuous f.val := by
  obtain ⟨p, hp⟩ := hf
  rw [← hp]
  exact KPMsResidualTailRestoration.OutgoingTailL2.AngularBound.scalarSection_continuous_of_levels Q
    (KPMsResidualTailRestoration.OutgoingTailL2.AngularBound.inducedLevel_scalar_continuous Q) p

theorem sourceCore_le_scalarSmooth (D : Iwasawa F ζ hζ) :
    sourceCore F ζ hζ D ≤ scalarSmooth F ζ hζ (sourcePolarization F ζ hζ 0) := by
  unfold sourceCore KPGlobalEisensteinData.hcHeckeCore
  apply iSup_le
  intro J
  apply iSup_le
  intro T
  exact le_trans inf_le_left inf_le_left

theorem sourceCore_continuous {D : Iwasawa F ζ hζ} (f : Vplus F ζ hζ D) :
    Continuous f.val.val :=
  scalarSmooth_continuous _ _ (sourceCore_le_scalarSmooth D f.property)

variable {C : ModelData F ζ hζ} {D : Iwasawa F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (A : RawCompactComparison F ζ hζ C D R P H)

end DedekindZetaZeroFree.KPMsRationalCompactCrossPairingProof

end

module

public import DedekindZetaZeroFree.Eisenstein.Residues.ResidualRepresentations.HilbertOrthogonality
public import DedekindZetaZeroFree.Metaplectic.Torus.ResidualRepresentations.GenuineCentralCharacter
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteCenterSums.Smoothness

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages ThetaExpansion TensorActionSource
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C)
  (plusReference R.A P C) (bad R.A P C)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem coreResidue_regular (x : V) :
    coreResidue R P C x ∈ MomentSources.regularResidualFunctions R := by
  obtain ⟨M, HR, HP, HH, n, U, m, w, B, Z, z, hz, heig, horth, hnative, hcus, he⟩ :=
    core_residue_hilbert_orthogonal_centers R P C x
  let a := fun i j => B i j 0
  let f := ResidualHilbertCenters.finiteCenterSum F ζ hζ M HR HP HH U m w a Z
  have hpin : coreResidue R P C x = fun g ↦
      f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
    funext g
    exact (he g).trans (ResidualHilbertCenters.finiteCenterSum_lift
      F ζ hζ M HR HP HH U m w a Z g).symm
  have hsm := ResidualHilbertCenters.finiteCenterSum_raw_smooth
    F ζ hζ M HR HP HH U m w a Z
  have hm := ResidualHilbertCenters.finiteCenterSum_mem
    F ζ hζ M HR HP HH U m w a Z z hz
    (KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) 0) hnative
  rw [hpin]
  refine ⟨hsm.1, ?_, ?_⟩
  · intro γ g
    have hq : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (KPLiteralRaw.rationalLift F ζ hζ γ * g) =
        KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g :=
      Quotient.sound ⟨⟨_, ⟨KPRationalAdelicSplitting.rationalPGLQuotient F (Quotient.out γ),
        KPRationalAdelicSplitting.rationalPGLHom_mk F ζ hζ (Quotient.out γ)⟩⟩, rfl⟩
    exact congrArg f hq
  · intro ε g
    exact ResidualHilbertCenters.original_word_genuine_left F ζ hζ f
      (hm [] ).1 (ResidualHilbertCenters.finiteCenterSum_genuine
        F ζ hζ M HR HP HH U m w a Z) [] ε g

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end

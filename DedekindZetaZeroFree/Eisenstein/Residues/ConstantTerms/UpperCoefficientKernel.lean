module

public import DedekindZetaZeroFree.Eisenstein.Residues.ResidualRepresentations.HilbertOrthogonality
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteCenterSums.CuspKernel

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory NumberField
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

theorem coreResidue_eq_zero_of_upper_zero (x : V)
    (hzero : ∀g,(∫u:KPAdditiveQuotient F,coreResidue R P C x
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out u)*g)
      ∂ KPWildKernelUpperBound.quotientHaar F)=0) :
    coreResidue R P C x = 0 := by
  obtain ⟨M,HR,HP,HH,n,U,m,w,B,Z,z,hz,heig,horth,hnative,hcus,he⟩ :=
    core_residue_hilbert_orthogonal_centers R P C x
  let a := fun i j => B i j 0
  let f := ResidualHilbertCenters.finiteCenterSum F ζ hζ M HR HP HH U m w a Z
  have hpin (g) : coreResidue R P C x g =
      f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) :=
    (he g).trans (ResidualHilbertCenters.finiteCenterSum_lift
      F ζ hζ M HR HP HH U m w a Z g).symm
  have hf : f = 0 := by
    apply ResidualHilbertCenters.finiteCenterSum_eq_zero_of_upper_zero
      F ζ hζ M HR HP HH U m w a Z z hz horth hnative
    intro g
    change (∫ u : KPAdditiveQuotient F, f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out u) * g))
      ∂ KPWildKernelUpperBound.quotientHaar F) = 0
    simpa only [← hpin] using hzero g
  funext g
  rw [hpin,hf]
  rfl

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end

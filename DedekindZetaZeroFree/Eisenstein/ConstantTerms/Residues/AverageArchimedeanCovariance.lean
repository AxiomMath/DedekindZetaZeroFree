module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CompactAveraging.UpperConstantTerm
public import DedekindZetaZeroFree.Eisenstein.Residues.ResidualRepresentations.AutomorphyAndEigenvalue
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residues.UpperMeanHeightDerivative

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalResidualConstruction KPMsGreenFlux
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "G" => KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
theorem coreResidue_rational_subgroup (x : V)
    (γ : KPSmoothLocalQuotientCharts.rationalSubgroup F R.A.zeta12 R.A.primitive_zeta12)
    (g : G) : coreResidue R P C x (γ.val*g) = coreResidue R P C x g := by
  obtain ⟨M,HR,HP,HH,n,U,m,w,B,Z,z,hz,heig,horth,hnative,hcus,he⟩ :=
    core_residue_hilbert_orthogonal_centers R P C x
  let a := fun i j => B i j 0
  let f := ResidualHilbertCenters.finiteCenterSum F R.A.zeta12 R.A.primitive_zeta12 M HR HP HH U m w a Z
  have hp (g : G) : coreResidue R P C x g =
      f (KPSmoothLocalQuotientCharts.quotientMap F R.A.zeta12 R.A.primitive_zeta12 g) :=
    (he g).trans (ResidualHilbertCenters.finiteCenterSum_lift
      F R.A.zeta12 R.A.primitive_zeta12 M HR HP HH U m w a Z g).symm
  rw [hp,hp]
  exact congrArg f (Quotient.sound ⟨γ,rfl⟩)
local instance (K : Subgroup G) : MeasurableSpace K := borel K
local instance (K : Subgroup G) : BorelSpace K := ⟨rfl⟩
theorem coreResidue_average_upper_arch_covariance
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : KPMsFixedHaarDisintegration.Level F R.A.zeta12 R.A.primitive_zeta12}
    (A : KPFiniteCuspAtlas.Atlas F R.A.zeta12 R.A.primitive_zeta12 hF U)
    (j : Cusps A) (K : Subgroup G) (hK : IsCompact (K : Set G))
    (ν : Measure K) [IsFiniteMeasure ν] (x : V)
    (u : InfinitePlace F → ℝ) (g : G) :
    upperConstantTerm F R.A.zeta12 R.A.primitive_zeta12 (KPWildKernelUpperBound.quotientHaar F)
      (ResidualRawAverage.average F R.A.zeta12 R.A.primitive_zeta12 K ν (coreResidue R P C x))
      ((KPContFlatArchDiagonalMultiplier.aInfinity F R.A.zeta12 R.A.primitive_zeta12 u).val*g) =
    Complex.exp (((2:ℂ)/3)*((∑w,u w:ℝ):ℂ)) *
      upperConstantTerm F R.A.zeta12 R.A.primitive_zeta12 (KPWildKernelUpperBound.quotientHaar F)
      (ResidualRawAverage.average F R.A.zeta12 R.A.primitive_zeta12 K ν (coreResidue R P C x)) g := by
  have hc := (coreResidue_raw_automorphic R P C x).1.1
  have hr := coreResidue_rational_subgroup R P C x
  rw [ResidualAverageCusp.original_upper_average A j K hK ν _ hc hr,
    ResidualAverageCusp.original_upper_average A j K hK ν _ hc hr, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with k
  rw [mul_assoc]
  exact coreResidue_upper_arch_covariance R P C x u (g*k.val)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end

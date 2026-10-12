module

public import DedekindZetaZeroFree.Theta.Periods.SphericalRealizationAndCommonGerms
public import DedekindZetaZeroFree.Theta.Whittaker.FirstRootSphericalSeedData

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
theorem spherical_seed_exists_of_transport

    (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (A : JointExteriorCoefficientSources R N)
    (D : SphericalTransportData R A)
    (hNative : RootDerivatives.SourceNativeLie R A.factorization) :
    ∃ B : FirstRootSphericalSeed R N, RootDerivatives.SourceNativeLie R B.base.factorization := by
  obtain ⟨P⟩ := normalizedSphericalTensor_nonempty R A D
  obtain ⟨L⟩ := sphericalFlatPreimages_nonempty  R A D P
  obtain ⟨B,hB,hdq,hpin,hsource,htheta,hperiod⟩ :=
    normalized_spherical_factorization_exists  R A D P L hNative
  let B' : FirstRootSphericalSeed R N := {
    base := B
    neighborhood := D.tensor.neighborhood
    open_neighborhood := D.tensor.open_neighborhood
    one_neighborhood := D.tensor.one_neighborhood
    spherical_near := by
      intro v y hy
      rw [hdq,hpin v]
      exact P.spherical_near y hy }
  exact ⟨B',hB⟩
end DedekindZetaZeroFree.ThetaExpansion

end

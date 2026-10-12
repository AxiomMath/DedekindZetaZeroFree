module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.BoxIntegral
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Scattering.ChamberHolomorphy
public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.NormOneTorus

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open MomentSources KPGlobalTorusFiniteStages FaithfulSource FaithfulSource.RepairedInducing
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open LiteralSource.CofactorChamber KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false

theorem chamber_right_spec (y : KPGlobalTorusFunctionData.Adeles F) (a : Raw R) :
    scalarQuotient F ζ hζ (amalgamation F ζ hζ (chamberRaw F ζ hζ y * a)) =
      KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ y *
        scalarQuotient F ζ hζ (amalgamation F ζ hζ a) := by
  rw [map_mul, map_mul, LiteralSource.chamberRaw_spec]

theorem current_scattering_integral_exhaustion (x : PlusCore R N P C)
    (a : Raw R) (z : ℂ) (hz : (1 / 3 : ℝ) < z.re) :
    Tendsto (fun Q : Finset (KPFinitePlace F) =>
      ∫ y : KPGlobalTorusFunctionData.Adeles F,
        (LiteralSource.coreFlatInsertion R P C (coreEquiv R N P C x)).val z
          (scalarQuotient F ζ hζ (amalgamation F ζ hζ (chamberRaw F ζ hζ y * a)))
        ∂(KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) atTop
      (𝓝 (LiteralSource.coreScattering R P C (coreEquiv R N P C x) z
        (scalarQuotient F ζ hζ (amalgamation F ζ hζ a)))) := by
  simp_rw [chamber_right_spec]
  have hi := LiteralSource.coreScattering_integrable R P C (coreEquiv R N P C x) z hz
    (scalarQuotient F ζ hζ (amalgamation F ζ hζ a))
  have h := tendsto_setIntegral_of_monotone
    (FullSourceExhaustion.adelicBox_measurable F)
    (FullSourceExhaustion.adelicBox_monotone F) hi.integrableOn
  rw [FullSourceExhaustion.adelicBox_iUnion F, Measure.restrict_univ] at h
  exact h

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end

module

public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.ProfileInsertionAndDescent

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.FourierContinuation.ActualKirillov
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellRepair KPKirillovGenuineSectionCharts KPKirillovProjectorGerms
open KPKirillovOrbitMapFaithful

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : KPFinitePlace F)
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m)
  (s : Sections F ζ hζ q m (phase F q) ℂ)

end DedekindZetaZeroFree.FourierContinuation.ActualKirillov

namespace DedekindZetaZeroFree.FourierContinuation.TensorActions
open MomentSources KPLocalExceptionalConstruction KPLocalStoneVonNeumann
open KPLocalPrincipalSeries KPRankOneShellRepair KPKirillovGenuineSectionCharts
open KPKirillovOrbitMapFaithful
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

theorem sliceLine_le_intrinsicWhittaker (D : TensorActions R N) (q : KPFinitePlace F) :
    D.toTensorHC.sliceLine (Sum.inr q) ≤
      RootEquivariantMaps
        (ActualKirillov.action F R.A.zeta12 R.A.primitive_zeta12 q
          (D.finiteData q).inducing (D.finiteData q).inducing.polarization
          (D.finiteData q).haar (D.finiteData q).haar_integer)
        (KPLocalSmoothRepresentation.upperRoot F R.A.zeta12 R.A.primitive_zeta12 q)
        (ActualKirillov.phase F q) ℂ := by
  rw [ActualKirillov.phase_eq_finiteTrace]
  have hn : KPLocalJacquetImage.root (D.finiteData q).inducing.borel =
      KPLocalSmoothRepresentation.upperRoot F R.A.zeta12 R.A.primitive_zeta12 q := by
    ext t
    exact ((D.finiteData q).inducing.openCell
      (D.finiteData q).inducing.polarization).upper_eq t
  simpa only [finiteWhittaker, hn] using D.sliceLine_le_finiteWhittaker q

end DedekindZetaZeroFree.FourierContinuation.TensorActions

end

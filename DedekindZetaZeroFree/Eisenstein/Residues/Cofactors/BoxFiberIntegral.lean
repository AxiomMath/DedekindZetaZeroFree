module

public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.BoxFiberCylinder
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ChamberIntegrals.RationalAndArchimedeanFubini
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ChamberIntegrals.AdelicBoxExhaustion

@[expose] public section

noncomputable section
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming adelic_measure_box → adelic_measure_box
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming finite_measure_sigmaFinite → finite_measure_sigmaFinite
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming arch_measure_sigmaFinite → arch_measure_sigmaFinite
local instance cofactorArchMeasurable (F : Type) [Field F] [NumberField F] : MeasurableSpace (NumberField.InfiniteAdeleRing F) := borel _
local instance cofactorArchBorel (F : Type) [Field F] [NumberField F] : BorelSpace (NumberField.InfiniteAdeleRing F) := ⟨rfl⟩
open _root_.DedekindZetaZeroFree.KPComplexIntertwinerParameterMajorant renaming forwardSection_real_formula → forwardSection_real_formula
open scoped Classical NumberField TensorProduct BigOperators
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber
open KPLocalPrincipalSeries KPGlobalTorusFiniteStages KPLocalExceptionalConstruction
open KPGlobalResidualConstruction
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem box_fiber_integral (E Q : Finset (KPFinitePlace F)) (hE : C.exceptional ⊆ E)
    (hEQ : E ⊆ Q) (hD : localDifferentSupport F ⊆ (Q : Set _))
    (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
      (C.canonical q.val).iwasawa .plus)
    (z : ℂ) (hz : KPRankOneShellContinuation.convergenceHalfPlane .plus z)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    (∫ x : KPGlobalTorusFunctionData.Adeles F,
      (coreFlatFiber R P C (cofactorSourceCore R P C E hE φ) z
        (chamberRaw F ζ hζ x)).val.val t
        ∂(KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) =
      (∫ u : ∀ q : Q, LocalField F q.val,
        ActualCofactor.rationalChamberIntegrand F ζ hζ P C Q (hE.trans hEQ)
          (ExteriorTensorHaar.enlargedProfiles F ζ hζ P C E Q hE φ z) t z u
          ∂Measure.pi (fun q : Q => localNormalizedHaar F q.val)) *
      ∏ _w : InfinitePlace F, ∫ u : ℂ, TraceBox.complexIntegrand z u
        ∂((2 : ENNReal) • KPCplxCharacterHaar.euclideanArea) := by
  let ψ := ExteriorTensorHaar.enlargedProfiles F ζ hζ P C E Q hE φ z
  let f := ActualCofactor.rationalChamberIntegrand F ζ hζ P C Q (hE.trans hEQ) ψ t z
  have hpin : (∫ x : KPGlobalTorusFunctionData.Adeles F,
      (coreFlatFiber R P C (cofactorSourceCore R P C E hE φ) z
        (chamberRaw F ζ hζ x)).val.val t
        ∂(KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) =
      ∫ x : KPGlobalTorusFunctionData.Adeles F, TraceBox.archCylinder F z x.1 *
        f (fun q => x.2 q.val)
        ∂(KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (FullSourceExhaustion.adelicBox_measurable F Q)] with x hx
    exact box_fiber_cylinder R P C E Q hE hEQ φ x hx z t
  rw [hpin]
  let := finite_measure_sigmaFinite F
  let := arch_measure_sigmaFinite F
  let e : (InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ≃ₜ
      KPGlobalTorusFunctionData.Adeles F := Homeomorph.refl _
  have he : @MeasurableEmbedding (InfiniteAdeleRing F ×
      IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) (KPGlobalTorusFunctionData.Adeles F)
      inferInstance inferInstance (fun a => a) := e.measurableEmbedding
  rw [adelic_measure_box F Q, he.integral_map]
  change (∫ x : InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F,
    TraceBox.archCylinder F z x.1 * f (fun q => x.2 q.val) ∂_) = _
  rw [integral_prod_mul (TraceBox.archCylinder F z)
    (fun a : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F => f (fun q => a q.val)), KPAdditiveHaar.finiteMeasure_chart F Q hD,
    (KPAdditiveHaar.chartMap_isOpenEmbedding F Q).measurableEmbedding.integral_map]
  have hc : (fun b : KPAdditiveHaar.Chart F Q =>
      f (fun q => KPAdditiveHaar.chartMap F Q b q.val)) = fun b => f b.1 := by
    funext b
    apply congrArg f
    funext q
    change (if h : q.val ∈ Q then b.1 ⟨q.val,h⟩ else _) = b.1 q
    rw [dite_eq_left q.property]
  rw [hc, ChamberReferenceInsertion.rational_chamber_chart_integral F ζ hζ P C Q
    (hE.trans hEQ) ψ t z hz, ChamberReferenceInsertion.arch_chamber_integral F ζ hζ]
  rw [← (ActualCofactor.rational_finite_chamber_integral F ζ hζ P C Q (hE.trans hEQ) ψ t z hz).2]
  exact mul_comm _ _

end DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber

end

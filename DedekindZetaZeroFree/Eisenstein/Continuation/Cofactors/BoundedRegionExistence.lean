module

public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.BoxFiberIntegral

@[expose] public section

noncomputable section
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming adelic_measure_box → adelic_measure_box
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming finite_measure_sigmaFinite → finite_measure_sigmaFinite
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox renaming arch_measure_sigmaFinite → arch_measure_sigmaFinite
local instance cofactorProducerArchMeasurable (F : Type) [Field F] [NumberField F] : MeasurableSpace (NumberField.InfiniteAdeleRing F) := borel _
local instance cofactorProducerArchBorel (F : Type) [Field F] [NumberField F] : BorelSpace (NumberField.InfiniteAdeleRing F) := ⟨rfl⟩
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

theorem exists_current_boxed_cofactor (E : Finset (KPFinitePlace F))
    (hE : C.exceptional ⊆ E) (hD : localDifferentSupport F ⊆ (E : Set _)) :
    ∃ (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
        (C.canonical q.val).iwasawa .plus)
      (t : KPGlobalTorusFunctionData.E F ζ hζ) (b : ℂ → ℂ),
      KPGlobalTorusFunctionData.delta F ζ hζ t = 1 ∧
      MeromorphicOn b Set.univ ∧ AnalyticAt ℂ b 0 ∧ b 0 ≠ 0 ∧
      ∀ (Q : Finset (KPFinitePlace F)), E ⊆ Q → ∀ z : ℂ,
        KPRankOneShellContinuation.convergenceHalfPlane .plus z →
        (∫ x : KPGlobalTorusFunctionData.Adeles F,
          (coreFlatFiber R P C (cofactorSourceCore R P C E hE φ) z
            (chamberRaw F ζ hζ x)).val.val t
            ∂(KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) =
          KPGlobalFiniteSIntertwiner.enlargementFactor F E Q z * b z := by
  let J := fun q : E => ActualFullCompactTransport.fullCompactIwasawa F ζ hζ q.val (C.canonical q.val)
  obtain ⟨φ,t,b,ht,hm,ha,hn,hb⟩ :=
    TransportedRationalCofactor.exists_transported_integral_cofactor F ζ hζ P C E hE J
  refine ⟨φ,t,b,ht,hm,ha,hn,?_⟩
  intro Q hEQ z hz
  have hD' : localDifferentSupport F ⊆ (Q : Set _) := fun q hq => hEQ (hD hq)
  rw [box_fiber_integral R P C E Q hE hEQ hD' φ z hz t,
    ExteriorTensorHaar.actual_finite_euler_enlargement F ζ hζ P C E Q hE hEQ hD φ t z hz,
    mul_assoc]
  apply congrArg (KPGlobalFiniteSIntertwiner.enlargementFactor F E Q z * ·)
  have he : b z =
      (∫ u : ∀ q : E, LocalField F q.val,
        ActualCofactor.rationalChamberIntegrand F ζ hζ P C E hE
          (ActualFullCompactTransport.fullCompactProfiles F ζ hζ P C E φ z) t z u
          ∂Measure.pi (fun q : E => localNormalizedHaar F q.val)) *
      ∏ _w : InfinitePlace F, ∫ u : ℂ, TraceBox.complexIntegrand z u
        ∂((2 : ENNReal) • KPCplxCharacterHaar.euclideanArea) := by
    simpa only [ActualCofactor.rationalChamberIntegrand,
      ActualFullCompactTransport.fullCompactProfiles, FiniteSourceTransport.parameterSource_extension,
      TraceBox.complexIntegrand, J] using (hb z hz).2
  exact he.symm

end DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber

end

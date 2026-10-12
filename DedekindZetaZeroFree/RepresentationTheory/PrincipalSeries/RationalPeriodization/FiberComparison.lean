module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.RootIntegrals.ArithmeticNormalization
public import DedekindZetaZeroFree.Metaplectic.Kubota.Induction.UnitaryRationalFiberComparison

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal TensorProduct
open NumberField MeasureTheory ValuativeRel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources KPGlobalTorusFiniteStages
open PrincipalOfKP.ResidueCoreBridge.CanonicalBinding
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

def integerHaar (q : KPFinitePlace F) : Measure (q.adicCompletion F) :=
  (ENNReal.ofReal (PoissonS.integerVolume F q))⁻¹ • N.finiteHaar q

instance integerHaar_add (q : KPFinitePlace F) : (integerHaar R N q).IsAddHaarMeasure := by
  letI := N.finiteHaar_add q
  apply Measure.IsAddHaarMeasure.smul
  · exact ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  · exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (PoissonS.integerVolume_pos F q))

theorem integerHaar_integer (q : KPFinitePlace F) :
    integerHaar R N q ((valuation (q.adicCompletion F)).integer : Set (q.adicCompletion F)) = 1 := by
  rw [integerHaar, Measure.smul_apply, FourierContinuation.integer_eq_normBall, N.finite_mass]
  change (ENNReal.ofReal (PoissonS.integerVolume F q))⁻¹ * ENNReal.ofReal (PoissonS.integerVolume F q) = 1
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (PoissonS.integerVolume_pos F q)) ENNReal.ofReal_ne_top

def imageData (q : KPFinitePlace F) : LocalImageData R q where
  inducing := { C.canonical q with polarization := C.polarization q }
  haar := integerHaar R N q
  haar_integer := integerHaar_integer R N q

abbrev Fiber : KPHilbert.Place F → Type :=
  KPGlobalResidualConstruction.ScalarAbsorption.FullV
    (LocalFiber F R.A.zeta12 R.A.primitive_zeta12 P C)

abbrev sourceFiber : KPHilbert.Place F → Type
  | Sum.inl _ => ℂ
  | Sum.inr q => KPLocalStoneVonNeumann.InducedModule (imageData R N P C q).inducing.polarization

abbrev reference : ∀ p, Fiber R P C p :=
  KPGlobalResidualConstruction.ScalarAbsorption.fullReference
    (LocalFiber F R.A.zeta12 R.A.primitive_zeta12 P C)
    (localReference F R.A.zeta12 R.A.primitive_zeta12 P C)

abbrev bad : Finset (KPHilbert.Place F) :=
  badSet F R.A.zeta12 R.A.primitive_zeta12 P C

def finiteTensorMap :
    RestrictedTensorSimple.Core (LocalFiber F R.A.zeta12 R.A.primitive_zeta12 P C)
      (localReference F R.A.zeta12 R.A.primitive_zeta12 P C) C.exceptional →ₗ[ℂ]
      KPGlobalTorusPeriodizationInverse.ProductUnitary F R.A.zeta12 R.A.primitive_zeta12 P :=
  (KPGlobalResidualConstruction.TorusCoreComparison.finiteTensorCore_lift_exists
    F R.A.zeta12 R.A.primitive_zeta12 P C).choose

theorem finiteTensorMap_stage (s : Finset (KPFinitePlace F)) (hs : C.exceptional ⊆ s)
    (x : RestrictedTensorSimple.Stage (LocalFiber F R.A.zeta12 R.A.primitive_zeta12 P C) s) :
    finiteTensorMap R P C (RestrictedTensorSimple.stageInclusion _ _ _ ⟨s, hs⟩ x) =
      finiteTensorRealization F R.A.zeta12 R.A.primitive_zeta12 P C s hs x :=
  (KPGlobalResidualConstruction.TorusCoreComparison.finiteTensorCore_lift_exists
    F R.A.zeta12 R.A.primitive_zeta12 P C).choose_spec.2.2 s hs x

def finiteCoreEquiv :
    RestrictedTensorSimple.Core (Fiber R P C) (reference R P C) (bad R P C) ≃ₗ[ℂ]
      RestrictedTensorSimple.Core (LocalFiber F R.A.zeta12 R.A.primitive_zeta12 P C)
        (localReference F R.A.zeta12 R.A.primitive_zeta12 P C) C.exceptional := by
  change RestrictedTensorSimple.Core
    (KPGlobalResidualConstruction.ScalarAbsorption.FullV
      (LocalFiber F R.A.zeta12 R.A.primitive_zeta12 P C))
    (KPGlobalResidualConstruction.ScalarAbsorption.fullReference
      (LocalFiber F R.A.zeta12 R.A.primitive_zeta12 P C)
      (localReference F R.A.zeta12 R.A.primitive_zeta12 P C))
    (badSet F R.A.zeta12 R.A.primitive_zeta12 P C) ≃ₗ[ℂ]
      RestrictedTensorSimple.Core (LocalFiber F R.A.zeta12 R.A.primitive_zeta12 P C)
        (localReference F R.A.zeta12 R.A.primitive_zeta12 P C) C.exceptional
  rw [badSet_eq_fullBad]
  exact KPGlobalResidualConstruction.ScalarAbsorption.equivalence
    (A := InfinitePlace F)
    (LocalFiber F R.A.zeta12 R.A.primitive_zeta12 P C)
    (localReference F R.A.zeta12 R.A.primitive_zeta12 P C) C.exceptional
    (fun q _ => localReference_ne_zero F R.A.zeta12 R.A.primitive_zeta12 P C q)

def comparisonSmooth :
    RestrictedTensorSimple.Core (Fiber R P C) (reference R P C) (bad R P C) →ₗ[ℂ]
      KPGlobalResidualConstruction.smoothRationalFiber F R.A.zeta12 R.A.primitive_zeta12 :=
  (productUnitaryToRational F R.A.zeta12 R.A.primitive_zeta12 P).comp
    ((finiteTensorMap R P C).comp (finiteCoreEquiv R P C).toLinearMap)

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end

module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactDerivatives.TensorIdentity
public import DedekindZetaZeroFree.Eisenstein.Induction.SmoothSections.AutomorphicLift
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.MatrixFlowDerivativeIdentification
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.Iwasawa.FullAngularCuspCoordinates

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped Classical NumberField Topology ContDiff
namespace DedekindZetaZeroFree.FourierContinuation.ResidualSphericalGeometry
open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra KPContSectorSmoothFramesSupport
open _root_.DedekindZetaZeroFree.KPContActualSphericalRightFieldIdentification renaming exponential_base_smooth → exponential_base_smooth
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (V : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
def reindex (a : KPSmoothActualFlowData.LieCoordinates F) :
    KPSmoothLocalQuotientCharts.Coordinates F :=
  fun b => a (KPMsClearedTruncationL2.NativeWordBridge.basisEquiv F b)
theorem reindex_smooth : ContDiff ℝ (⊤ : ℕ∞) (reindex F) := by
  apply contDiff_pi.mpr
  intro b
  change ContDiff ℝ (⊤ : ℕ∞) (fun a : KPSmoothActualFlowData.LieCoordinates F =>
    a (KPMsClearedTruncationL2.NativeWordBridge.basisEquiv F b))
  fun_prop

theorem exponential_reindex (a : KPSmoothActualFlowData.LieCoordinates F) :
    KPSmoothLocalQuotientCharts.matrixExp F (reindex F a) =
      KPSmoothActualFlowData.exponential F a := by
  funext v
  have hm : KPSmoothLocalQuotientCharts.lieMatrix F (reindex F a) v =
      KPSmoothActualFlowData.sl2Matrix (fun j => a (v,j)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPSmoothLocalQuotientCharts.lieMatrix, KPSmoothActualFlowData.sl2Matrix,
      reindex, KPMsClearedTruncationL2.NativeWordBridge.basisEquiv,
      finProdFinEquiv, Complex.mk_eq_add_mul_I, mul_comm]
  simp only [KPSmoothLocalQuotientCharts.matrixExp, KPSmoothActualFlowData.exponential,
    KPSmoothActualFlowData.matrixExponential, hm]

def originalScalar (Z : smoothSections F ζ hζ V R P H) :
    KPSmoothActualFlowData.X F ζ hζ → ℂ :=
  ((smoothS F ζ hζ V R P H).symm Z).val.val ∘
    KPContSectorQuotientRelationsComparison.piTilde F ζ hζ V

theorem originalScalar_continuous (Z : smoothSections F ζ hζ V R P H) :
    Continuous (originalScalar F ζ hζ V R P H Z) := by
  have hc := (KPContSectorLineL2Isometry.continuous_iff F ζ hζ V R P H Z.val).mp
    (fun i => (Z.property i).continuous)
  rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm] at hc
  exact hc.comp (KPContSectorQuotientRelationsComparison.piTilde_continuous F ζ hζ V)

theorem originalScalar_smooth (Z : smoothSections F ζ hζ V R P H) :
    KPSmoothActualFlowData.SmoothAutomorphic F ζ hζ
      (originalScalar F ζ hζ V R P H Z) := by
  refine ⟨originalScalar_continuous F ζ hζ V R P H Z, ?_⟩
  intro x
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨e, he⟩ := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_product_splitting F ζ hζ
    obtain ⟨⟨a,c⟩,rfl⟩ := e.surjective g
    have hex (b : KPSmoothActualFlowData.GInfinity F) :
        e (b,1) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ b := by
      rw [he]
      simp
    have hprod (y : KPSmoothActualFlowData.LieCoordinates F) :
        e (a,c) * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPSmoothActualFlowData.exponential F y) =
        e (a * KPSmoothActualFlowData.exponential F y,c) := by
      rw [← hex, ← map_mul]
      congr 1
      simp
    have heval (y : KPSmoothActualFlowData.LieCoordinates F) :
        originalScalar F ζ hζ V R P H Z
          (KPSmoothActualFlowData.rightTranslate F ζ hζ
            (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
              (KPSmoothActualFlowData.exponential F y))
            (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (e (a,c)))) =
        (J F ζ hζ V ((smoothS F ζ hζ V R P H).symm Z).val).val
          (KPMsFixedHaarDisintegration.archBasepoint F
            (a * KPSmoothActualFlowData.exponential F y),c) := by
      change ((smoothS F ζ hζ V R P H).symm Z).val.val
        (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ V
          (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
            (e (a,c) * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
              (KPSmoothActualFlowData.exponential F y)))) = _
      rw [hprod, he]
      exact group_lift_formula F ζ hζ V _ _ _
    have hs := (exponential_base_smooth a).comp (reindex_smooth F)
    simp only [Function.comp_def, exponential_reindex] at hs
    convert (((smoothS F ζ hζ V R P H).symm Z).property c).comp hs using 1
    funext y
    exact heval y

theorem originalScalar_lift (Z : smoothSections F ζ hζ V R P H)
    (g : KPSmoothActualFlowData.G F ζ hζ) :
    originalScalar F ζ hζ V R P H Z
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) =
    KPContActualCommonDiskRightHolomorphy.lift F ζ hζ V R P H Z.val g := by
  simp only [originalScalar, Function.comp_apply, KPContActualCommonDiskRightHolomorphy.lift,
    KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
  rfl

theorem originalScalar_mem_smoothSpace (Z : smoothSections F ζ hζ V R P H) :
    originalScalar F ζ hζ V R P H Z ∈ KPMsClearedTruncationL2.smoothSpace F ζ hζ
      (KPGlobalResidualConstruction.ActualSectionLift.nativeLevel F ζ hζ V) := by
  refine ⟨originalScalar_smooth F ζ hζ V R P H Z, ?_, ?_⟩
  · intro g u
    rw [originalScalar_lift, originalScalar_lift]
    exact KPGlobalResidualConstruction.ActualSectionLift.lift_native_level
      F ζ hζ V R P H Z.val g u.val u.property
  · intro g ε
    rw [originalScalar_lift, originalScalar_lift]
    have hc : g * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε =
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g :=
      Subgroup.mem_center_iff.mp
        (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε,rfl⟩) g
    rw [hc]
    exact KPGlobalResidualConstruction.ActualSectionLift.lift_genuine F ζ hζ V R P H Z.val ε g

open _root_.DedekindZetaZeroFree.KPContSectorArchSphericalFibers renaming mem_KInfinity_iff_stab → mem_KInfinity_iff_stab
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FiniteSlabFullAngularHaar renaming compactSubgroup_eq_origin_stabilizer → compactSubgroup_eq_origin_stabilizer
open ResidualCompactTensor
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.FullSixCoercivity renaming compactTensor → compactTensor

theorem originalScalar_compact (Z : smoothSections F ζ hζ V R P H)
    (g : KPSmoothActualFlowData.G F ζ hζ) (k : KPMsGreenFlux.K F) :
    originalScalar F ζ hζ V R P H Z (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (g * KPMsGreenFlux.compactInsertion F ζ hζ k)) =
    originalScalar F ζ hζ V R P H Z (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
  let a : KPContSectorArchSphericalFibers.KInfinity F := ⟨fun w => (k w).val, by
    apply (mem_KInfinity_iff_stab F _).mpr
    intro i
    rw [← compactSubgroup_eq_origin_stabilizer]
    exact (k (KPCusp.complexPlace F i)).property⟩
  apply congrArg (((smoothS F ζ hζ V R P H).symm Z).val.val)
  unfold KPContSectorQuotientRelationsComparison.piTilde
  apply congrArg (KPContSectorQuotientRelationsComparison.e F ζ hζ V)
  rw [KPContSectorCoveredQuotientVocabulary.coveredActualMap_mk,
    KPContSectorCoveredQuotientVocabulary.coveredActualMap_mk]
  apply Eq.symm
  apply DoubleCoset.eq.mpr
  refine ⟨1, Subgroup.one_mem _, KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a.val,
    ?_, by simp [a, KPMsGreenFlux.compactInsertion]⟩
  apply Subgroup.subset_closure
  exact Set.mem_union_left _ ⟨a.val, a.property, rfl⟩

end DedekindZetaZeroFree.FourierContinuation.ResidualSphericalGeometry

end

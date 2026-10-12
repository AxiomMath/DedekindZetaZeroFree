module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LevelProfiles.MultilinearIntegration

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open MomentSources KPLocalPrincipalSeries KPGlobalTorusFiniteStages FaithfulSource FaithfulSource.RepairedInducing
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem parameter_box_integrable_and_integral
    (Q : Finset (KPFinitePlace F)) (hQ : C.exceptional ⊆ Q)
    (hD : localDifferentSupport F ⊆ (Q : Set _))
    (J : ∀ q, IwasawaData (C.canonical q).borel) (a : Raw R)
    (t : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12)
    (z : ℂ) (hz : z ∈ KPContinuation.spectralDomain)
    (y : RestrictedTensorSimple.Stage (Plus R N P C) (fullLevel R P C Q hQ).val) :
    Integrable (fun x : KPGlobalTorusFunctionData.Adeles F =>
      parameterStageIntegrand R N P C J (fullLevel R P C Q hQ) a t z y
        (fun j => rootCoordinate R x j.val))
      ((KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) ∧
    (∫ x : KPGlobalTorusFunctionData.Adeles F,
      parameterStageIntegrand R N P C J (fullLevel R P C Q hQ) a t z y
        (fun j => rootCoordinate R x j.val)
      ∂(KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) =
      (parameterStage R N P C J (fullLevel R P C Q hQ) a z y).val.val t := by
  let ev : KPGlobalResidualConstruction.smoothRationalFiber F R.A.zeta12 R.A.primitive_zeta12 →ₗ[ℂ] ℂ :=
    { toFun f := f.val.val t
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let L : MultilinearMap ℂ (fun j : (fullLevel R P C Q hQ).val => Fiber R P C j) ℂ :=
    ((ev.comp (comparisonSmooth R P C)).comp
      (RestrictedTensorSimple.stageInclusion (Fiber R P C) (reference R P C) (bad R P C) (fullLevel R P C Q hQ))).compMultilinearMap
      (PiTensorProduct.tprod ℂ)
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    have hi := full_multilinear_integral R N P C Q hQ hD (fun j : (fullLevel R P C Q hQ).val => inducingCoordinates R P C j) L
      (fun j x => parameterKernel R N P C J j (a j) z x (f j))
      (fun j => parameterOutput R N P C J j (a j) z (f j))
      (fun j r => parameterKernel_integrable R N P C J j (a j) z hz (f j) r)
      (fun j r => (parameterKernel_integral R N P C J j (a j) z hz (f j) r).symm)
    have he : (fun x : KPGlobalTorusFunctionData.Adeles F => L (fun j => parameterKernel R N P C J j (a j) z (rootCoordinate R x j.val) (f j))) =
        (fun x => parameterStageIntegrand R N P C J (fullLevel R P C Q hQ) a t z (PiTensorProduct.tprod ℂ f) (fun j => rootCoordinate R x j.val)) := by
      funext x
      simp only [L, parameterStageIntegrand, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        PiTensorProduct.map_tprod]
      rfl
    rw [he] at hi
    have hs : (fun x => parameterStageIntegrand R N P C J (fullLevel R P C Q hQ) a t z (c • PiTensorProduct.tprod ℂ f) (fun j => rootCoordinate R x j.val)) =
        c • (fun x => parameterStageIntegrand R N P C J (fullLevel R P C Q hQ) a t z (PiTensorProduct.tprod ℂ f) (fun j => rootCoordinate R x j.val)) := by
      ext x
      simp only [parameterStageIntegrand, map_smul, map_add, Submodule.coe_smul,
        Submodule.coe_add, Pi.smul_apply, Pi.add_apply]
    rw [hs]
    refine ⟨hi.1.smul c, ?_⟩
    refine (integral_smul c _).trans ((congrArg (fun x : ℂ => c • x) hi.2).trans ?_)
    simp only [parameterStage, map_smul, LinearMap.comp_apply, PiTensorProduct.map_tprod,
      Submodule.coe_smul, Pi.smul_apply]
    rfl
  | add y v hy hv =>
    have he : (fun x => parameterStageIntegrand R N P C J (fullLevel R P C Q hQ) a t z (y + v) (fun j => rootCoordinate R x j.val)) =
        (fun x => parameterStageIntegrand R N P C J (fullLevel R P C Q hQ) a t z y (fun j => rootCoordinate R x j.val)) + (fun x => parameterStageIntegrand R N P C J (fullLevel R P C Q hQ) a t z v (fun j => rootCoordinate R x j.val)) := by
      ext x
      simp only [parameterStageIntegrand, map_smul, map_add, Submodule.coe_smul,
        Submodule.coe_add, Pi.smul_apply, Pi.add_apply]
    rw [he]
    refine ⟨hy.1.add hv.1, ?_⟩
    refine (integral_add hy.1 hv.1).trans ((congrArg₂ (fun x y : ℂ => x + y) hy.2 hv.2).trans ?_)
    simp only [map_add, Submodule.coe_add, Pi.add_apply]

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end

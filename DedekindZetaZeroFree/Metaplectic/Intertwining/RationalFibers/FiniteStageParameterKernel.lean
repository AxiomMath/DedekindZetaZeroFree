module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RationalFibers.AnalyticParameterKernel

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct Topology
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages KPLocalPrincipalSeries
open _root_.DedekindZetaZeroFree.KPGlobalResidualKernel.IntertwinerRegularization.FactorizationSources.NormalizedCoordinateAnalyticity.ActualOutputAnalytic renaming multilinear_coordinate_analytic → multilinear_coordinate_analytic
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

def parameterStage (J : ∀ q, IwasawaData (C.canonical q).borel)
    (s : RestrictedTensorSimple.Level (bad R P C)) (a : Raw R) (z : ℂ) :
    RestrictedTensorSimple.Stage (Plus R N P C) s.val →ₗ[ℂ]
      KPGlobalResidualConstruction.smoothRationalFiber F R.A.zeta12 R.A.primitive_zeta12 :=
  (comparisonSmooth R P C).comp
    ((RestrictedTensorSimple.stageInclusion (Fiber R P C) (reference R P C) (bad R P C) s).comp
      (PiTensorProduct.map (fun j : s.val => parameterOutput R N P C J j (a j) z)))

def parameterStageIntegrand (J : ∀ q, IwasawaData (C.canonical q).borel)
    (s : RestrictedTensorSimple.Level (bad R P C)) (a : Raw R)
    (t : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12) (z : ℂ)
    (y : RestrictedTensorSimple.Stage (Plus R N P C) s.val)
    (x : ∀ j : s.val, RootPoint R j) : ℂ :=
  (comparisonSmooth R P C ((RestrictedTensorSimple.stageInclusion (Fiber R P C) (reference R P C)
    (bad R P C) s) (PiTensorProduct.map (fun j : s.val => parameterKernel R N P C J j (a j) z (x j)) y))).val.val t

theorem parameterStage_analytic
    (J : ∀ q, IwasawaData (C.canonical q).borel)
    (s : RestrictedTensorSimple.Level (bad R P C)) (a : Raw R)
    (t : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12)
    (y : RestrictedTensorSimple.Stage (Plus R N P C) s.val) :
    AnalyticOnNhd ℂ (fun z => (parameterStage R N P C J s a z y).val.val t)
      KPContinuation.spectralDomain := by
  let ev : KPGlobalResidualConstruction.smoothRationalFiber F R.A.zeta12 R.A.primitive_zeta12 →ₗ[ℂ] ℂ :=
    { toFun f := f.val.val t
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let L : MultilinearMap ℂ (fun j : s.val => Fiber R P C j) ℂ :=
    ((ev.comp (comparisonSmooth R P C)).comp
      (RestrictedTensorSimple.stageInclusion (Fiber R P C) (reference R P C) (bad R P C) s)).compMultilinearMap
      (PiTensorProduct.tprod ℂ)
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    have ha := multilinear_coordinate_analytic (fun j : s.val => inducingCoordinates R P C j) L
      (fun z j => parameterOutput R N P C J j (a j) z (f j)) KPContinuation.spectralDomain
      (fun j r => parameterOutput_coordinate_analytic R N P C J j (a j) (f j) r)
    intro z hz
    convert analyticAt_const.mul (ha z hz) using 1
    funext u
    simp only [parameterStage, map_smul, LinearMap.comp_apply, PiTensorProduct.map_tprod,
      Submodule.coe_smul, Pi.smul_apply]
    rfl
  | add y z hy hz =>
    have he : (fun u => (parameterStage R N P C J s a u (y+z)).val.val t) =
        (fun u => (parameterStage R N P C J s a u y).val.val t +
          (parameterStage R N P C J s a u z).val.val t) := by
      funext u
      simp only [map_add, Submodule.coe_add, Pi.add_apply]
    rw [he]
    exact hy.add hz

theorem parameterStage_zero
    (J : ∀ q, IwasawaData (C.canonical q).borel)
    (s : RestrictedTensorSimple.Level (bad R P C)) (a : Raw R)
    (y : RestrictedTensorSimple.Stage (Plus R N P C) s.val) :
    parameterStage R N P C J s a 0 y =
      (arithmeticStageScale R s.val : ℂ) •
        reflectedStage R N P C s a (sourceStageQuotient R (imageData R N P C) s.val y) := by
  have he : PiTensorProduct.map (fun j : s.val => parameterOutput R N P C J j (a j) 0) =
      (PiTensorProduct.map (fun j : s.val => localMinusValue R N P C j (a j))).comp
        (PiTensorProduct.map (fun j : s.val => arithmeticQuotient R N P C j)) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod]
    congr 1
    funext j
    exact parameterOutput_zero R N P C J j (a j) (f j)
  unfold parameterStage
  rw [LinearMap.comp_apply, LinearMap.comp_apply, he, LinearMap.comp_apply, arithmetic_tensor]
  simp only [map_smul]
  rfl

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end

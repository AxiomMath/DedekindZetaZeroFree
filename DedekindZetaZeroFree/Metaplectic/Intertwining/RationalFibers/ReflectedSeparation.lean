module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RationalFibers.ModifiedHaarIntegration

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

theorem arithmetic_tensor (s : Finset (KPHilbert.Place F))
    (y : RestrictedTensorSimple.Stage (Plus R N P C) s) :
    PiTensorProduct.map (fun j : s => arithmeticQuotient R N P C j) y =
      (arithmeticStageScale R s : ℂ) • sourceStageQuotient R (imageData R N P C) s y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    simp only [map_smul, PiTensorProduct.map_tprod, arithmeticQuotient, LinearMap.smul_apply,
      sourceStageQuotient]
    rw [(PiTensorProduct.tprod ℂ).map_smul_univ]
    simp only [arithmeticStageScale, Complex.ofReal_prod]
    exact smul_comm _ _ _
  | add y z hy hz => simp only [map_add, hy, hz, smul_add]

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end

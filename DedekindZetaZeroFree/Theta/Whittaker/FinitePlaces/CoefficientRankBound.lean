module

public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.WhittakerProfileRank

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.FourierContinuation.TensorActions
open MomentSources
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

theorem finite_slice_rank_le_one_of_coefficient_rank (D : TensorActions R N)
    (q : KPFinitePlace F)
    (hJ : Module.rank ℂ (ActualKirillov.coefficient F R.A.zeta12 R.A.primitive_zeta12 q
      (D.finiteData q).inducing (D.finiteData q).inducing.polarization
      (D.finiteData q).haar (D.finiteData q).haar_integer) ≤ 1) :
    Module.rank ℂ (D.toTensorHC.sliceLine (Sum.inr q)) ≤ 1 := by
  exact (Submodule.rank_mono (D.sliceLine_le_intrinsicWhittaker q)).trans
    (ExteriorWhittakerValues.ActualWhittaker.equivariant_rank_le_one_of_coinvariant_rank_le_one
      _ _ _ hJ)

end DedekindZetaZeroFree.FourierContinuation.TensorActions

end

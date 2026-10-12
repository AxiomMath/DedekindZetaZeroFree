module

public import DedekindZetaZeroFree.Theta.Periods.Wild.FourierContinuity
public import DedekindZetaZeroFree.Theta.Periods.Wild.FiniteTameWords

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct Topology
open NumberField Filter
namespace DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
open WildCurrentGlobalMap KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance rawFiniteClosureDecidablePlace : DecidableEq (KPHilbert.Place F) := Classical.decEq _
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem rawGlobal_continuous : Continuous (rawGlobal (R := R)) := by
  exact QuotientGroup.continuous_mk.comp QuotientGroup.continuous_mk

theorem raw_tame_kernel (D : TensorDetected R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (ha : ∀ p, a p ≠ 1 → ∃ q : KPFinitePlace F, p = Sum.inr q ∧
      Sum.inr q ∉ places W ∧ WildCurrentTameExterior.tameSlot (Sum.inr q))
    (z : AmbientTensor F W (fiber D.toTensorActions W))
    (hz : WildCurrentJointPeriod.period D.toTensorActions W s hW x z = 0) :
    fourier R D.sources.dq (globalMap D.toTensorActions W s hW x z) (rawGlobal (R := R) a) = 0 := by
  let f := fun a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 ↦
    fourier R D.sources.dq (globalMap D.toTensorActions W s hW x z) (rawGlobal (R := R) a)
  have hf : Continuous f :=
    (globalMap_fourier_continuous D.toTensorActions W s hW x z).comp rawGlobal_continuous
  have hlim := hf.continuousAt.tendsto.comp
    (WildRestrictedTruncation.tendsto_truncate _ (compact F R.A.zeta12 R.A.primitive_zeta12) a)
  have he : (fun t : Finset (KPHilbert.Place F) ↦ f
      (WildRestrictedTruncation.truncate _ (compact F R.A.zeta12 R.A.primitive_zeta12) a t)) =
      fun _ ↦ 0 := by
    funext t
    have hw := WildRestrictedTruncation.truncate_list _
      (compact F R.A.zeta12 R.A.primitive_zeta12) a t.toList t.nodup_toList
    rw [Finset.toList_toFinset] at hw
    rw [hw]
    change fourier R D.sources.dq (globalMap D.toTensorActions W s hW x z)
      (rawGlobal (R := R) (WildRestrictedTruncation.word _
        (compact F R.A.zeta12 R.A.primitive_zeta12) a t.toList)) = 0
    rw [← rawWord_eq]
    exact rawWord_kernel D W s hW x hx a ha t.toList z hz
  change Tendsto (fun t : Finset (KPHilbert.Place F) ↦ f
    (WildRestrictedTruncation.truncate _ (compact F R.A.zeta12 R.A.primitive_zeta12) a t))
      atTop (𝓝 (f a)) at hlim
  rw [he] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds
end DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly

end

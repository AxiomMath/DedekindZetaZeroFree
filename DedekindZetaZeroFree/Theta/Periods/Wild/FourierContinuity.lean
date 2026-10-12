module

public import DedekindZetaZeroFree.Theta.Periods.Wild.FourierKernelElimination
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactMeromorphicAverages

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance periodContinuityDecidablePlace : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem globalMap_quotient_joint (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (z : AmbientTensor F W (fiber D W)) :
    Continuous (fun p : Group R × KPAdditiveQuotient F ↦ globalMap D W s hW x z
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out p.2) * p.1)) := by
  let : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  apply ((IsOpenQuotientMap.id (X := Group R)).prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk
      (N := AdeleRing.principalSubgroup (𝓞 F) F))).continuous_comp_iff.mp
  have he (g : Group R) (u : KPAdeles F) : globalMap D W s hW x z
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (Quotient.out (QuotientAddGroup.mk u : KPAdditiveQuotient F)) * g) =
      globalMap D W s hW x z
        (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 u * g) := by
    let n : AddChar (KPAdeles F) (Group R) :=
      { toFun := KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        map_zero_eq_one' := (KPGlobalTorusFunctionData.Nhom F R.A.zeta12 R.A.primitive_zeta12).map_one
        map_add_eq_mul' := KPGlobalTorusFunctionData.N_add F R.A.zeta12 R.A.primitive_zeta12 }
    apply KPGlobalGenericity.unipotentFiber_eq F n (globalMap D W s hW x z) ?_ g u
    intro t a
    change globalMap D W s hW x z
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (algebraMap F (KPAdeles F) t) * a) = _
    rw [← KPLiteralExceptionalResidue.rationalLift_unipotent]
    exact (globalMap_regular D W s hW x z).2.1 _ _
  have hc : Continuous (fun p : Group R × KPAdeles F ↦ globalMap D W s hW x z
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 p.2 * p.1)) :=
    (globalMap_regular D W s hW x z).1.comp
      (((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
        F R.A.zeta12 R.A.primitive_zeta12).comp continuous_snd).mul continuous_fst)
  simpa only [Function.comp_def, Prod.map, id_eq, he] using hc

theorem globalMap_fourier_continuous (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (z : AmbientTensor F W (fiber D W)) :
    Continuous (fourier R D.sources.dq (globalMap D W s hW x z)) := by
  let : IsProbabilityMeasure D.sources.dq := ⟨D.sources.probability⟩
  let f : Group R → C(KPAdditiveQuotient F, ℂ) := fun g ↦
    ⟨fun u ↦ globalMap D W s hW x z
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out u) * g) *
        star (adelicTraceQuotientCharacter F u : ℂ),
      ((globalMap_quotient_joint D W s hW x z).comp
        (continuous_const.prodMk continuous_id)).mul trace_weight_continuous⟩
  have hf : Continuous f := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (globalMap_quotient_joint D W s hW x z).mul
      (trace_weight_continuous.comp continuous_snd)
  have hh := (CompactPeriodAnalyticity.UpperPeriodContinuation.averageCLM D.sources.dq).continuous.comp hf
  apply hh.congr
  intro g
  exact CompactPeriodAnalyticity.UpperPeriodContinuation.averageCLM_apply D.sources.dq (f g)
end DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap

end

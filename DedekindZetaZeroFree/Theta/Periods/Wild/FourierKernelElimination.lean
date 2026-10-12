module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.Wild.TrivialFrequencyVanishing
public import DedekindZetaZeroFree.Theta.Whittaker.Uniqueness.FourierDensity
public import DedekindZetaZeroFree.Theta.Whittaker.Borel.InverseTraceFrequencyReduction

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance fourierEliminationDecidablePlace : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem globalMap_image_zero_of_all_borel (D : TensorActions R N)
    (W : Finset (KPFinitePlace F)) (s : RestrictedTensorSimple.Level D.bad)
    (hW : places W ⊆ s.val) (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (E : Submodule ℂ (JacquetTensor F R.A.zeta12 R.A.primitive_zeta12 W
      (character W) (fiber D W) (action D W))) (q : W)
    (z : InducedTensor F R.A.zeta12 R.A.primitive_zeta12 W
      (depth (R := R) W) (character W) (fiber D W) (action D W) E)
    (hzero : ∀ b : KPGlobalTorusFunctionData.borel F R.A.zeta12 R.A.primitive_zeta12,
      fourier R D.sources.dq (globalMap D W s hW x
        (subspaceEmbedding F R.A.zeta12 R.A.primitive_zeta12 W
          (depth (R := R) W) (depth_valid (R := R) W) (character W)
          (fiber D W) (action D W) (localData D W) E z)) b.val = 0) :
    globalMap D W s hW x
      (subspaceEmbedding F R.A.zeta12 R.A.primitive_zeta12 W
        (depth (R := R) W) (depth_valid (R := R) W) (character W)
        (fiber D W) (action D W) (localData D W) E z) = 0 := by
  let u := subspaceEmbedding F R.A.zeta12 R.A.primitive_zeta12 W
    (depth (R := R) W) (depth_valid (R := R) W) (character W)
    (fiber D W) (action D W) (localData D W) E z
  let θ := globalMap D W s hW x u
  have hc : Continuous θ := (globalMap_regular D W s hW x u).1
  have hr := globalMap_rational D W s hW x u
  let := D.sources.quotientHaar
  let : IsProbabilityMeasure D.sources.dq := ⟨D.sources.probability⟩
  have hhaar : D.sources.dq = KPWildKernelUpperBound.quotientHaar F :=
    ((Measure.addHaarMeasure_eq_iff _ D.sources.dq).mpr D.sources.probability).symm
  have hn := (KPWildInverseBorelFrequencyReduction.borel_nontrivial_fourier_zero_iff_inverse_standard_trace_zero
    F R.A.zeta12 R.A.primitive_zeta12 D.sources.dq θ hc hr).mpr (by
      intro b
      change (∫ y, θ (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (Quotient.out y) * b.val) * (adelicTraceQuotientCharacter F y : ℂ)⁻¹ ∂D.sources.dq) = 0
      simp_rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]
      exact hzero b)
  apply KPWildKernelUpperBound.uniqueFourierDensity F R.A.zeta12 R.A.primitive_zeta12 θ hc hr
  · intro b
    exact KPWildKernelSource.rawBorelRootFiber_continuous
      F R.A.zeta12 R.A.primitive_zeta12 θ hc hr b
  · intro b χ hχ
    rw [← hhaar]
    by_cases ht : χ = 1
    · subst χ
      simp only [AddChar.one_apply, Circle.coe_one, mul_one]
      exact constant_image_zero D W s hW x D.sources.dq b E q z
    · exact hn b χ hχ ht

end DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap

end

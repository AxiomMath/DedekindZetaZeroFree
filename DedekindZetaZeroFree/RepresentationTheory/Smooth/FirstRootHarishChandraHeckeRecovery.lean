module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.HarishChandraHeckeDifferentialRecovery
public import DedekindZetaZeroFree.Theta.Whittaker.ResidualTensorRootDifferentiation

@[expose] public section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical TensorProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem first_root_hc_span_recovery (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R)
    (J : FirstRootProjected R N A B)
    (hNative : RootDerivatives.SourceNativeLie R J.base.factorization)
    {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (hdq : Q.dq = J.base.sources.dq)
    (hpin : ∀ v, T.theta v = firstRootDerivatives R J.cutoffs (J.base.realization.theta v))
    (hsource : ∀ v, (Q.flat v).val 0 ≠ 0)
    (hperiod : ∀ v, fourier R Q.dq (T.theta v) 1 ≠ 0)
    (hfrozen : ∀ v, ∃ (s : RestrictedTensorSimple.Level J.base.factorization.bad)
      (x : ∀ p : s.val, actualLocal R J.base.factorization.finiteData p),
      s.val = J.base.factorization.bad ∧
      RootDerivatives.tensorFunction R J.base.factorization s x =
        firstRootDerivatives R J.cutoffs (J.base.realization.theta v) ∧
      (∀ p : s.val, J.base.factorization.ell p (x p) ≠ 0) ∧
      (∀ p : s.val, x p ≠ 0) ∧
      fourier R J.base.sources.dq (RootDerivatives.tensorFunction R J.base.factorization s x) 1 ≠ 0) :
    hcHeckeSpan J.base.realization ≤ hcHeckeSpan T ∧
      (∀ v, T.theta v ≠ 0) ∧ Nontrivial (Functions R) := by
  have hn (v : R.A.UnitQuotient) : T.theta v ≠ 0 := by
    intro hz
    apply hperiod v
    rw [hz]
    simp [MomentSources.fourier]
  refine ⟨?_, hn, inferInstance⟩
  apply RootDerivatives.frozen_hc_recovery_of_differential_stability R J.base.factorization T
    KPGlobalResidualConstruction.NativeComplexHCOperators.operators
  · intro v hv
    exact RootDerivatives.complexHC_algebra_cyclic _
      KPGlobalResidualConstruction.NativeComplexHCAlgebraic.native_operators_simple v hv
  · intro s x w hw i hm
    have hh := hNative s w hw i (PiTensorProduct.tprod ℂ x)
    rw [FourierContinuation.HCGeneration.tensorSlot_tprod] at hh
    change RootDerivatives.tensorFunction R J.base.factorization s
      (Function.update x ⟨Sum.inl w,hw⟩
        (KPGlobalResidualConstruction.NativeComplexHCOperators.operators i
          (x ⟨Sum.inl w,hw⟩))) = _ at hh
    change RootDerivatives.tensorFunction R J.base.factorization s
      (Function.update x ⟨Sum.inl w,hw⟩
        (KPGlobalResidualConstruction.NativeComplexHCOperators.operators i
          (x ⟨Sum.inl w,hw⟩))) ∈ RootDerivatives.wordRecovery R T
    rw [hh]
    have hd := RootDerivatives.wordRecovery_word R T hm
      [(FourierContinuation.HCGeneration.actualLieIndexEquiv (F := F)).symm (w,i)]
    simpa only [KPContActualSphericalRightFieldIdentification.actualRightWord,
      RootDerivatives.tensorFunction, FiniteWhittakerProjectors.tensorFunction] using hd
  · intro v
    obtain ⟨s,x,hs,hx,hell,hne,hfour⟩ := hfrozen v
    exact ⟨s,x,hs,hx.trans (hpin v).symm,hne⟩

end DedekindZetaZeroFree.ThetaExpansion

end

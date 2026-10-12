module

public import DedekindZetaZeroFree.Theta.Whittaker.FirstRootNondegeneracy
public import DedekindZetaZeroFree.Theta.Whittaker.ArchimedeanFirstRootTensors

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical TensorProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem first_root_fixed_stage_tensors_exists (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R)
    (J : FirstRootProjected R N A B)
    (hNative : RootDerivatives.SourceNativeLie R J.base.factorization) :
    Nontrivial (RestrictedTensorSimple.Core (actualLocal R J.base.factorization.finiteData)
      J.base.factorization.references J.base.factorization.bad) ∧
    ∀ v, ∃ (s : RestrictedTensorSimple.Level J.base.factorization.bad)
      (x : ∀ p : s.val, actualLocal R J.base.factorization.finiteData p),
      s.val = J.base.factorization.bad ∧
      RootDerivatives.tensorFunction R J.base.factorization s x =
        firstRootDerivatives R J.cutoffs (J.base.realization.theta v) ∧
      (∀ p : s.val, J.base.factorization.ell p (x p) ≠ 0) ∧
      (∀ p : s.val, x p ≠ 0) ∧
      fourier R J.base.sources.dq (RootDerivatives.tensorFunction R J.base.factorization s x) 1 ≠ 0 := by
  have he : ∀ v, ∃ (s : RestrictedTensorSimple.Level J.base.factorization.bad)
      (x : ∀ p : s.val, actualLocal R J.base.factorization.finiteData p),
      s.val = J.base.factorization.bad ∧
      RootDerivatives.tensorFunction R J.base.factorization s x =
        firstRootDerivatives R J.cutoffs (J.base.realization.theta v) := by
    intro v
    obtain ⟨s,x,hs,hx⟩ := J.base.factorization.selected_frozen_stage v
    have hxθ : RootDerivatives.tensorFunction R J.base.factorization s x =
        J.base.realization.theta v := by
      change J.base.factorization.coreMap _ = _
      rw [← hx]
      exact J.base.factorization.selected_eq v
    refine ⟨s,RootDerivatives.nativeRootTupleList R J.base.factorization s J.cutoffs
      (Finset.univ : Finset (InfinitePlace F)).toList x,hs,?_⟩
    rw [RootDerivatives.native_firstRoots_pure R J.base.factorization hNative,hxθ]
  have hn := first_root_derivatives_nondegenerate R N A B J
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv⟩ := J.base.factorization.detected
    refine ⟨⟨J.base.factorization.selected v, 0, ?_⟩⟩
    intro hz
    apply hv
    rw [← J.base.factorization.selected_eq, hz, map_zero]
    simp [MomentSources.fourier]
  · intro v
    obtain ⟨s, x, hs, hx⟩ := he v
    have hp : fourier R J.base.sources.dq
        (RootDerivatives.tensorFunction R J.base.factorization s x) 1 ≠ 0 := by
      rw [hx]
      exact hn.1 v
    have hprod : (∏ p : s.val, J.base.factorization.ell p (x p)) ≠ 0 := by
      rw [← J.base.factorization.product_exact]
      exact hp
    have hell (p : s.val) : J.base.factorization.ell p (x p) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hprod) p (Finset.mem_univ p)
    refine ⟨s, x, hs, hx, hell, ?_, hp⟩
    intro p hz
    apply hell p
    rw [hz, map_zero]

end DedekindZetaZeroFree.ThetaExpansion

end

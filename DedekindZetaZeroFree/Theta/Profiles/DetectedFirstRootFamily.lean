module

public import DedekindZetaZeroFree.Theta.Whittaker.ResidueModelTransport
public import DedekindZetaZeroFree.Theta.Whittaker.SphericalSeed
public import DedekindZetaZeroFree.Theta.Whittaker.NormalizedFiniteProjector
public import DedekindZetaZeroFree.Eisenstein.Residues.FirstRootFlatLifts

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def FirstRootLift.packet {R : PrincipalMellin.ActualRecipe S η}
    {N : TraceHaarTransport R} {A : FirstRootSphericalSeed R N} {B : FirstRootCutoffs R}
    {J : FirstRootProjected R N A B} (L : FirstRootLift R N A B J) : Packet R L.base.sources where
  seed := L.base.sources.flat
  seed_spherical := L.base.sources.exterior_spherical
  operations := fun v => FlatOperation.seed v
  v₀ := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
  cutoff := J.cutoffs.cutoff
  cutoff_open := J.cutoffs.open_cutoff
  cutoff_compact := J.cutoffs.compact_cutoff
  cutoff_sixth := J.cutoffs.sixth
  exponents := fun _ => J.cutoffs.exponent
  first_root := fun _ => J.cutoffs.sign
  branch := firstRootBranch R
  branch_global := firstRootBranch_apply R
  branch_exact := J.cutoffs.branch_exact
  cutoff_kernel := J.cutoffs.kernel

theorem FirstRootLift.profile {R : PrincipalMellin.ActualRecipe S η}
    {N : TraceHaarTransport R} {A : FirstRootSphericalSeed R N} {B : FirstRootCutoffs R}
    {J : FirstRootProjected R N A B} (L : FirstRootLift R N A B J) (v : R.A.UnitQuotient) (y : R.A.G) :
    firstRootMultiplier R J.cutoffs y * firstRootRadialProfile R J.cutoffs y =
      L.packet.forwardProfile v y := by
  unfold firstRootMultiplier firstRootRadialProfile firstRootSphericalProduct Packet.forwardProfile
  change (∏ w : InfinitePlace F, _) * ((if ∀ p : R.A.Sf, y.2 p ∈ J.cutoffs.cutoff p then 1 else 0) *
    ∏ w : InfinitePlace F, _) =
    (if ∀ p : R.A.Sf, y.2 p ∈ J.cutoffs.cutoff p then 1 else 0) * ∏ w : InfinitePlace F, _
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  dsimp only [Packet.scale, FirstRootLift.packet]
  push_cast
  ring

def FirstRootLift.toJointForwardIdentitySources {R : PrincipalMellin.ActualRecipe S η}
    {N : TraceHaarTransport R} {A : FirstRootSphericalSeed R N} {B : FirstRootCutoffs R}
    {J : FirstRootProjected R N A B} (L : FirstRootLift R N A B J)
    (_hi : ∀ v g, Integrable (fun q => firstRootDerivatives R J.cutoffs (J.base.realization.theta v)
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) J.base.sources.dq)
    (hd : ∀ v y, fourier R J.base.sources.dq
      (firstRootDerivatives R J.cutoffs (J.base.realization.theta v)) (diagonal R y) =
        firstRootMultiplier R J.cutoffs y *
          fourier R J.base.sources.dq (J.base.realization.theta v) (diagonal R y)) : JointForwardIdentitySources R N :=
  { L.base with
    packet := L.packet
    forward := by
      intro v y
      unfold MomentSources.fourier
      rw [L.dq_exact, L.residue_exact]
      change fourier R J.base.sources.dq
        (firstRootDerivatives R J.cutoffs (J.base.realization.theta v)) (diagonal R y) = _
      rw [hd v y, J.radial v y]
      exact L.profile v y }

theorem first_root_packet
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R) (N : TraceHaarTransport R)
    (prior : Nonempty (JointExteriorCoefficientSources R N)) : Nonempty (JointForwardIdentitySources R N) := by
  obtain ⟨A, hNative, ⟨D⟩⟩ := FourierContinuation.LiteralSource.current_native_transport_exists R hR N
  obtain ⟨B⟩ := first_root_cutoffs_exist R
  obtain ⟨Anew, hAnew⟩ := spherical_seed_exists_of_transport R N A D hNative
  obtain ⟨J, hJ⟩ := RootDerivatives.finite_projector_native R hR N Anew B hAnew
  obtain ⟨L⟩ := first_root_flat_lift_exists R hR N Anew B J hJ
  obtain ⟨hi, hd⟩ := first_root_derivative_period R N Anew B J
  exact ⟨L.toJointForwardIdentitySources hi hd⟩

end DedekindZetaZeroFree.ThetaExpansion

end

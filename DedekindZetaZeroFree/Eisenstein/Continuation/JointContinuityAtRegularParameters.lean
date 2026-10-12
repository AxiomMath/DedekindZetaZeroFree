module

public import DedekindZetaZeroFree.Eisenstein.Continuation.RegularLocusJointContinuity
public import DedekindZetaZeroFree.Eisenstein.Continuation.JointContinuityFromNumerators

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms
open scoped Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem selected_scalar_branch_joint_continuous_on
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R} (B : JointRootAlignedSources R N)
    (v : R.A.UnitQuotient) (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D) :
    ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ) := by
  exact ResidueContinuity.ScalarSourceJointContinuity.selected_regular_joint R B v D P

theorem selected_regular_continuous
    {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R} {B : JointRootAlignedSources R N}
    {v : R.A.UnitQuotient} {D : SelectedScalarBranch R B v} {P : SelectedPoleSet D}
    (h : ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ))
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (hp : s ∉ P.poles) :
    Continuous (D.E s) := by
  apply continuousOn_univ.mp
  exact h.comp (continuousOn_const.prodMk continuousOn_id)
    (fun g _ => ⟨⟨hs, hp⟩, Set.mem_univ g⟩)

end DedekindZetaZeroFree.ThetaExpansion

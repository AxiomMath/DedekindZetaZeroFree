module

public import DedekindZetaZeroFree.Eisenstein.Continuation.FlatSectionResolvent
public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarAndSmoothGerms
public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberAbsoluteConvergence

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms
open scoped Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

structure SelectedScalarBranch (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (B : JointRootAlignedSources R N) (v : R.A.UnitQuotient) where
  E : ℂ → Functions R
  normal : ∀ g, MeromorphicNFOn (fun s => E s g) KPContinuation.spectralDomain
  chamber : ∀ s, (1 / 3 : ℝ) < s.re → ∀ g,
    E s g = KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
      B.sources.K (B.sources.flat v) s g

theorem selected_scalar_branch_exists
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R} (B : JointRootAlignedSources R N)
    (v : R.A.UnitQuotient) : Nonempty (SelectedScalarBranch R B v) := by
  obtain ⟨E, hnormal, hchamber⟩ :=
    EisensteinSmoothGerms.ScalarSource.selected_scalar_continuation R B v
  exact ⟨⟨E, hnormal, hchamber⟩⟩

end DedekindZetaZeroFree.ThetaExpansion

end

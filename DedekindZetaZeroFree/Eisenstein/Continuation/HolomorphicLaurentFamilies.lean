module

public import DedekindZetaZeroFree.Eisenstein.Induction.OrdinaryAndGenuineFlatSections
public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothLaurentCoefficients
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactSmoothRealization

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem common_smooth_laurent_germ_exists
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (prior : Nonempty (JointRootAlignedSources R N)) :
    Nonempty (JointRealizedFlatSources R N) := by
  classical
  obtain ⟨B⟩ := prior
  obtain ⟨C, ⟨H⟩⟩ := selected_scalar_source_exists R B
  have hg : ∀ v : R.A.UnitQuotient, ∃ G : EisensteinSmoothGerms.IndividualSmoothGerm C v,
      G.radius ≤ (H v).radius ∧ ∀ s, s ∈ Metric.ball (0 : ℂ) G.radius →
        G.cleared s = ((H v).cleared s : Functions R) :=
    fun v => selected_source_smooth_germ_of_scalar_germ R B C v (H v)
  choose G hG using hg
  exact ⟨{ toJointRootAlignedSources := B, realization := EisensteinSmoothGerms.assemble C G }⟩
end DedekindZetaZeroFree.ThetaExpansion

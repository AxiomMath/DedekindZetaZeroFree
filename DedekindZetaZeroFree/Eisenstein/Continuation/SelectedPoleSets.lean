module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarChamberSeries

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms
open scoped Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

structure SelectedPoleSet {R : PrincipalMellin.ActualRecipe S η}
    {N : TraceHaarTransport R} {B : JointRootAlignedSources R N} {v : R.A.UnitQuotient} (D : SelectedScalarBranch R B v) where
  poles : Set ℂ
  subset : poles ⊆ KPContinuation.spectralDomain
  isolated : ∀ z ∈ KPContinuation.spectralDomain, ∃ r : ℝ, 0 < r ∧
    Metric.ball z r ⊆ KPContinuation.spectralDomain ∧
    ∀ s ∈ Metric.ball z r, s ∈ poles → s = z
  chamber_disjoint : ∀ s, (1 / 3 : ℝ) < s.re → s ∉ poles
  regular : ∀ s ∈ KPContinuation.spectralDomain, s ∉ poles →
    ∀ g, AnalyticAt ℂ (fun z => D.E z g) s

end DedekindZetaZeroFree.ThetaExpansion

end

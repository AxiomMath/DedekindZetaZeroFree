module

public import DedekindZetaZeroFree.Eisenstein.Continuation.JointContinuityAtRegularParameters
public import DedekindZetaZeroFree.Eisenstein.Residues.ScalarPoleOrder

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms Filter
open scoped Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def selectedScalarNumerator
    {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R} {B : JointRootAlignedSources R N}
    {v : R.A.UnitQuotient} (D : SelectedScalarBranch R B v) (r : ℝ) : ℂ → Functions R :=
  fun s g => toMeromorphicNFOn (fun z => z * D.E z g) (Metric.ball (0 : ℂ) r) s

theorem selectedScalarNumerator_analytic
    {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R} {B : JointRootAlignedSources R N}
    {v : R.A.UnitQuotient} (D : SelectedScalarBranch R B v) (r : ℝ)
    (hb : Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain)
    (hregular : ∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 →
      ∀ g, AnalyticAt ℂ (fun z => D.E z g) s)
    (horder : ∀ g, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun s => D.E s g) 0) :
    ∀ g, AnalyticOnNhd ℂ (fun s => selectedScalarNumerator D r s g)
      (Metric.ball (0 : ℂ) r) := by
  intro g s hs
  have hm : MeromorphicOn (fun z => z * D.E z g) (Metric.ball (0 : ℂ) r) := by
    intro z hz
    exact analyticAt_id.meromorphicAt.mul ((D.normal g (hb hz)).meromorphicAt)
  apply (meromorphicNFOn_toMeromorphicNFOn (fun z => z * D.E z g) _ hs).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hm hs]
  by_cases hs0 : s = 0
  · subst s
    change 0 ≤ meromorphicOrderAt (id * (fun z => D.E z g)) 0
    rw [meromorphicOrderAt_mul analyticAt_id.meromorphicAt
      (D.normal g (hb hs)).meromorphicAt, meromorphicOrderAt_id]
    have h := add_le_add_left (horder g) (1 : WithTop ℤ)
    norm_num at h ⊢
    simpa only [add_comm] using h
  · exact (analyticAt_id.mul (hregular s hs hs0 g)).meromorphicOrderAt_nonneg

theorem selectedScalarNumerator_clears
    {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R} {B : JointRootAlignedSources R N}
    {v : R.A.UnitQuotient} (D : SelectedScalarBranch R B v) (r : ℝ)
    (hb : Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain)
    (hregular : ∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 →
      ∀ g, AnalyticAt ℂ (fun z => D.E z g) s)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) r) (hs0 : s ≠ 0) :
    selectedScalarNumerator D r s = s • D.E s := by
  funext g
  have hm : MeromorphicOn (fun z => z * D.E z g) (Metric.ball (0 : ℂ) r) := by
    intro z hz
    exact analyticAt_id.meromorphicAt.mul ((D.normal g (hb hz)).meromorphicAt)
  unfold selectedScalarNumerator
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm hs]
  exact congrFun (toMeromorphicNFAt_eq_self.mpr
    (analyticAt_id.mul (hregular s hs hs0 g)).meromorphicNFAt) s

end DedekindZetaZeroFree.ThetaExpansion

end

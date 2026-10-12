module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarBranchUniquenessAndSingularSets

@[expose] public section

noncomputable section
open scoped Topology
open Filter
namespace DedekindZetaZeroFree.KPScalarContinuation
open MomentSources ThetaExpansion ResidueContinuity.ScalarSourcePoleGeometry

variable {X : Type*}

theorem meromorphicOn_of_local_clearing (A : ℂ → X → ℂ) (O : Set ℂ)
    (hlocal : ∀ z ∈ O, ∃ (r : ℝ) (m : ℕ) (w : ℂ → X → ℂ),
      0 < r ∧ Metric.ball z r ⊆ O ∧
      (∀ g, AnalyticOnNhd ℂ (fun s => w s g) (Metric.ball z r)) ∧
      ∀ s ∈ Metric.ball z r, s ≠ z → ∀ g, w s g = (s-z)^m * A s g) :
    ∀ g, MeromorphicOn (fun s => A s g) O := by
  intro g z hz
  obtain ⟨r, m, w, hr, _, ha, hc⟩ := hlocal z hz
  apply MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr
  refine ⟨-(m : ℤ), fun s => w s g, ha g z (Metric.mem_ball_self hr), ?_⟩
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z hr), self_mem_nhdsWithin]
    with s hs hsz
  have hne : s ≠ z := by simpa using hsz
  rw [hc s hs hne g, zpow_neg, zpow_natCast, smul_eq_mul,
    inv_mul_cancel_left₀ (pow_ne_zero m (sub_ne_zero.mpr hne))]

theorem scalar_singularities_isolated_of_local_clearing
    (A : ℂ → X → ℂ) (O : Set ℂ)
    (hlocal : ∀ z ∈ O, ∃ (r : ℝ) (m : ℕ) (w : ℂ → X → ℂ),
      0 < r ∧ Metric.ball z r ⊆ O ∧
      (∀ g, AnalyticOnNhd ℂ (fun s => w s g) (Metric.ball z r)) ∧
      ∀ s ∈ Metric.ball z r, s ≠ z → ∀ g, w s g = (s-z)^m * A s g) :
    IsolatedPoles O {s | s ∈ O ∧ ∃ g, ¬ AnalyticAt ℂ (fun z => A z g) s} := by
  intro z hz
  obtain ⟨r, m, w, hr, hb, ha, hc⟩ := hlocal z hz
  refine ⟨r, hr, hb, ?_⟩
  intro t ht hp
  by_contra htz
  obtain ⟨g, hg⟩ := hp.2
  have hn : (t-z)^m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr htz)
  have hq : AnalyticAt ℂ (fun s => w s g / (s-z)^m) t :=
    (ha g t ht).div ((analyticAt_id.sub analyticAt_const).pow m) hn
  have he : (fun s => A s g) =ᶠ[𝓝 t] (fun s => w s g / (s-z)^m) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds ht, isOpen_ne.mem_nhds htz]
      with s hs hsz
    rw [hc s hs hsz g, mul_div_cancel_left₀ _
      (pow_ne_zero m (sub_ne_zero.mpr hsz))]
  exact hg (hq.congr he.symm)

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
variable {B : JointRootAlignedSources R N} {v : R.A.UnitQuotient}

end DedekindZetaZeroFree.KPScalarContinuation

end

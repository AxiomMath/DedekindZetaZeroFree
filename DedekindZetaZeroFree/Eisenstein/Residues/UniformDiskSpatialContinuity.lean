module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarLaurentNumerator

@[expose] public section

noncomputable section
open scoped Topology
namespace DedekindZetaZeroFree.ResidueContinuity
open MomentSources ThetaExpansion
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem selected_numerator_circle_continuous
    {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R} {B : JointRootAlignedSources R N}
    {v : R.A.UnitQuotient} (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (hjoint : ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ))
    (r t : ℝ) (ht : 0 < t) (htr : t < r)
    (hb : Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain)
    (hp : ∀ s ∈ Metric.ball (0 : ℂ) r, s ∈ P.poles → s = 0) :
    Continuous (fun p : Metric.sphere (0 : ℂ) t × Group R =>
      selectedScalarNumerator D r p.1 p.2) := by
  have hball (z : Metric.sphere (0 : ℂ) t) : (z : ℂ) ∈ Metric.ball 0 r :=
    Metric.closedBall_subset_ball htr (Metric.sphere_subset_closedBall z.property)
  have hne (z : Metric.sphere (0 : ℂ) t) : (z : ℂ) ≠ 0 := by
    intro hz
    have he := z.property
    rw [hz] at he
    exact ht.ne' (by simpa using he.symm)
  have hnot (z : Metric.sphere (0 : ℂ) t) : (z : ℂ) ∉ P.poles :=
    fun hz => hne z (hp z (hball z) hz)
  have hreg : ∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 →
      ∀ g, AnalyticAt ℂ (fun z => D.E z g) s := by
    intro s hs hs0
    exact P.regular s (hb hs) (fun h => hs0 (hp s hs h))
  have hE : Continuous (fun p : Metric.sphere (0 : ℂ) t × Group R =>
      D.E p.1 p.2) := by
    apply continuousOn_univ.mp
    exact hjoint.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      continuous_snd).continuousOn (fun p _ =>
        ⟨⟨hb (hball p.1), hnot p.1⟩, Set.mem_univ p.2⟩)
  apply ((continuous_subtype_val.comp continuous_fst).mul hE).congr
  intro p
  exact (congrFun (selectedScalarNumerator_clears D r hb hreg p.1
    (hball p.1) (hne p.1)) p.2).symm

theorem selected_residue_continuous
    {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R} {B : JointRootAlignedSources R N}
    {v : R.A.UnitQuotient} (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (hjoint : ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ))
    (horder : ∀ g, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun s => D.E s g) 0)
    (r : ℝ) (hr : 0 < r)
    (hb : Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain)
    (hp : ∀ s ∈ Metric.ball (0 : ℂ) r, s ∈ P.poles → s = 0) :
    Continuous (selectedScalarNumerator D r 0) := by
  have ht : 0 < r / 2 := by positivity
  have htr : r / 2 < r := by linarith
  have hreg : ∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 →
      ∀ g, AnalyticAt ℂ (fun z => D.E z g) s := by
    intro s hs hs0
    exact P.regular s (hb hs) (fun h => hs0 (hp s hs h))
  exact continuous_center_of_continuous_circle (selectedScalarNumerator D r) r
    (r / 2) ht htr (selectedScalarNumerator_analytic D r hb hreg horder)
    (selected_numerator_circle_continuous D P hjoint r (r / 2) ht htr hb hp)

end DedekindZetaZeroFree.ResidueContinuity

end

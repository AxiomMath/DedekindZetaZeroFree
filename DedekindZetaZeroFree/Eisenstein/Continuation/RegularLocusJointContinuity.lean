module

public import DedekindZetaZeroFree.Eisenstein.Continuation.FixedLevelPoleSets
public import DedekindZetaZeroFree.Analysis.Complex.JointContinuityFromCircle

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SelectedPoleSet
open MomentSources EisensteinSmoothGerms
open scoped Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
variable {B : JointRootAlignedSources R N} {v : R.A.UnitQuotient}

theorem exists_ball_subset_regularLocus
    (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain \ P.poles) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball s r ⊆ KPContinuation.spectralDomain \ P.poles := by
  obtain ⟨r, hr, hdom, hiso⟩ := P.isolated s hs.1
  refine ⟨r, hr, fun z hz => ⟨hdom hz, ?_⟩⟩
  intro hp
  exact hs.2 ((hiso z hz hp) ▸ hp)

theorem isOpen_regularLocus (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D) :
    IsOpen (KPContinuation.spectralDomain \ P.poles) := by
  rw [Metric.isOpen_iff]
  intro s hs
  exact exists_ball_subset_regularLocus D P s hs

private theorem continuousOn_iff_continuousAt
    (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D) :
    ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ) ↔
    ∀ s ∈ KPContinuation.spectralDomain \ P.poles, ∀ g : Group R,
      ContinuousAt (fun p : ℂ × Group R => D.E p.1 p.2) (s, g) := by
  constructor
  · intro h s hs g
    exact h.continuousAt (((isOpen_regularLocus D P).prod isOpen_univ).mem_nhds
      ⟨hs, Set.mem_univ g⟩)
  · intro h p hp
    exact (h p.1 hp.1 p.2).continuousWithinAt

private theorem continuousAt_of_continuous_sphere
    (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (s : ℂ) (t : ℝ) (ht : 0 < t)
    (hclosed : Metric.closedBall s t ⊆ KPContinuation.spectralDomain \ P.poles)
    (hc : Continuous (fun p : Metric.sphere s t × Group R => D.E p.1 p.2))
    (g : Group R) : ContinuousAt (fun p : ℂ × Group R => D.E p.1 p.2) (s, g) := by
  have hf : ∀ x, DifferentiableOn ℂ (fun z => D.E z x) (Metric.closedBall s t) := by
    intro x z hz
    exact (P.regular z (hclosed hz).1 (hclosed hz).2 x).differentiableAt.differentiableWithinAt
  have hj := ComplexAnalysis.continuousOn_ball_of_continuous_sphere
    (fun z g => D.E z g) s t ht hf hc
  exact hj.continuousAt ((Metric.isOpen_ball.prod isOpen_univ).mem_nhds
    ⟨Metric.mem_ball_self ht, Set.mem_univ g⟩)

private theorem continuousAt_of_continuousOn_punctured_ball
    (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (s : ℂ) (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball s r ⊆ KPContinuation.spectralDomain \ P.poles)
    (hj : ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((Metric.ball s r \ {s}) ×ˢ Set.univ))
    (g : Group R) : ContinuousAt (fun p : ℂ × Group R => D.E p.1 p.2) (s, g) := by
  have ht : 0 < r / 2 := by positivity
  have htr : r / 2 < r := by linarith
  have hc : Continuous (fun p : Metric.sphere s (r / 2) × Group R => D.E p.1 p.2) := by
    apply hj.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    intro p
    refine ⟨⟨Metric.closedBall_subset_ball htr
      (Metric.sphere_subset_closedBall p.1.property), ?_⟩, Set.mem_univ p.2⟩
    intro he
    have heq : (p.1 : ℂ) = s := Set.mem_singleton_iff.mp he
    have hs := p.1.property
    rw [heq] at hs
    exact ht.ne' (by simpa using hs.symm)
  exact continuousAt_of_continuous_sphere D P s (r / 2) ht
    ((Metric.closedBall_subset_ball htr).trans hball) hc g

theorem continuousOn_of_locally_continuousOn_punctured_ball
    (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (hlocal : ∀ s ∈ KPContinuation.spectralDomain \ P.poles,
      ∃ r : ℝ, 0 < r ∧ Metric.ball s r ⊆ KPContinuation.spectralDomain \ P.poles ∧
        ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
          ((Metric.ball s r \ {s}) ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ) := by
  apply (continuousOn_iff_continuousAt D P).mpr
  intro s hs g
  obtain ⟨r, hr, hb, hj⟩ := hlocal s hs
  exact continuousAt_of_continuousOn_punctured_ball D P s r hr hb hj g

end DedekindZetaZeroFree.ThetaExpansion.SelectedPoleSet

end

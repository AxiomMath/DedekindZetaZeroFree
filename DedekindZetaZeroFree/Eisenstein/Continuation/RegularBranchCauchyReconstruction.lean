module

public import DedekindZetaZeroFree.Eisenstein.Continuation.RegularBranchCovariance
public import DedekindZetaZeroFree.Analysis.Complex.CauchyJointContinuity

@[expose] public section

noncomputable section
open scoped Topology
namespace DedekindZetaZeroFree.ResidueContinuity.ScalarSourceJointContinuity
open MomentSources ThetaExpansion
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
variable {B : JointRootAlignedSources R N} {v : R.A.UnitQuotient}

theorem selected_regular_joint_at_of_circle
    (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (s : ℂ) (t : ℝ) (ht : 0 < t)
    (hclosed : Metric.closedBall s t ⊆ KPContinuation.spectralDomain \ P.poles)
    (hc : Continuous (fun p : Metric.sphere s t × Group R => D.E p.1 p.2))
    (g : Group R) : ContinuousAt (fun p : ℂ × Group R => D.E p.1 p.2) (s, g) := by
  have hf : ∀ x, DifferentiableOn ℂ (fun z => D.E z x) (Metric.closedBall s t) := by
    intro x z hz
    exact (P.regular z (hclosed hz).1 (hclosed hz).2 x).differentiableAt.differentiableWithinAt
  have hj := joint_continuousOn_ball_of_continuous_circle (fun z g => D.E z g) s t ht hf hc
  exact hj.continuousAt ((Metric.isOpen_ball.prod isOpen_univ).mem_nhds
    ⟨Metric.mem_ball_self ht, Set.mem_univ g⟩)

theorem selected_regular_joint_at_of_punctured
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
  exact selected_regular_joint_at_of_circle D P s (r / 2) ht
    ((Metric.closedBall_subset_ball htr).trans hball) hc g

theorem selected_regular_joint_of_punctured
    (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (hlocal : ∀ s ∈ KPContinuation.spectralDomain \ P.poles,
      ∃ r : ℝ, 0 < r ∧ Metric.ball s r ⊆ KPContinuation.spectralDomain \ P.poles ∧
        ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
          ((Metric.ball s r \ {s}) ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ) := by
  apply (regular_joint_iff D P).mpr
  intro s hs g
  obtain ⟨r, hr, hb, hj⟩ := hlocal s hs
  exact selected_regular_joint_at_of_punctured D P s r hr hb hj g

end DedekindZetaZeroFree.ResidueContinuity.ScalarSourceJointContinuity

end

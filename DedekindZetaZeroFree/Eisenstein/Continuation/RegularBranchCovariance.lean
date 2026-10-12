module

public import DedekindZetaZeroFree.Eisenstein.Continuation.FixedLevelPoleSets

@[expose] public section

noncomputable section
open scoped Topology
open Filter
namespace DedekindZetaZeroFree.ResidueContinuity
open MomentSources ThetaExpansion
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R} {B : JointRootAlignedSources R N}
variable {v : R.A.UnitQuotient}

theorem regular_ball (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain \ P.poles) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball s r ⊆ KPContinuation.spectralDomain \ P.poles := by
  obtain ⟨r, hr, hdom, hiso⟩ := P.isolated s hs.1
  refine ⟨r, hr, fun z hz => ⟨hdom hz, ?_⟩⟩
  intro hp
  exact hs.2 ((hiso z hz hp) ▸ hp)

theorem regular_isOpen (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D) :
    IsOpen (KPContinuation.spectralDomain \ P.poles) := by
  rw [Metric.isOpen_iff]
  intro s hs
  exact regular_ball D P s hs

theorem regular_joint_iff (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D) :
    ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ) ↔
    ∀ s ∈ KPContinuation.spectralDomain \ P.poles, ∀ g : Group R,
      ContinuousAt (fun p : ℂ × Group R => D.E p.1 p.2) (s, g) := by
  constructor
  · intro h s hs g
    exact h.continuousAt (((regular_isOpen D P).prod isOpen_univ).mem_nhds
      ⟨hs, Set.mem_univ g⟩)
  · intro h p hp
    exact (h p.1 hp.1 p.2).continuousWithinAt

end DedekindZetaZeroFree.ResidueContinuity

end

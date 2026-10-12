module

public import DedekindZetaZeroFree.Eisenstein.Residues.GroupVariableContinuity

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms Filter
open scoped Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def selectedContinuousBranch
    {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R} {B : JointRootAlignedSources R N}
    {v : R.A.UnitQuotient} (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (hj : ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ))
    (s : ℂ) : C(Group R, ℂ) := by
  classical
  exact if h : s ∈ KPContinuation.spectralDomain ∧ s ∉ P.poles then
    ⟨D.E s, selected_regular_continuous hj s h.1 h.2⟩ else 0

theorem selectedContinuousBranch_regular
    {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R} {B : JointRootAlignedSources R N}
    {v : R.A.UnitQuotient} (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (hj : ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ))
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (hp : s ∉ P.poles) :
    (selectedContinuousBranch D P hj s : Functions R) = D.E s := by
  simp [selectedContinuousBranch, hs, hp]

theorem selectedContinuousBranch_meromorphic
    {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R} {B : JointRootAlignedSources R N}
    {v : R.A.UnitQuotient} (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (hj : ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ)) (g : Group R) :
    MeromorphicOn (fun s => selectedContinuousBranch D P hj s g)
      KPContinuation.spectralDomain := by
  intro z hz
  obtain ⟨r, hr, hb, hp⟩ := P.isolated z hz
  apply (D.normal g hz).meromorphicAt.congr
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z hr),
    self_mem_nhdsWithin] with s hs hn
  have hsne : s ≠ z := by simpa using hn
  have hsp : s ∉ P.poles := fun h => hsne (hp s hs h)
  exact (congrFun (selectedContinuousBranch_regular D P hj s (hb hs) hsp) g).symm

def selectedContinuousNumerator
    {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R} {B : JointRootAlignedSources R N}
    {v : R.A.UnitQuotient} (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (hj : ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ))
    (r : ℝ) (hb : Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain)
    (hp : ∀ s ∈ Metric.ball (0 : ℂ) r, s ∈ P.poles → s = 0)
    (hres : Continuous (selectedScalarNumerator D r 0))
    (s : ℂ) : C(Group R, ℂ) := by
  classical
  refine if hs : s ∈ Metric.ball (0 : ℂ) r then ⟨selectedScalarNumerator D r s, ?_⟩ else 0
  by_cases h0 : s = 0
  · subst s; exact hres
  · have hn : s ∉ P.poles := fun h => h0 (hp s hs h)
    have hreg : ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 →
        ∀ g, AnalyticAt ℂ (fun t => D.E t g) z := by
      intro z hz hz0
      exact P.regular z (hb hz) (fun h => hz0 (hp z hz h))
    rw [selectedScalarNumerator_clears D r hb hreg s hs h0]
    exact continuous_const.smul (selected_regular_continuous hj s (hb hs) hn)

theorem selectedContinuousNumerator_eq
    {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R} {B : JointRootAlignedSources R N}
    {v : R.A.UnitQuotient} (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (hj : ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ))
    (r : ℝ) (hb : Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain)
    (hp : ∀ s ∈ Metric.ball (0 : ℂ) r, s ∈ P.poles → s = 0)
    (hres : Continuous (selectedScalarNumerator D r 0))
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) r) :
    (selectedContinuousNumerator D P hj r hb hp hres s : Functions R) =
      selectedScalarNumerator D r s := by
  simp [selectedContinuousNumerator, hs]

theorem selectedScalarSource_assemble
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R} (B : JointRootAlignedSources R N)
    (D : ∀ v, SelectedScalarBranch R B v) (P : ∀ v, SelectedPoleSet (D v))
    (hj : ∀ v, ContinuousOn (fun p : ℂ × Group R => (D v).E p.1 p.2)
      ((KPContinuation.spectralDomain \ (P v).poles) ×ˢ Set.univ))
    (ho : ∀ v g, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun s => (D v).E s g) 0)
    (hres : ∀ v (r : ℝ), 0 < r →
      Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain →
      (∀ s ∈ Metric.ball (0 : ℂ) r, s ∈ (P v).poles → s = 0) →
      Continuous (selectedScalarNumerator (D v) r 0)) :
    ∃ C : ScalarContinuation R B.sources,
      Nonempty (∀ v : R.A.UnitQuotient, ScalarGerm C v) := by
  classical
  let C : ScalarContinuation R B.sources := {
    E := fun v => selectedContinuousBranch (D v) (P v) (hj v)
    meromorphic := fun v g => selectedContinuousBranch_meromorphic (D v) (P v) (hj v) g
    chamber := by
      intro v s hs g
      have hΩ := KPContinuation.convergenceHalfPlane_subset_spectralDomain hs
      rw [show selectedContinuousBranch (D v) (P v) (hj v) s g = (D v).E s g from
        congrFun (selectedContinuousBranch_regular (D v) (P v) (hj v) s hΩ
          ((P v).chamber_disjoint s hs)) g]
      exact (D v).chamber s hs g }
  refine ⟨C, ?_⟩
  suffices h : ∀ v, Nonempty (ScalarGerm C v) from ⟨fun v => Classical.choice (h v)⟩
  intro v
  obtain ⟨r, hr, hb, hp⟩ := (P v).isolated 0 (by norm_num [KPContinuation.spectralDomain])
  have hreg : ∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 →
      ∀ g, AnalyticAt ℂ (fun z => (D v).E z g) s := by
    intro s hs hs0
    exact (P v).regular s (hb hs) (fun h => hs0 (hp s hs h))
  have hc := hres v r hr hb hp
  refine ⟨{
    radius := r
    radius_pos := hr
    cleared := selectedContinuousNumerator (D v) (P v) (hj v) r hb hp hc
    clears := ?_
    analytic := ?_ }⟩
  · intro s hs hs0
    rw [selectedContinuousNumerator_eq (D v) (P v) (hj v) r hb hp hc s hs,
      selectedScalarNumerator_clears (D v) r hb hreg s hs hs0]
    change s • (D v).E s = s • (selectedContinuousBranch (D v) (P v) (hj v) s : Functions R)
    rw [selectedContinuousBranch_regular (D v) (P v) (hj v) s (hb hs)
      (fun h => hs0 (hp s hs h))]
  · intro g s hs
    apply (selectedScalarNumerator_analytic (D v) r hb hreg (ho v) g s hs).congr
    filter_upwards [Metric.isOpen_ball.mem_nhds hs] with z hz
    exact (congrFun (selectedContinuousNumerator_eq (D v) (P v) (hj v) r hb hp hc z hz) g).symm

theorem selected_scalar_source_exists
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R} (B : JointRootAlignedSources R N) :
    ∃ C : ScalarContinuation R B.sources,
      Nonempty (∀ v : R.A.UnitQuotient, ScalarGerm C v) := by
  classical
  have hex (v : R.A.UnitQuotient) := selected_scalar_branch_exists R B v
  let D := fun v => Classical.choice (hex v)
  let P := fun v => Classical.choice (selected_scalar_pole_set_exists R B v (D v))
  have hj := fun v => selected_scalar_branch_joint_continuous_on R B v (D v) (P v)
  have ho := fun v => selected_scalar_order_at_zero_ge_neg_one R B v (D v)
  exact selectedScalarSource_assemble R B D P hj ho
    (fun v => selected_scalar_numerator_zero_continuous R B v (D v) (P v) (hj v) (ho v))
end DedekindZetaZeroFree.ThetaExpansion

end

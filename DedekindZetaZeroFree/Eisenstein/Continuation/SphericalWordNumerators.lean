module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothGerms.JointNumeratorEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open Filter
namespace DedekindZetaZeroFree.ResidueContinuity.ScalarSourceJointContinuity
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_line_construction → scalar_line_construction
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_analytic_of_right_holomorphic → scalar_analytic_of_right_holomorphic
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming word_smul → word_smul
open _root_.DedekindZetaZeroFree.KPContinuation.NativeWordCompactHolomorphy renaming actualRightWord_compact_holomorphy → actualRightWord_compact_holomorphy
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "G" => KPSmoothLocalQuotientCharts.ActualCover F ζ hζ
local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U

include C R P H in
 theorem spherical_word_numerators
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (w : List (Fin (groupDimension F))) :
    ∃ A : ℂ → G → ℂ,
      (∀ s, (1 / 3 : ℝ) < s.re → ∀ g, A s g = actualRightWord F ζ hζ w
        (fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
          (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
            (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out c) * h)) g) ∧
      (∀ g, MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain) ∧
      ∀ c ∈ KPContinuation.spectralDomain,
        ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
          ∃ N : ℂ → G → ℂ,
            (∀ g, AnalyticOnNhd ℂ (fun s => N s g) (Metric.ball c r)) ∧
            ContinuousOn (fun p : ℂ × G => N p.1 p.2) (Metric.ball c r ×ˢ Set.univ) ∧
            ∀ s ∈ Metric.ball c r, s ≠ c → N s = (s - c) • A s := by
  by_cases hv : v = 0
  · subst v
    refine ⟨fun _ _ => 0, ?_, fun g s hs => (analyticAt_const).meromorphicAt, ?_⟩
    · intro s hs g
      have hz : (KPContFlatSourceRecipe.flatR F ζ hζ s
          (0 : KPContActualSphericalFlatStage.Stage F ζ hζ U).val).val = fun _ => 0 := by
        funext h
        simp
      rw [hz]
      simp only [tsum_zero]
      have hw : actualRightWord F ζ hζ w (fun _ => 0) = fun _ => 0 := by
        induction w with
        | nil => rfl
        | cons b w ih =>
          simp only [actualRightWord, ih]
          funext h
          exact deriv_const _ _
      exact (congrFun hw g).symm
    · intro c hc
      obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp KPContinuation.spectralDomain_isOpen c hc
      exact ⟨r, hr, hb, fun _ _ => 0, fun _ _ _ => analyticAt_const,
        continuousOn_const, fun s hs hne => by ext g; simp⟩
  · obtain ⟨Z, hch, hlocal⟩ := scalar_line_construction F ζ hζ C R P H U v hv
    let A : ℂ → G → ℂ := fun s => actualRightWord F ζ hζ w
      (groupScalar F ζ hζ C R P H U (Z s))
    have hwordlocal (c : ℂ) (hc : c ∈ KPContinuation.spectralDomain) :
        ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
          ∃ N : ℂ → G → ℂ,
            (∀ g, AnalyticOnNhd ℂ (fun s => N s g) (Metric.ball c r)) ∧
            ContinuousOn (fun p : ℂ × G => N p.1 p.2) (Metric.ball c r ×ˢ Set.univ) ∧
            ∀ s ∈ Metric.ball c r, s ≠ c → N s = (s - c) • A s := by
      obtain ⟨r, hr, hb, N, hN, he⟩ := hlocal c hc
      let M : ℂ → G → ℂ := fun s => actualRightWord F ζ hζ w
        (groupScalar F ζ hζ C R P H U (N s))
      have hM (D : GroupChart F ζ hζ level R P H) :=
        actualRightWord_compact_holomorphy D _ _ (hN.right_holomorphic D) w
      refine ⟨r, hr, hb, M,
        scalar_analytic_of_right_holomorphic F ζ hζ C R P H U M _ Metric.isOpen_ball hM, ?_, ?_⟩
      · apply actual_joint_of_groupCharts (U := level) (R := R) (P := P) (H := H)
          M _ Metric.isOpen_ball _ hM
        intro s hs g u
        exact actual_word_right_level (U := level) _
          (fun g u => (KPContActualCutoffSmoothDescent.lift_covariance F ζ hζ C R P H U (N s)).2.1 g u)
          w g u
      · intro s hs hne
        dsimp [M, A]
        rw [he s hs hne, word_smul]
    refine ⟨A, ?_, ?_, hwordlocal⟩
    · intro s hs g
      have hz : groupScalar F ζ hζ C R P H U (Z s) =
          fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
              (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out c) * h) := funext (hch s hs)
      exact congrFun (congrArg (actualRightWord F ζ hζ w) hz) g
    · intro g c hc
      obtain ⟨r, hr, hb, N, hNa, hNj, he⟩ := hwordlocal c hc
      have hn := ((hNa g) c (Metric.mem_ball_self hr)).meromorphicAt
      have hq : MeromorphicAt (fun s => N s g / (s - c)) c :=
        hn.div ((analyticAt_id.sub analyticAt_const).meromorphicAt)
      apply hq.congr
      filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)),
        self_mem_nhdsWithin] with s hs hne
      have hsne : s ≠ c := by simpa using hne
      have heq := congrFun (he s hs hsne) g
      change N s g = (s - c) * A s g at heq
      rw [heq]
      exact mul_div_cancel_left₀ (A s g) (sub_ne_zero.mpr hsne)

end DedekindZetaZeroFree.ResidueContinuity.ScalarSourceJointContinuity

end

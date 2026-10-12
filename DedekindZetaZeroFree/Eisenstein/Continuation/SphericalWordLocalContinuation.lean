module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SphericalScalarPoleClearing

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open Filter
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource
open KPLiteralRaw KPContActualSphericalRightFieldIdentification
open KPContActualCutoffPlusClearedGerm
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_line_construction → scalar_line_construction
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_analytic_of_right_holomorphic → scalar_analytic_of_right_holomorphic
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming word_smul → word_smul
open _root_.DedekindZetaZeroFree.KPContinuation.NativeWordCompactHolomorphy renaming actualRightWord_compact_holomorphy → actualRightWord_compact_holomorphy
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming word_zero → word_zero
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "G" => KPContSectorCoveredQuotientVocabulary.ActualCover F ζ hζ

include C R P H in

theorem spherical_word_local_continuation
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (w : List (Fin (groupDimension F))) :
    ∃ A : ℂ → G → ℂ,
      (∀ s, (1 : ℝ) / 3 < s.re → ∀ g,
        A s g = actualRightWord F ζ hζ w
          (fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
              (rationalLift F ζ hζ (Quotient.out c) * h)) g) ∧
      ∀ c ∈ KPContinuation.spectralDomain,
        ∃ (r : ℝ) (N : ℂ → G → ℂ),
          0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
          (∀ g, AnalyticOnNhd ℂ (fun s => N s g) (Metric.ball c r)) ∧
          ∀ s ∈ Metric.ball c r, s ≠ c → ∀ g, N s g = (s-c) * A s g := by
  by_cases hv : v = 0
  · subst v
    refine ⟨fun _ _ => 0, ?_, ?_⟩
    · intro s hs g
      have hz : (KPContFlatSourceRecipe.flatR F ζ hζ s
          (0 : KPContActualSphericalFlatStage.Stage F ζ hζ U).val).val = fun _ => 0 := by
        funext h
        simp
      rw [hz]
      simp only [tsum_zero, word_zero]
    · intro c hc
      obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp KPContinuation.spectralDomain_isOpen c hc
      exact ⟨r, fun _ _ => 0, hr, hb, fun _ _ _ => analyticAt_const,
        fun _ _ _ _ => by simp⟩
  · obtain ⟨Z, hch, hlocal⟩ := scalar_line_construction F ζ hζ C R P H U v hv
    let A : ℂ → G → ℂ := fun s => actualRightWord F ζ hζ w
      (groupScalar F ζ hζ C R P H U (Z s))
    refine ⟨A, ?_, ?_⟩
    · intro s hs g
      have hz : groupScalar F ζ hζ C R P H U (Z s) =
          fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
              (rationalLift F ζ hζ (Quotient.out c) * h) := funext (hch s hs)
      exact congrFun (congrArg (actualRightWord F ζ hζ w) hz) g
    · intro c hc
      obtain ⟨r, hr, hb, N, hN, he⟩ := hlocal c hc
      let M : ℂ → G → ℂ := fun s => actualRightWord F ζ hζ w
        (groupScalar F ζ hζ C R P H U (N s))
      have hM (D : GroupChart F ζ hζ level R P H) :
          KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
            (fun s x => M s (D.groupLift x)) (Metric.ball c r) :=
        actualRightWord_compact_holomorphy D _ _ (hN.right_holomorphic D) w
      refine ⟨r, M, hr, hb,
        scalar_analytic_of_right_holomorphic F ζ hζ C R P H U M _ Metric.isOpen_ball hM, ?_⟩
      intro s hs hne g
      change actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U (N s)) g = _
      rw [he s hs hne, word_smul]
      rfl

end DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource

end

module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightDifferentialWords.CompactHolomorphy
public import DedekindZetaZeroFree.Eisenstein.Continuation.FiniteWordChamberReconstruction
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.ResolventSeriesEquality

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff
open MeasureTheory Filter
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
open _root_.DedekindZetaZeroFree renaming canonicalRealization → canonicalRealization
open _root_.DedekindZetaZeroFree.KPContActualSphericalFlatStage renaming stageConclusions → stageConclusions
open _root_.DedekindZetaZeroFree.KPContinuation.NativeWordCompactHolomorphy renaming actualRightWord_compact_holomorphy → actualRightWord_compact_holomorphy
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming lift_eq → lift_eq
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

 def cutoff (T : ℝ) : KPCutoffSource.SmoothCuspCutoff T where
  toFun t := Real.smoothTransition (t - T)
  smooth := Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  zero_below t ht := Real.smoothTransition.zero_of_nonpos (by linarith)
  one_above t ht := Real.smoothTransition.one_of_one_le (by linarith)

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem word_smul (w : List (Fin (groupDimension F))) (c : ℂ)
    (u : KPContSectorCoveredQuotientVocabulary.ActualCover F ζ hζ → ℂ) :
    actualRightWord F ζ hζ w (c • u) = c • actualRightWord F ζ hζ w u := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [actualRightWord, ih]
    funext g
    exact deriv_const_mul_field c

variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
local notation "G" => KPContSectorCoveredQuotientVocabulary.ActualCover F ζ hζ

 theorem scalar_analytic_of_right_holomorphic
    (u : ℂ → G → ℂ) (O : Set ℂ) (hO : IsOpen O)
    (hu : ∀ D : GroupChart F ζ hζ level R P H,
      KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
        (fun s x => u s (D.groupLift x)) O) (g : G) :
    AnalyticOnNhd ℂ (fun s => u s g) O := by
  obtain ⟨D, hD⟩ := chart_at_point F ζ hζ level R P H g
  let K : Set (KPContLocalNorm.Space (groupDimension F)) := {0}
  have hK : IsCompact K := isCompact_singleton
  have hKT : K ⊆ D.T.carrier := by
    intro x hx
    simpa only [K, Set.mem_singleton_iff.mp hx] using D.zero_mem
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨j, hj, he⟩ := (hu D).2 K hK hKT [(1, [])]
  let x : K := ⟨0, Set.mem_singleton 0⟩
  have hjg : Set.EqOn (fun s => j s x) (fun s => u s g) O := by
    intro s hs
    simpa only [KPContRightJets.rightCombination, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, KPContRightJets.rightWord, one_mul, add_zero,
      x, hD] using he s hs x
  have hd : DifferentiableOn ℂ (fun s => j s x) O := by
    let L : C(K, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM (R := ℂ) x
    exact L.differentiable.comp_differentiableOn hj
  exact (hd.congr hjg.symm).analyticOnNhd hO

 theorem scalar_line_construction
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U) (hv : v ≠ 0) :
    ∃ Z : ℂ → Smooth,
      (∀ s, (1 : ℝ) / 3 < s.re → ∀ g : G,
        groupScalar F ζ hζ C R P H U (Z s) g =
          ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
              (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out c) * g)) ∧
      ∀ c ∈ KPContinuation.spectralDomain,
        ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
          ∃ N : ℂ → Smooth,
            SmoothTaylorData F ζ hζ C R P H U (Metric.ball c r) N ∧
            ∀ s ∈ Metric.ball c r, s ≠ c →
              groupScalar F ζ hζ C R P H U (N s) =
                (s - c) • groupScalar F ζ hζ C R P H U (Z s) := by
  let ι : ℂ →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U :=
    LinearMap.toSpanSingleton ℂ _ v
  have hι : Function.Injective ι := by
    intro a b hab
    exact (smul_left_injective ℂ (m := v) hv) hab
  let realization : KPContActualFixedSectorRealization.LevelRealization
      F ζ hζ level R P H := canonicalRealization
  let T : ℝ := (H.atlas level).threshold + 1
  have hT : (H.atlas level).threshold < T := by dsimp [T]; linarith
  let χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U →
      KPCutoffSource.SmoothCuspCutoff T := fun _ => cutoff T
  have hf : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) KPContinuation.spectralDomain :=
    differentiableOn_const _
  obtain ⟨buffer, source, domain, W, hW, ⟨formula⟩⟩ :=
    kp_cont_actual_chamber_formula_equality F ζ hζ C R.adelicHaar R.adelic_isHaar R rfl
      P H U realization ι hι (fun _ => 1) hf T hT χ
  let Z : ℂ → Smooth := E F ζ hζ C R P H U KPContinuation.spectralDomain
    (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U
      R.adelicHaar R.adelic_isHaar rfl realization KPContinuation.spectralDomain)
    source.descent.cutoff W
  refine ⟨Z, ?_, ?_⟩
  · intro s hs g
    rw [formula.group_equal s hs g]
    unfold KPContActualChamberNormalSeries.E
    congr 1
    funext q
    unfold KPContActualChamberNormalSeries.term KPContActualSphericalFlatStage.L
      KPContFlatCommonLevelKernel.L
    simp [ι, lift_eq]
  · have hStage := stageConclusions F ζ hζ C R P H U ι hι
    have hHilb := kp_cont_actual_hilbert_simple_germs F ζ hζ C R P H U
      R.adelicHaar R.adelic_isHaar rfl realization ι hι hStage
      KPContinuation.spectralDomain KPContinuation.spectralDomain_isOpen Set.Subset.rfl
      (fun _ => 1) hf buffer χ source
    intro c hc
    obtain ⟨r, hr, hb, hi, w, hw, he, _⟩ := hHilb.simple_germs c hc
    obtain ⟨N⟩ := hW.continuation.every_germ c hc r hr hb hi w hw he
    exact ⟨r, hr, hb, numerator F ζ hζ C R P H U source.descent.cutoff c N.W,
      N.numerator_data, N.punctured_group⟩

 theorem spherical_word_scalar_producer
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (w : List (Fin (groupDimension F))) :
    ∃ A N : ℂ → G → ℂ,
      (∀ s, (1 : ℝ) / 3 < s.re → ∀ g,
        A s g = actualRightWord F ζ hζ w
          (fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
              (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out c) * h)) g) ∧
      (∀ g, MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain) ∧
      ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
        (∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → N s = s • A s) ∧
        (∀ g, AnalyticOnNhd ℂ (fun s => N s g) (Metric.ball (0 : ℂ) r)) ∧
        (∀ D : GroupChart F ζ hζ level R P H,
          KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
            (fun s x => N s (D.groupLift x)) (Metric.ball (0 : ℂ) r)) := by
  by_cases hv : v = 0
  · subst v
    refine ⟨fun _ _ => 0, fun _ _ => 0, ?_, ?_, 1 / 6, by norm_num,
      KPContinuation.exceptionalBall_subset_spectralDomain, ?_, ?_, ?_⟩
    · intro s hs g
      have hz : (KPContFlatSourceRecipe.flatR F ζ hζ s
          (0 : KPContActualSphericalFlatStage.Stage F ζ hζ U).val).val = fun _ => 0 := by
        funext h
        simp
      rw [hz]
      simp only [tsum_zero]
      have hwz : actualRightWord F ζ hζ w (fun _ => 0) = fun _ => 0 := by
        induction w with
        | nil => rfl
        | cons b w ih =>
          simp only [actualRightWord, ih]
          funext h
          exact deriv_const _ _
      exact (congrFun hwz g).symm
    · intro g s hs
      exact (analyticAt_const (v := (0 : ℂ))).meromorphicAt
    · intro s hs hne
      ext g
      simp
    · intro g s hs
      exact analyticAt_const
    · intro D
      refine ⟨fun s hs => contDiffOn_const, ?_⟩
      intro K hK hKT terms
      exact ⟨fun _ => 0, differentiableOn_const _, fun s hs x => by
        have hz (a : List (Fin (groupDimension F))) :
            KPContRightJets.rightWord D.fields a (fun _ => (0 : ℂ)) = fun _ => 0 := by
          induction a with
          | nil => rfl
          | cons b a ih => simp [KPContRightJets.rightWord, ih]
        simp [KPContRightJets.rightCombination, hz]⟩
  · obtain ⟨Z, hch, hlocal⟩ := scalar_line_construction F ζ hζ C R P H U v hv
    let A : ℂ → G → ℂ := fun s => actualRightWord F ζ hζ w
      (groupScalar F ζ hζ C R P H U (Z s))
    have hwordlocal (c : ℂ) (hc : c ∈ KPContinuation.spectralDomain) :
        ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
          ∃ N : ℂ → G → ℂ,
            (∀ D : GroupChart F ζ hζ level R P H,
              KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
                (fun s x => N s (D.groupLift x)) (Metric.ball c r)) ∧
            (∀ g, AnalyticOnNhd ℂ (fun s => N s g) (Metric.ball c r)) ∧
            ∀ s ∈ Metric.ball c r, s ≠ c → N s = (s - c) • A s := by
      obtain ⟨r, hr, hb, N, hN, he⟩ := hlocal c hc
      let M : ℂ → G → ℂ := fun s => actualRightWord F ζ hζ w
        (groupScalar F ζ hζ C R P H U (N s))
      have hM (D : GroupChart F ζ hζ level R P H) :
          KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
            (fun s x => M s (D.groupLift x)) (Metric.ball c r) :=
        actualRightWord_compact_holomorphy D _ _ (hN.right_holomorphic D) w
      refine ⟨r, hr, hb, M, hM,
        scalar_analytic_of_right_holomorphic F ζ hζ C R P H U M _ Metric.isOpen_ball hM, ?_⟩
      intro s hs hne
      dsimp [M, A]
      rw [he s hs hne, word_smul]
    have hm (g : G) : MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain := by
      intro c hc
      obtain ⟨r, hr, hb, N, hNj, hNa, he⟩ := hwordlocal c hc
      have hcenter : c ∈ Metric.ball c r := Metric.mem_ball_self hr
      have hn := ((hNa g) c hcenter).meromorphicAt
      have hq : MeromorphicAt (fun s => N s g / (s - c)) c :=
        hn.div ((analyticAt_id.sub analyticAt_const).meromorphicAt)
      apply hq.congr
      filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hcenter),
        self_mem_nhdsWithin] with s hs hne
      have hsne : s ≠ c := by simpa using hne
      have heq := congrFun (he s hs hsne) g
      change N s g = (s - c) * A s g at heq
      rw [heq]
      exact mul_div_cancel_left₀ (A s g) (sub_ne_zero.mpr hsne)
    have hzero : (0 : ℂ) ∈ KPContinuation.spectralDomain := by
      norm_num [KPContinuation.spectralDomain]
    obtain ⟨r, hr, hb, N, hNj, hNa, he⟩ := hwordlocal 0 hzero
    refine ⟨A, N, ?_, hm, r, hr, hb, ?_, hNa, hNj⟩
    · intro s hs g
      have hz : groupScalar F ζ hζ C R P H U (Z s) =
          fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
              (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out c) * h) :=
        funext (hch s hs)
      exact congrFun (congrArg (actualRightWord F ζ hζ w) hz) g
    · simpa only [sub_zero] using he

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer

end

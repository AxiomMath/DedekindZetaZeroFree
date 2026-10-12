module

public import DedekindZetaZeroFree.Eisenstein.Residues.Spherical.EigenOrthogonalCenters

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff
open MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming cutoff → cutoff
open _root_.DedekindZetaZeroFree renaming canonicalRealization → canonicalRealization
open _root_.DedekindZetaZeroFree.KPContActualSphericalFlatStage renaming stageConclusions → stageConclusions
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming lift_eq → lift_eq
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
local notation "G" => KPContSectorCoveredQuotientVocabulary.ActualCover F ζ hζ

open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_analytic_of_right_holomorphic → scalar_analytic_of_right_holomorphic
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming word_smul → word_smul
open _root_.DedekindZetaZeroFree.KPContinuation.NativeWordCompactHolomorphy renaming actualRightWord_compact_holomorphy → actualRightWord_compact_holomorphy
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming word_zero → word_zero
theorem spherical_word_scalar_hilbert_orthogonal_producer
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
            (fun s x => N s (D.groupLift x)) (Metric.ball (0 : ℂ) r)) ∧
        ∃ Z : Smooth, ∃ z : KPContActualAllCuspSource.Sector F ζ hζ C R P H U,
          KPContActualSmoothLineGluing.Represents F ζ hζ level R P H Z.val z ∧
          (z, KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) 0 • z) ∈
            (sourceLaplacian F ζ hζ C R P H U).graph ∧
          CuspEigentestOrthogonal F ζ hζ C R P H U 0 z ∧
          (∀ g : G, KPMsGreenFlux.casimir F ζ hζ
            (groupScalar F ζ hζ C R P H U Z) g =
            KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) 0 *
              groupScalar F ζ hζ C R P H U Z g) ∧
          N 0 = actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U Z) ∧
          (KPGlobalResidualConstruction.IncomingFiberOrthogonality.AllCuspMeanZero
            F ζ hζ C R P H U Z → Z = 0) := by
  by_cases hv : v = 0
  · subst v
    refine ⟨fun _ _ => 0, fun _ _ => 0, ?_, ?_, 1 / 6, by norm_num,
      KPContinuation.exceptionalBall_subset_spectralDomain, ?_, ?_, ?_, 0, 0, ?_, ?_, ?_, ?_, ?_, fun _ => rfl⟩
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
    · have hs : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H
          (0 : Smooth).val).val = 0 := by
        rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
        exact congrArg Subtype.val (LinearEquiv.map_zero
          (KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm)
      refine ⟨hs ▸ (MemLp.zero : MemLp
        (0 : KPContActualAllCuspSource.Covered F ζ hζ C R P H U → ℂ)
        2 (KPContActualAllCuspSource.measure F ζ hζ C R P H U)), ?_⟩
      simp only [hs, MemLp.toLp_zero]
      rfl
    · simpa using (sourceLaplacian F ζ hζ C R P H U).graph.zero_mem
    · intro test t hrep hmean heig
      exact inner_zero_right t
    · intro g
      have hz : groupScalar F ζ hζ C R P H U (0 : Smooth) = 0 := by
        have he := groupScalar_smul F ζ hζ C R P H U (0 : ℂ) (0 : Smooth)
        simpa using he
      rw [hz]
      have he := ResidualSphericalGeometry.casimir_smul F ζ hζ (0 : ℂ) (0 : G → ℂ) g
      simpa using he
    · have hz : groupScalar F ζ hζ C R P H U (0 : Smooth) = 0 := by
        have he := groupScalar_smul F ζ hζ C R P H U (0 : ℂ) (0 : Smooth)
        simpa using he
      rw [hz]
      change (fun _ => (0 : ℂ)) = actualRightWord F ζ hζ w (fun _ => 0)
      rw [word_zero]
  · obtain ⟨Z, hch, hlocal⟩ := ResidualSphericalGeometry.spherical_scalar_native_orthogonal_centers F ζ hζ C R P H U v hv
    let A : ℂ → G → ℂ := fun s => actualRightWord F ζ hζ w
      (groupScalar F ζ hζ C R P H U (Z s))
    have hwordlocal (c : ℂ) (hc : c ∈ KPContinuation.spectralDomain) :
        ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
          ∃ N : ℂ → G → ℂ,
            (∀ D : GroupChart F ζ hζ level R P H,
              KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
                (fun s x => N s (D.groupLift x)) (Metric.ball c r)) ∧
            (∀ g, AnalyticOnNhd ℂ (fun s => N s g) (Metric.ball c r)) ∧
            (∀ s ∈ Metric.ball c r, s ≠ c → N s = (s - c) • A s) ∧
            ∃ Z : Smooth, ∃ z : KPContActualAllCuspSource.Sector F ζ hζ C R P H U,
              KPContActualSmoothLineGluing.Represents F ζ hζ level R P H Z.val z ∧
              (z, KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) c • z) ∈
                (sourceLaplacian F ζ hζ C R P H U).graph ∧
              CuspEigentestOrthogonal F ζ hζ C R P H U c z ∧
              (∀ g : G, KPMsGreenFlux.casimir F ζ hζ
                (groupScalar F ζ hζ C R P H U Z) g =
                KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) c *
                  groupScalar F ζ hζ C R P H U Z g) ∧
              N c = actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U Z) ∧
              (KPGlobalResidualConstruction.IncomingFiberOrthogonality.AllCuspMeanZero
                F ζ hζ C R P H U Z → Z = 0) := by
      obtain ⟨r, hr, hb, N, hN, he, ⟨z, hz, heig, horth⟩, hnative, hcus⟩ := hlocal c hc
      let M : ℂ → G → ℂ := fun s => actualRightWord F ζ hζ w
        (groupScalar F ζ hζ C R P H U (N s))
      have hM (D : GroupChart F ζ hζ level R P H) :
          KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
            (fun s x => M s (D.groupLift x)) (Metric.ball c r) :=
        actualRightWord_compact_holomorphy D _ _ (hN.right_holomorphic D) w
      refine ⟨r, hr, hb, M, hM,
        scalar_analytic_of_right_holomorphic F ζ hζ C R P H U M _ Metric.isOpen_ball hM, ?_, N c, z, hz, heig, horth, hnative, rfl, hcus⟩
      intro s hs hne
      dsimp [M, A]
      rw [he s hs hne, word_smul]
    have hm (g : G) : MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain := by
      intro c hc
      obtain ⟨r, hr, hb, N, hNj, hNa, he, _⟩ := hwordlocal c hc
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
    obtain ⟨r, hr, hb, N, hNj, hNa, he, hcent⟩ := hwordlocal 0 hzero
    refine ⟨A, N, ?_, hm, r, hr, hb, ?_, hNa, hNj, hcent⟩
    · intro s hs g
      have hz : groupScalar F ζ hζ C R P H U (Z s) =
          fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
              (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out c) * h) :=
        funext (hch s hs)
      exact congrFun (congrArg (actualRightWord F ζ hζ w) hz) g
    · simpa only [sub_zero] using he

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end

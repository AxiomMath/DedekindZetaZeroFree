module

public import DedekindZetaZeroFree.Eisenstein.Residues.Spherical.BoundaryCenters

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
variable {F : Type} [Field F] [NumberField F]
variable {SS : SArithmeticData F} {η : RayClassCharacter F SS.modulus}
variable (AR : PrincipalMellin.ActualRecipe SS η)
variable (AP : KPGlobalTorusFiniteStages.CompatibleModelData F AR.A.zeta12 AR.A.primitive_zeta12)
variable (AC : KPGlobalTorusFiniteStages.LocalFiberData F AR.A.zeta12 AR.A.primitive_zeta12 AP)
variable (D : KPGlobalTorusInducingPlan.ModelData F AR.A.zeta12 AR.A.primitive_zeta12)
variable (Haar : KPSmoothLocalQuotientCharts.HaarRecipe F AR.A.zeta12 AR.A.primitive_zeta12)
variable (Transport : KPMsFixedHaarDisintegration.SphericalTransport F AR.A.zeta12 AR.A.primitive_zeta12)
variable (H : KPMsFixedHaarDisintegration.AllLevels F AR.A.zeta12 AR.A.primitive_zeta12 Haar Transport)
variable (U : KPMsRationalCompactCrossPairing.Level F AR.A.zeta12 AR.A.primitive_zeta12)
local notation "level" => KPContActualAllCuspSource.level F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U
local notation "G" => KPContSectorCoveredQuotientVocabulary.ActualCover F AR.A.zeta12 AR.A.primitive_zeta12

open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_analytic_of_right_holomorphic → scalar_analytic_of_right_holomorphic
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming word_smul → word_smul
open _root_.DedekindZetaZeroFree.KPContinuation.NativeWordCompactHolomorphy renaming actualRightWord_compact_holomorphy → actualRightWord_compact_holomorphy
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming word_zero → word_zero
theorem spherical_word_scalar_hilbert_boundary_producer
    (v : KPContActualSphericalFlatStage.Stage F AR.A.zeta12 AR.A.primitive_zeta12 U)
    (w : List (Fin (groupDimension F))) :
    ∃ A N : ℂ → G → ℂ,
      (∀ s, (1 : ℝ) / 3 < s.re → ∀ g,
        A s g = actualRightWord F AR.A.zeta12 AR.A.primitive_zeta12 w
          (fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F AR.A.zeta12 AR.A.primitive_zeta12 s v.val).val
              (KPLiteralRaw.rationalLift F AR.A.zeta12 AR.A.primitive_zeta12 (Quotient.out c) * h)) g) ∧
      (∀ g, MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain) ∧
      ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
        (∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → N s = s • A s) ∧
        (∀ g, AnalyticOnNhd ℂ (fun s => N s g) (Metric.ball (0 : ℂ) r)) ∧
        (∀ D : GroupChart F AR.A.zeta12 AR.A.primitive_zeta12 level Haar Transport H,
          KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
            (fun s x => N s (D.groupLift x)) (Metric.ball (0 : ℂ) r)) ∧
        ∃ Z : Smooth, ∃ z : KPContActualAllCuspSource.Sector F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U,
          KPContActualSmoothLineGluing.Represents F AR.A.zeta12 AR.A.primitive_zeta12 level Haar Transport H Z.val z ∧
          (z, KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) 0 • z) ∈
            (sourceLaplacian F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U).graph ∧
          LiteralSource.SphericalBoundaryProperty AR AP AC D Haar Transport H U v z ∧
          (∀ g : G, KPMsGreenFlux.casimir F AR.A.zeta12 AR.A.primitive_zeta12
            (groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U Z) g =
            KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) 0 *
              groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U Z g) ∧
          N 0 = actualRightWord F AR.A.zeta12 AR.A.primitive_zeta12 w (groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U Z) ∧
          (KPGlobalResidualConstruction.IncomingFiberOrthogonality.AllCuspMeanZero
            F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U Z → Z = 0) := by
  by_cases hv : v = 0
  · subst v
    refine ⟨fun _ _ => 0, fun _ _ => 0, ?_, ?_, 1 / 6, by norm_num,
      KPContinuation.exceptionalBall_subset_spectralDomain, ?_, ?_, ?_, 0, 0, ?_, ?_, ?_, ?_, ?_, fun _ => rfl⟩
    · intro s hs g
      have hz : (KPContFlatSourceRecipe.flatR F AR.A.zeta12 AR.A.primitive_zeta12 s
          (0 : KPContActualSphericalFlatStage.Stage F AR.A.zeta12 AR.A.primitive_zeta12 U).val).val = fun _ => 0 := by
        funext h
        simp
      rw [hz]
      simp only [tsum_zero]
      have hwz : actualRightWord F AR.A.zeta12 AR.A.primitive_zeta12 w (fun _ => 0) = fun _ => 0 := by
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
    · have hs : (KPContSectorLineL2Isometry.scalarRepresentative F AR.A.zeta12 AR.A.primitive_zeta12 level Haar Transport H
          (0 : Smooth).val).val = 0 := by
        rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
        exact congrArg Subtype.val (LinearEquiv.map_zero
          (KPContSectorScalarLineAlgebra.S F AR.A.zeta12 AR.A.primitive_zeta12 level Haar Transport H).symm)
      refine ⟨hs ▸ (MemLp.zero : MemLp
        (0 : KPContActualAllCuspSource.Covered F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U → ℂ)
        2 (KPContActualAllCuspSource.measure F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U)), ?_⟩
      simp only [hs, MemLp.toLp_zero]
      rfl
    · simpa using (sourceLaplacian F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U).graph.zero_mem
    · intro K hK ν hν x test t hrep heig hpin
      simp [KPContFlatCuspIncomingEvaluation.sheetEvaluation, KPContFlatCommonLevelKernel.L_formula, KPContFlatCuspIncomingEvaluation.zeroProjection, KPContFlatCuspIncomingEvaluation.projectedScalar]
    · intro g
      have hz : groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (0 : Smooth) = 0 := by
        have he := groupScalar_smul F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (0 : ℂ) (0 : Smooth)
        simpa using he
      rw [hz]
      have he := ResidualSphericalGeometry.casimir_smul F AR.A.zeta12 AR.A.primitive_zeta12 (0 : ℂ) (0 : G → ℂ) g
      simpa using he
    · have hz : groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (0 : Smooth) = 0 := by
        have he := groupScalar_smul F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (0 : ℂ) (0 : Smooth)
        simpa using he
      rw [hz]
      change (fun _ => (0 : ℂ)) = actualRightWord F AR.A.zeta12 AR.A.primitive_zeta12 w (fun _ => 0)
      rw [word_zero]
  · obtain ⟨Z, hch, hlocal⟩ := ResidualSphericalGeometry.spherical_scalar_native_boundary_centers AR AP AC D Haar Transport H U v hv
    let A : ℂ → G → ℂ := fun s => actualRightWord F AR.A.zeta12 AR.A.primitive_zeta12 w
      (groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (Z s))
    have hwordlocal (c : ℂ) (hc : c ∈ KPContinuation.spectralDomain) :
        ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
          ∃ N : ℂ → G → ℂ,
            (∀ D : GroupChart F AR.A.zeta12 AR.A.primitive_zeta12 level Haar Transport H,
              KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
                (fun s x => N s (D.groupLift x)) (Metric.ball c r)) ∧
            (∀ g, AnalyticOnNhd ℂ (fun s => N s g) (Metric.ball c r)) ∧
            (∀ s ∈ Metric.ball c r, s ≠ c → N s = (s - c) • A s) ∧
            ∃ Z : Smooth, ∃ z : KPContActualAllCuspSource.Sector F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U,
              KPContActualSmoothLineGluing.Represents F AR.A.zeta12 AR.A.primitive_zeta12 level Haar Transport H Z.val z ∧
              (z, KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) c • z) ∈
                (sourceLaplacian F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U).graph ∧
              (c = 0 → LiteralSource.SphericalBoundaryProperty AR AP AC D Haar Transport H U v z) ∧
              (∀ g : G, KPMsGreenFlux.casimir F AR.A.zeta12 AR.A.primitive_zeta12
                (groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U Z) g =
                KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) c *
                  groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U Z g) ∧
              N c = actualRightWord F AR.A.zeta12 AR.A.primitive_zeta12 w (groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U Z) ∧
              (KPGlobalResidualConstruction.IncomingFiberOrthogonality.AllCuspMeanZero
                F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U Z → Z = 0) := by
      obtain ⟨r, hr, hb, N, hN, he, ⟨z, hz, heig, horth⟩, hnative, hcus⟩ := hlocal c hc
      let M : ℂ → G → ℂ := fun s => actualRightWord F AR.A.zeta12 AR.A.primitive_zeta12 w
        (groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (N s))
      have hM (D : GroupChart F AR.A.zeta12 AR.A.primitive_zeta12 level Haar Transport H) :
          KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
            (fun s x => M s (D.groupLift x)) (Metric.ball c r) :=
        actualRightWord_compact_holomorphy D _ _ (hN.right_holomorphic D) w
      refine ⟨r, hr, hb, M, hM,
        scalar_analytic_of_right_holomorphic F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U M _ Metric.isOpen_ball hM, ?_, N c, z, hz, heig, horth, hnative, rfl, hcus⟩
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
    refine ⟨A, N, ?_, hm, r, hr, hb, ?_, hNa, hNj, ?_⟩
    · intro s hs g
      have hz : groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U (Z s) =
          fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F AR.A.zeta12 AR.A.primitive_zeta12 s v.val).val
              (KPLiteralRaw.rationalLift F AR.A.zeta12 AR.A.primitive_zeta12 (Quotient.out c) * h) :=
        funext (hch s hs)
      exact congrFun (congrArg (actualRightWord F AR.A.zeta12 AR.A.primitive_zeta12 w) hz) g
    · simpa only [sub_zero] using he
    · obtain ⟨Z0, z0, hz0, heig0, hboundary0, hnative0, hvalue0, hcus0⟩ := hcent
      exact ⟨Z0, z0, hz0, heig0, hboundary0 rfl, hnative0, hvalue0, hcus0⟩

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end

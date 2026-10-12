module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SphericalScalarPoleClearing
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactPeriodMeromorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
open Filter
namespace DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator
open KPLiteralRaw KPContActualSphericalRightFieldIdentification
open KPContActualCutoffPlusClearedGerm
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_line_construction → scalar_line_construction
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming word_smul → word_smul
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming word_zero → word_zero
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming literal_finite_word_chamber → literal_finite_word_chamber
open _root_.DedekindZetaZeroFree renaming canonicalRealization → canonicalRealization
open _root_.DedekindZetaZeroFree.KPContActualCommonDiskRightHolomorphy renaming continuous_of_pieces → continuous_of_pieces
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U

 theorem scalar_eq_lift (v : Smooth) :
    groupScalar F ζ hζ C R P H U v =
      KPContActualCommonDiskRightHolomorphy.lift F ζ hζ level R P H v.val := by
  unfold groupScalar KPContActualCommonDiskRightHolomorphy.lift
  unfold KPContActualCutoffSmoothDescent.scalar
  rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
  rfl

 theorem singleton_combination (w : List (Fin (groupDimension F)))
    (u : G F ζ hζ → ℂ) :
    KPContActualCommonDiskRightHolomorphy.rightCombination F ζ hζ [(1, w)] u =
      actualRightWord F ζ hζ w u := by
  funext g
  simp [KPContActualCommonDiskRightHolomorphy.rightCombination]

 theorem compact_word_holomorphy
    (D : Set (G F ζ hζ)) (hD : IsCompact D)
    (O : Set ℂ) (hO : IsOpen O) (Z : ℂ → Smooth)
    (hZ : SmoothTaylorData F ζ hζ C R P H U O Z)
    (w : List (Fin (groupDimension F))) :
    letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
    ∃ A : ℂ → C(D, ℂ), AnalyticOnNhd ℂ A O ∧
      ∀ s g, A s g = actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U (Z s)) g := by
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let re : KPContActualFixedSectorRealization.LevelRealization F ζ hζ level R P H :=
    canonicalRealization
  let terms : KPContActualCommonDiskRightHolomorphy.Combination F := [(1, w)]
  obtain ⟨n, p, hp⟩ := KPContActualRightCanonicalRefinement.compact_refinement re D hD
  have hc (s : ℂ) : ContinuousOn
      (actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U (Z s))) D := by
    simpa only [terms, singleton_combination, scalar_eq_lift] using
      continuous_of_pieces F ζ hζ level R P H p D hp terms (Z s)
  let A : ℂ → C(D, ℂ) := fun s => ⟨fun g =>
    actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U (Z s)) g,
    (hc s).restrict⟩
  refine ⟨A, ?_, fun _ _ => rfl⟩
  intro z hz
  obtain ⟨ρ, hρ, hρO⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hz)
  obtain ⟨b, hb, _⟩ := hZ.disks z ρ hρ hρO
  obtain ⟨f, a, hf, _, hfd, _, _⟩ :=
    (kp_cont_actual_common_disk_right_holomorphy F ζ hζ level R P H re O hO
      Z b z ρ hρ (Metric.ball_subset_closedBall.trans hρO) hb D hD terms).2.2
  have heq : Set.EqOn A f (Metric.ball z ρ) := by
    intro s hs
    ext g
    change actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U (Z s)) g = f s g
    simpa [terms, KPContActualCommonDiskRightHolomorphy.rightCombination,
      scalar_eq_lift] using (hf s hs g).symm
  exact ((hfd.congr heq).analyticOnNhd Metric.isOpen_ball) z (Metric.mem_ball_self hρ)

include C R P H in

private theorem spherical_word_compact_producer
    (D : Set (G F ζ hζ)) (hD : IsCompact D)
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (w : List (Fin (groupDimension F))) :
    letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
    ∃ A N : ℂ → C(D, ℂ),
      (∀ s, (1 : ℝ) / 3 < s.re → ∀ g,
        A s g = actualRightWord F ζ hζ w
          (fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
              (rationalLift F ζ hζ (Quotient.out c) * h)) g) ∧
      MeromorphicOn A KPContinuation.spectralDomain ∧
      ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
        (∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → N s = s • A s) ∧
        AnalyticOnNhd ℂ N (Metric.ball (0 : ℂ) r) := by
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
  by_cases hv : v = 0
  · subst v
    refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, 1 / 6, by norm_num,
      KPContinuation.exceptionalBall_subset_spectralDomain, ?_, ?_⟩
    · intro s hs g
      have hz : (KPContFlatSourceRecipe.flatR F ζ hζ s
          (0 : KPContActualSphericalFlatStage.Stage F ζ hζ U).val).val = fun _ => 0 := by
        funext h
        simp
      rw [hz]
      simp only [tsum_zero, word_zero]
      rfl
    · exact fun _ _ => analyticAt_const.meromorphicAt
    · intro s hs hn
      simp
    · exact fun _ _ => analyticAt_const
  · obtain ⟨Z, hch, hlocal⟩ := scalar_line_construction F ζ hζ C R P H U v hv
    let re : KPContActualFixedSectorRealization.LevelRealization F ζ hζ level R P H :=
      canonicalRealization
    let terms : KPContActualCommonDiskRightHolomorphy.Combination F := [(1, w)]
    obtain ⟨n, p, hp⟩ := KPContActualRightCanonicalRefinement.compact_refinement re D hD
    have hc (s : ℂ) : ContinuousOn
        (actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U (Z s))) D := by
      simpa only [terms, singleton_combination, scalar_eq_lift] using
        continuous_of_pieces F ζ hζ level R P H p D hp terms (Z s)
    let A : ℂ → C(D, ℂ) := fun s => ⟨fun g =>
      actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U (Z s)) g, (hc s).restrict⟩
    have hAnum (z : ℂ) (hz : z ∈ KPContinuation.spectralDomain) :
        ∃ (r : ℝ) (N : ℂ → C(D, ℂ)), 0 < r ∧
          Metric.ball z r ⊆ KPContinuation.spectralDomain ∧
          AnalyticOnNhd ℂ N (Metric.ball z r) ∧
          ∀ s ∈ Metric.ball z r, s ≠ z → N s = (s - z) • A s := by
      obtain ⟨r, hr, hb, W, hW, he⟩ := hlocal z hz
      obtain ⟨N, hN, hNe⟩ := compact_word_holomorphy F ζ hζ C R P H U D hD
        (Metric.ball z r) Metric.isOpen_ball W hW w
      refine ⟨r, N, hr, hb, hN, ?_⟩
      intro s hs hn
      ext g
      rw [hNe, he s hs hn, word_smul]
      rfl
    have hm : MeromorphicOn A KPContinuation.spectralDomain := by
      intro z hz
      obtain ⟨r, N, hr, hb, hN, he⟩ := hAnum z hz
      have hn := (hN z (Metric.mem_ball_self hr)).meromorphicAt
      have hq : MeromorphicAt (fun s => (s - z)⁻¹ • N s) z :=
        ((analyticAt_id.sub analyticAt_const).meromorphicAt.inv).smul hn
      apply hq.congr
      filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)),
        self_mem_nhdsWithin] with s hs hne
      rw [he s hs hne]
      exact inv_smul_smul₀ (sub_ne_zero.mpr hne) _
    obtain ⟨r, N, hr, hb, hN, he⟩ := hAnum 0 (by norm_num [KPContinuation.spectralDomain])
    refine ⟨A, N, ?_, hm, r, hr, hb, ?_, hN⟩
    · intro s hs g
      have hz : groupScalar F ζ hζ C R P H U (Z s) =
          fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
              (rationalLift F ζ hζ (Quotient.out c) * h) := funext (hch s hs)
      exact congrFun (congrArg (actualRightWord F ζ hζ w) hz) g
    · simpa only [sub_zero] using he

open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.FiniteCompactAssembly renaming finite_compact_numerator → finite_compact_numerator

include C R P H in

 theorem finite_literal_compact_numerator
    (D : Set (G F ζ hζ)) (hD : IsCompact D)
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
    ∃ (Q : ℂ → ℂ) (S T : ℂ → C(D, ℂ)) (r : ℝ),
      AnalyticOnNhd ℂ Q KPContinuation.spectralDomain ∧ Q 0 = 1 ∧
      MeromorphicOn S KPContinuation.spectralDomain ∧
      (∀ s, (1 : ℝ) / 3 < s.re → ∀ g, S s g = Q s * eisenstein F ζ hζ K f s g) ∧
      0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
      AnalyticOnNhd ℂ T (Metric.ball (0 : ℂ) r) ∧
      ∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → T s = s • S s := by
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
  obtain ⟨n, U, m, v, w, Q, B, hQ, hQ0, ⟨r₀, hr₀, hb₀, _⟩, hB, _, hch⟩ :=
    literal_finite_word_chamber F ζ hζ K hK f
  have hp (i : Fin n) (j : Fin (m i)) :=
    spherical_word_compact_producer F ζ hζ C R P H (U i) D hD (v i j) (w i j)
  choose A N hAc hAm r hr hb hclear hNa using hp
  obtain ⟨hS, ρ, hρ, hρsub, hT, he⟩ := finite_compact_numerator
    KPContinuation.spectralDomain B A N hB hAm r hr hb hNa hclear r₀ hr₀ hb₀
  refine ⟨Q, (fun s => ∑ i, ∑ j, B i j s • A i j s),
    (fun s => ∑ i, ∑ j, B i j s • N i j s), ρ, hQ, hQ0, hS, ?_, hρ,
    hρsub.trans hb₀, hT, he⟩
  intro s hs g
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  simp_rw [hAc _ _ s hs]
  exact (hch s hs g).symm

end DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator

end

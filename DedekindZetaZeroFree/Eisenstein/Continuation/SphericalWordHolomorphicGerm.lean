module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ArchimedeanJetEvaluation

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology ContDiff BigOperators
open Filter
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource.ArchSeries
open KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification
open KPContActualCutoffPlusClearedGerm
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_line_construction → scalar_line_construction
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming scalar_eq_lift → scalar_eq_lift
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming word_zero → word_zero
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

theorem sectionWord_eq (u : KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U)
    (w : List (Fin (groupDimension F))) :
    (sectionWord F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H w u).val =
      actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U u) := by
  rw [scalar_eq_lift]
  rfl

theorem sectionWord_holomorphic {O : Set ℂ} (hO : IsOpen O)
    (Z : ℂ → KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U)
    (hZ : SmoothTaylorData F ζ hζ C R P H U O Z)
    (w : List (Fin (groupDimension F))) :
    KPGlobalEisensteinData.SmoothHolomorphicOn (jets F ζ hζ)
      (fun s => sectionWord F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H w (Z s)) O := by
  intro s hs
  obtain ⟨t,ht,htO⟩ := Metric.isOpen_iff.mp hO s hs
  let ρ := t/2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hclosed : Metric.closedBall s ρ ⊆ O := by
    intro z hz
    apply htO
    apply Metric.mem_ball.mpr
    apply (Metric.mem_closedBall.mp hz).trans_lt
    dsimp [ρ]
    linarith
  obtain ⟨b,hb,_⟩ := hZ.disks s ρ hρ hclosed
  exact ⟨ρ,hρ,Metric.ball_subset_closedBall.trans hclosed,
    fun n => sectionWord F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H w (b n),
    sectionWord_series F ζ hζ _ R P H Z b s ρ hb w⟩

theorem holomorphic_scalar {O : Set ℂ} {f : ℂ → space F ζ hζ}
    (hf : KPGlobalEisensteinData.SmoothHolomorphicOn (jets F ζ hζ) f O)
    (g : KPLiteralRaw.G F ζ hζ) : AnalyticOnNhd ℂ (fun s => (f s).val g) O := by
  intro s hs
  obtain ⟨r,hr,hb,a,ha⟩ := hf s hs
  exact (powerSeries_eval F ζ hζ hr ha g).analyticAt

include C R P H in
theorem spherical_word_germ
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (w : List (Fin (groupDimension F))) :
    ∃ (A : ℂ → KPLiteralRaw.G F ζ hζ → ℂ) (N : ℂ → space F ζ hζ) (r : ℝ),
      (∀ s, (1 : ℝ)/3 < s.re → ∀ g,
        A s g = actualRightWord F ζ hζ w
          (fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
              (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out c) * h)) g) ∧
      (∀ g, MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain) ∧
      0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
      (∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → (N s).val = s • A s) ∧
      KPGlobalEisensteinData.SmoothHolomorphicOn (jets F ζ hζ) N (Metric.ball 0 r) := by
  by_cases hv : v = 0
  · subst v
    refine ⟨fun _ _ => 0,fun _ => 0,1/6,?_,?_,by norm_num,
      KPContinuation.exceptionalBall_subset_spectralDomain,?_,?_⟩
    · intro s hs g
      have hz : (KPContFlatSourceRecipe.flatR F ζ hζ s
          (0 : KPContActualSphericalFlatStage.Stage F ζ hζ U).val).val = fun _ => 0 := by
        funext h
        simp
      rw [hz]
      simp only [tsum_zero, word_zero]
    · exact fun _ _ _ => analyticAt_const.meromorphicAt
    · intro s hs hn
      funext g
      simp
    · simpa only [LinearMap.zero_apply] using
        FiniteStageAnalytic.holomorphic_into_smooth (jets F ζ hζ)
          (0 : ℂ →ₗ[ℂ] space F ζ hζ) Metric.isOpen_ball (differentiableOn_const (0 : ℂ))
  · obtain ⟨Z,hch,hlocal⟩ := scalar_line_construction F ζ hζ C R P H U v hv
    let A := fun s => actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U (Z s))
    have hnum (c : ℂ) (hc : c ∈ KPContinuation.spectralDomain) :
        ∃ (r : ℝ) (N : ℂ → space F ζ hζ), 0 < r ∧
          Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
          KPGlobalEisensteinData.SmoothHolomorphicOn (jets F ζ hζ) N (Metric.ball c r) ∧
          ∀ s ∈ Metric.ball c r, s ≠ c → (N s).val = (s-c) • A s := by
      obtain ⟨r,hr,hb,W,hW,he⟩ := hlocal c hc
      let N := fun s => sectionWord F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H w (W s)
      refine ⟨r,N,hr,hb,sectionWord_holomorphic F ζ hζ C R P H U Metric.isOpen_ball W hW w,?_⟩
      intro s hs hn
      rw [sectionWord_eq, he s hs hn]
      change actualRightWord F ζ hζ w ((s-c) • groupScalar F ζ hζ C R P H U (Z s)) = _
      have hz := (word F ζ hζ w).map_smul (s-c)
        (sectionLift F ζ hζ (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H (Z s))
      have hz' := congrArg Subtype.val hz
      change actualRightWord F ζ hζ w
        ((s-c) • KPContActualCommonDiskRightHolomorphy.lift F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H (Z s).val) =
        (s-c) • actualRightWord F ζ hζ w
          (KPContActualCommonDiskRightHolomorphy.lift F ζ hζ
            (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H (Z s).val) at hz'
      rw [← scalar_eq_lift] at hz'
      exact hz'
    have hm (g : KPLiteralRaw.G F ζ hζ) : MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain := by
      intro c hc
      obtain ⟨r,N,hr,hb,hN,he⟩ := hnum c hc
      have ha := holomorphic_scalar F ζ hζ hN g
      have hq : MeromorphicAt (fun s => (N s).val g / (s-c)) c :=
        (ha c (Metric.mem_ball_self hr)).meromorphicAt.div
          ((analyticAt_id.sub analyticAt_const).meromorphicAt)
      apply hq.congr
      filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)),
        self_mem_nhdsWithin] with s hs hn
      have heq := congrFun (he s hs hn) g
      change (N s).val g = (s-c) * A s g at heq
      rw [heq]
      exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hn)
    obtain ⟨r,N,hr,hb,hN,he⟩ := hnum 0 (by norm_num [KPContinuation.spectralDomain])
    refine ⟨A,N,r,?_,hm,hr,hb,?_,hN⟩
    · intro s hs g
      have heq := funext (hch s hs)
      exact congrFun (congrArg (actualRightWord F ζ hζ w) heq) g
    · simpa only [sub_zero] using he

end DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource.ArchSeries

end

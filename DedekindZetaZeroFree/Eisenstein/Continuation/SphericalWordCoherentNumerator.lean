module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothGerms.RightWordTaylorSeries
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactWordNumerator

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff BigOperators
namespace DedekindZetaZeroFree.SharedSource
open KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification
open KPContActualCutoffPlusClearedGerm
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_line_construction → scalar_line_construction
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_analytic_of_right_holomorphic → scalar_analytic_of_right_holomorphic
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming word_smul → word_smul
open _root_.DedekindZetaZeroFree.KPContinuation.NativeWordCompactHolomorphy renaming actualRightWord_compact_holomorphy → actualRightWord_compact_holomorphy
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming scalar_eq_lift → scalar_eq_lift
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming word_zero → word_zero
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_zero → smooth_zero
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming finite_level_exists → finite_level_exists
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

include C R P H in

theorem sphericalWord_coherent_numerator
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (w : List (Fin (groupDimension F))) :
    ∃ A N : ℂ → KPLiteralRaw.Functions F ζ hζ,
      (∀ s, (1 / 3 : ℝ) < s.re → ∀ g,
        A s g = actualRightWord F ζ hζ w
          (fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
            (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
              (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out c) * h)) g) ∧
      (∀ g, MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (0 : ℂ) ρ ⊆ KPContinuation.spectralDomain ∧
        (∀ s ∈ Metric.ball (0 : ℂ) ρ, s ≠ 0 → N s = s • A s) ∧
        (∀ g, AnalyticOnNhd ℂ (fun s => N s g) (Metric.ball (0 : ℂ) ρ)) ∧
        (∀ s, KPLiteralRaw.Smooth F ζ hζ (N s)) ∧
        ∃ b : ℕ → KPLiteralRaw.Functions F ζ hζ,
          (∀ n, KPLiteralRaw.Smooth F ζ hζ (b n)) ∧
          ∀ (g : G F ζ hζ) (m : ℕ) (K : Set (ArchCoordinates F)),
            IsCompact K → K ⊆ archDomain F → ∀ r : ℝ, 0 < r → r < ρ →
            ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ M ≥ k, ∀ s : ℂ, ‖s‖ ≤ r → ∀ x ∈ K,
              ‖iteratedFDeriv ℝ m (fun y => N s (g * archChart F ζ hζ y) -
                ∑ n ∈ Finset.range M, s ^ n * b n (g * archChart F ζ hζ y)) x‖ < ε := by
  by_cases hv : v = 0
  · subst v
    obtain ⟨V⟩ := finite_level_exists F ζ hζ
    have hz : KPLiteralRaw.Smooth F ζ hζ (fun _ => 0) := smooth_zero F ζ hζ V
    refine ⟨fun _ _ => 0, fun _ _ => 0, ?_, ?_, 1 / 6, by norm_num,
      KPContinuation.exceptionalBall_subset_spectralDomain, ?_, ?_,
      fun _ => hz, fun _ _ => 0, fun _ => hz, ?_⟩
    · intro s hs g
      have he : (KPContFlatSourceRecipe.flatR F ζ hζ s
          (0 : KPContActualSphericalFlatStage.Stage F ζ hζ U).val).val = fun _ => 0 := by
        funext h; simp
      rw [he]
      simp only [tsum_zero, word_zero]
    · exact fun _ _ _ => analyticAt_const.meromorphicAt
    · intro s hs hn; ext g; simp
    · exact fun _ _ _ => analyticAt_const
    · intro g m K hK hKd r hr hrρ ε hε
      exact ⟨0, fun M hM s hs x hx => by simpa using hε⟩
  · obtain ⟨Z, hZch, hlocal⟩ := scalar_line_construction F ζ hζ C R P H U v hv
    let A : ℂ → KPLiteralRaw.Functions F ζ hζ := fun s =>
      actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U (Z s))
    have hm (g : G F ζ hζ) : MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain := by
      intro c hc
      obtain ⟨r, hr, hb, W, hW, he⟩ := hlocal c hc
      let T : ℂ → KPLiteralRaw.Functions F ζ hζ := fun s =>
        actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U (W s))
      have ha : AnalyticOnNhd ℂ (fun s => T s g) (Metric.ball c r) :=
        scalar_analytic_of_right_holomorphic F ζ hζ C R P H U T _ Metric.isOpen_ball
          (fun D => actualRightWord_compact_holomorphy D _ _ (hW.right_holomorphic D) w) g
      have hq : MeromorphicAt (fun s => T s g / (s-c)) c :=
        (ha c (Metric.mem_ball_self hr)).meromorphicAt.div
          ((analyticAt_id.sub analyticAt_const).meromorphicAt)
      apply hq.congr
      filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self hr)), self_mem_nhdsWithin] with s hs hn
      have hT : T s = (s-c) • A s := by
        dsimp [T, A]
        rw [he s hs hn, word_smul]
      rw [congrFun hT g]
      change (s-c) * A s g / (s-c) = A s g
      exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hn)
    obtain ⟨t, ht, htb, W, hW, hWe⟩ := hlocal 0 (by norm_num [KPContinuation.spectralDomain])
    let L : ℂ → KPLiteralRaw.Functions F ζ hζ := fun s =>
      actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U (W s))
    have hLa : ∀ g, AnalyticOnNhd ℂ (fun s => L s g) (Metric.ball (0 : ℂ) t) :=
      scalar_analytic_of_right_holomorphic F ζ hζ C R P H U L _ Metric.isOpen_ball
        (fun D => actualRightWord_compact_holomorphy D _ _ (hW.right_holomorphic D) w)
    let ρ := t / 2
    have hρ : 0 < ρ := half_pos ht
    have hρt : ρ < t := half_lt_self ht
    have hclosed : Metric.closedBall (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) t :=
      Metric.closedBall_subset_ball hρt
    obtain ⟨b, hbseries, _⟩ := hW.disks 0 ρ hρ hclosed
    refine ⟨A, L, ?_, hm, ρ, hρ, (Metric.ball_subset_ball hρt.le).trans htb, ?_,
      fun g => (hLa g).mono (Metric.ball_subset_ball hρt.le), ?_,
      (fun n => actualRightWord F ζ hζ w (groupScalar F ζ hζ C R P H U (b n))), ?_, ?_⟩
    · intro s hs g
      exact congrFun (congrArg (actualRightWord F ζ hζ w) (funext (hZch s hs))) g
    · intro s hs hn
      dsimp [L, A]
      rw [hWe s (Metric.ball_subset_ball hρt.le hs) hn, sub_zero, word_smul]
    · intro s
      dsimp [L]
      rw [scalar_eq_lift]
      exact actualRightWord_smooth _ (sectionLift_smooth _ R P H (W s)) w
    · intro n
      dsimp only
      rw [scalar_eq_lift]
      exact actualRightWord_smooth _ (sectionLift_smooth _ R P H (b n)) w
    · intro g m K hK hKd r₁ hr₁ hr₁ρ ε hε
      simp only [L, scalar_eq_lift]
      simpa only [sub_zero] using coherentSectionWord_compact_taylor _ R P H W b 0 ρ
        hbseries w g m K hK hKd r₁ hr₁ hr₁ρ ε hε

end DedekindZetaZeroFree.SharedSource

end

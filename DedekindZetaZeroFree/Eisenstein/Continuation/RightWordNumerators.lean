module

public import DedekindZetaZeroFree.Analysis.SmoothFunctions.MovingJetTaylorSeries
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactWordNumerator
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FlatProjection

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
open Filter
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw KPContActualSphericalRightFieldIdentification SharedSource
open KPGlobalResidualConstruction KPContActualCutoffPlusClearedGerm
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_line_construction → scalar_line_construction
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming scalar_analytic_of_right_holomorphic → scalar_analytic_of_right_holomorphic
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming word_smul → word_smul
open _root_.DedekindZetaZeroFree.KPContinuation.NativeWordCompactHolomorphy renaming actualRightWord_compact_holomorphy → actualRightWord_compact_holomorphy
open _root_.DedekindZetaZeroFree.KPContinuation.NativeWordCompactHolomorphy renaming actualRightWord_append → actualRightWord_append
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming scalar_eq_lift → scalar_eq_lift
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming word_zero → word_zero
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming literal_finite_word_chamber → literal_finite_word_chamber
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_zero → smooth_zero
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming finite_level_exists → finite_level_exists
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (M : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (μ : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ μ P)

include M μ P H in
theorem spherical_allWord_numerator (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U) (w : List (Fin (groupDimension F))) :
    ∃ A N : ℂ → KPLiteralRaw.Functions F ζ hζ,
      (∀ s, (1/3 : ℝ) < s.re → ∀ g, A s g = actualRightWord F ζ hζ w
        (fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
          (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val (rationalLift F ζ hζ (Quotient.out c) * h)) g) ∧
      (∀ s, KPLiteralRaw.Smooth F ζ hζ (A s)) ∧
      (∀ a g, MeromorphicOn (fun s => actualRightWord F ζ hζ a (A s) g) KPContinuation.spectralDomain) ∧
      ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
        (∀ s, KPLiteralRaw.Smooth F ζ hζ (N s)) ∧
        (∀ a g, AnalyticOnNhd ℂ (fun s => actualRightWord F ζ hζ a (N s) g) (Metric.ball (0 : ℂ) r)) ∧
        ∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → N s = s • A s := by
  by_cases hv : v = 0
  · subst v
    obtain ⟨V⟩ := finite_level_exists F ζ hζ
    refine ⟨fun _ => 0, fun _ => 0, ?_, fun _ => smooth_zero F ζ hζ V, ?_, 1/6,
      by norm_num, KPContinuation.exceptionalBall_subset_spectralDomain,
      fun _ => smooth_zero F ζ hζ V, ?_, ?_⟩
    · intro s hs g
      have hz : (KPContFlatSourceRecipe.flatR F ζ hζ s
          (0 : KPContActualSphericalFlatStage.Stage F ζ hζ U).val).val = fun _ => 0 := by ext h; simp
      rw [hz]; simp only [tsum_zero, word_zero]; rfl
    · intro a g; simp only [word_zero]; exact fun _ _ => analyticAt_const.meromorphicAt
    · intro a g; simp only [word_zero]; exact analyticOnNhd_const
    · intro s hs hn; ext g; simp
  · obtain ⟨Z,hch,hlocal⟩ := scalar_line_construction F ζ hζ M μ P H U v hv
    let A := fun s => actualRightWord F ζ hζ w (groupScalar F ζ hζ M μ P H U (Z s))
    have hs (s) : KPLiteralRaw.Smooth F ζ hζ (A s) := by
      dsimp [A]; rw [scalar_eq_lift]
      exact actualRightWord_smooth _ (sectionLift_smooth _ μ P H (Z s)) w
    have hloc (c : ℂ) (hc : c ∈ KPContinuation.spectralDomain) :
        ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
          ∃ N : ℂ → KPLiteralRaw.Functions F ζ hζ,
            (∀ s, KPLiteralRaw.Smooth F ζ hζ (N s)) ∧
            (∀ a g, AnalyticOnNhd ℂ (fun s => actualRightWord F ζ hζ a (N s) g) (Metric.ball c r)) ∧
            ∀ s ∈ Metric.ball c r, s ≠ c → N s = (s-c) • A s := by
      obtain ⟨r,hr,hb,W,hW,he⟩ := hlocal c hc
      let N := fun s => actualRightWord F ζ hζ w (groupScalar F ζ hζ M μ P H U (W s))
      refine ⟨r,hr,hb,N,?_,?_,?_⟩
      · intro s; dsimp [N]; rw [scalar_eq_lift]
        exact actualRightWord_smooth _ (sectionLift_smooth _ μ P H (W s)) w
      · intro a g
        have ha := scalar_analytic_of_right_holomorphic F ζ hζ M μ P H U
          (fun s => actualRightWord F ζ hζ (a ++ w) (groupScalar F ζ hζ M μ P H U (W s)))
          _ Metric.isOpen_ball (fun D => actualRightWord_compact_holomorphy D _ _
            (hW.right_holomorphic D) (a ++ w)) g
        simpa only [N, actualRightWord_append] using ha
      · intro s hs hn; dsimp [N,A]; rw [he s hs hn, word_smul]
    have hm (a) (g) : MeromorphicOn (fun s => actualRightWord F ζ hζ a (A s) g)
        KPContinuation.spectralDomain := by
      intro c hc
      obtain ⟨r,hr,hb,N,hNs,hNa,he⟩ := hloc c hc
      have hq : MeromorphicAt (fun s => actualRightWord F ζ hζ a (N s) g / (s-c)) c :=
        ((hNa a g c (Metric.mem_ball_self hr)).meromorphicAt).div
          ((analyticAt_id.sub analyticAt_const).meromorphicAt)
      apply hq.congr
      filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds c hr), self_mem_nhdsWithin] with s hsr hn
      rw [he s hsr hn, actualRightWord_smul _ _ (hs s) a]
      change (s-c) * actualRightWord F ζ hζ a (A s) g / (s-c) = _
      exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hn)
    obtain ⟨r,hr,hb,N,hNs,hNa,he⟩ := hloc 0 (by norm_num [KPContinuation.spectralDomain])
    refine ⟨A,N,?_,hs,hm,r,hr,hb,hNs,hNa,?_⟩
    · intro s hs g; exact congrFun (congrArg (actualRightWord F ζ hζ w) (funext (hch s hs))) g
    · simpa only [sub_zero] using he

include M μ P H in
theorem literal_allWord_numerator (K : Subgroup (KPLiteralRaw.G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ (q : ℂ → ℂ) (A N : ℂ → KPLiteralRaw.Functions F ζ hζ) (r : ℝ),
      AnalyticOnNhd ℂ q KPContinuation.spectralDomain ∧ q 0 = 1 ∧
      (∀ s, KPLiteralRaw.Smooth F ζ hζ (A s)) ∧
      (∀ a g, MeromorphicOn (fun s => actualRightWord F ζ hζ a (A s) g) KPContinuation.spectralDomain) ∧
      (∀ s, (1/3 : ℝ) < s.re → ∀ g, A s g = q s * eisenstein F ζ hζ K f s g) ∧
      0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
      (∀ s, KPLiteralRaw.Smooth F ζ hζ (N s)) ∧
      (∀ a g, AnalyticOnNhd ℂ (fun s => actualRightWord F ζ hζ a (N s) g) (Metric.ball (0 : ℂ) r)) ∧
      ∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → N s = s • A s := by
  obtain ⟨n,U,m,v,w,q,B,hq,hq0,hdisk,hB,hrec,hch⟩ := literal_finite_word_chamber F ζ hζ K hK f
  choose A N hAc hAs hAm r hr hb hNs hNa he using
    (fun (i : Fin n) (j : Fin (m i)) => spherical_allWord_numerator F ζ hζ M μ P H (U i) (v i j) (w i j))
  let AA := fun s => ∑ i, ∑ j, B i j s • A i j s
  let NN := fun s => ∑ i, ∑ j, B i j s • N i j s
  have hall : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ i j, s ∈ Metric.ball (0 : ℂ) (r i j) := by
    apply Filter.eventually_all.mpr; intro i
    apply Filter.eventually_all.mpr; intro j
    exact Metric.ball_mem_nhds _ (hr i j)
  obtain ⟨ρ,hρ,hρsub⟩ := Metric.mem_nhds_iff.mp
    (hall.and (KPContinuation.spectralDomain_isOpen.mem_nhds (by norm_num [KPContinuation.spectralDomain])))
  have hsm (s) : KPLiteralRaw.Smooth F ζ hζ (AA s) :=
    nativeSmooth_finset_sum _ _ (fun i _ => nativeSmooth_finset_sum _ _ (fun j _ =>
      (nativeSmoothSpace F ζ hζ).smul_mem (B i j s) (hAs i j s)))
  have hword (a) (s) : actualRightWord F ζ hζ a (AA s) =
      ∑ i, ∑ j, B i j s • actualRightWord F ζ hζ a (A i j s) := by
    dsimp [AA]
    rw [actualRightWord_finset_sum _ _ (fun i _ => nativeSmooth_finset_sum _ _
      (fun j _ => (nativeSmoothSpace F ζ hζ).smul_mem _ (hAs i j s))) a]
    simp_rw [actualRightWord_finset_sum _ _ (fun j _ =>
      (nativeSmoothSpace F ζ hζ).smul_mem _ (hAs _ j s)) a,
      actualRightWord_smul _ _ (hAs _ _ s) a]
  have hnsm (s) : KPLiteralRaw.Smooth F ζ hζ (NN s) :=
    nativeSmooth_finset_sum _ _ (fun i _ => nativeSmooth_finset_sum _ _ (fun j _ =>
      (nativeSmoothSpace F ζ hζ).smul_mem (B i j s) (hNs i j s)))
  have hnword (a) (s) : actualRightWord F ζ hζ a (NN s) =
      ∑ i, ∑ j, B i j s • actualRightWord F ζ hζ a (N i j s) := by
    dsimp [NN]
    rw [actualRightWord_finset_sum _ _ (fun i _ => nativeSmooth_finset_sum _ _
      (fun j _ => (nativeSmoothSpace F ζ hζ).smul_mem _ (hNs i j s))) a]
    simp_rw [actualRightWord_finset_sum _ _ (fun j _ =>
      (nativeSmoothSpace F ζ hζ).smul_mem _ (hNs _ j s)) a,
      actualRightWord_smul _ _ (hNs _ _ s) a]
  refine ⟨q,AA,NN,ρ,hq,hq0,hsm,?_,?_,hρ,(fun s hs => (hρsub hs).2),hnsm,?_,?_⟩
  · intro a g s hs
    simp only [hword, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact MeromorphicAt.fun_sum (fun i _ => MeromorphicAt.fun_sum (fun j _ =>
      ((hB i j) s hs).meromorphicAt.mul (hAm i j a g s hs)))
  · intro s hs g
    dsimp [AA]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hAc _ _ s hs]
    exact (hch s hs g).symm
  · intro a g s hs
    simp only [hnword, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.univ.analyticAt_fun_sum (fun i _ => Finset.univ.analyticAt_fun_sum (fun j _ =>
      ((hB i j) s (hρsub hs).2).mul (hNa i j a g s ((hρsub hs).1 i j))))
  · intro s hs hn
    dsimp [NN,AA]; simp_rw [he _ _ s ((hρsub hs).1 _ _) hn, smul_smul]
    simp only [Finset.smul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [smul_smul]
    congr 1
    ring

end DedekindZetaZeroFree.RootDerivatives

end

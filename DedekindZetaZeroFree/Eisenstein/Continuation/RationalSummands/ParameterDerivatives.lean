module

public import DedekindZetaZeroFree.Eisenstein.Continuation.RationalSummands.RightFlowDerivatives

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators Topology ContDiff

namespace DedekindZetaZeroFree.KPContinuation.ChamberNormalTerm

open KPContActualChamberNormalSeries

section GenericChart
open scoped Topology
variable {A E Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

set_option backward.isDefEq.respectTransparency.types false in

theorem chartPartialEq (h : A → E → Y) (s : A) (z : E)
    (hh : DifferentiableAt ℝ (Function.uncurry h) (s, z)) :
    fderiv ℝ (h s) z =
      (fderiv ℝ (Function.uncurry h) (s, z)).comp (ContinuousLinearMap.inr ℝ A E) := by
  exact (hh.hasFDerivAt.comp z (hasFDerivAt_prodMk_right s z)).fderiv

set_option backward.isDefEq.respectTransparency.types false in

theorem chartMixedPartial (h : A → E → Y) (s : A) (z : E)
    (hh : ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry h) (s, z)) (v : A) (w : E) :
    (fderiv ℝ (fun t => fderiv ℝ (h t) z) s) v w =
      (fderiv ℝ (fun x => fderiv ℝ (fun t => h t x) s) z) w v := by
  let H := Function.uncurry h
  let D := fderiv ℝ H
  let L := ContinuousLinearMap.inl ℝ A E
  let R := ContinuousLinearMap.inr ℝ A E
  let CR := (ContinuousLinearMap.compL ℝ E (A × E) Y).flip R
  let CL := (ContinuousLinearMap.compL ℝ A (A × E) Y).flip L
  have hD : HasFDerivAt D (fderiv ℝ D (s, z)) (s, z) :=
    (hh.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
  have hs : (fun t => fderiv ℝ (h t) z) =ᶠ[𝓝 s]
      (fun t => CR (D (t, z))) := by
    have hn := (hh.of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).eventually (by simp)
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hn] with t ht
    exact chartPartialEq h t z (ht.differentiableAt (by simp))
  have hz : (fun x => fderiv ℝ (fun t => h t x) s) =ᶠ[𝓝 z]
      (fun x => CL (D (s, x))) := by
    have hn := (hh.of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).eventually (by simp)
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.eventually hn] with x hx
    have hd : HasFDerivAt H (D (s, x)) (s, x) := (hx.differentiableAt (by simp)).hasFDerivAt
    have hleft : HasFDerivAt (fun t : A => H (t, x)) (CL (D (s, x))) s :=
      by convert hd.comp s (hasFDerivAt_prodMk_left (𝕜 := ℝ) s x) using 1 <;> rfl
    exact hleft.fderiv
  have hsd := CR.hasFDerivAt.comp s (hD.comp s (hasFDerivAt_prodMk_left s z))
  have hzd := CL.hasFDerivAt.comp z (hD.comp z (hasFDerivAt_prodMk_right s z))
  have hsde := hsd.fderiv
  have hzde := hzd.fderiv
  dsimp only [Function.comp_def] at hsde hzde
  rw [hs.fderiv_eq, hz.fderiv_eq, hsde, hzde]
  exact (hh.isSymmSndFDerivAt (by simp)).eq (v, 0) (0, w)

end GenericChart

namespace ParameterChart
open Filter
variable {A E Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedSpace ℂ Y] [IsScalarTower ℝ ℂ Y]
set_option backward.isDefEq.respectTransparency.types false in
private lemma partial_snd_hasDeriv (h k : ℂ → E → Y) (Ω : Set ℂ) (hΩ : IsOpen Ω) (U : Set E) (hU : IsOpen U)
 (hh : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry h) (Ω ×ˢ U))
 (hk : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry k) (Ω ×ˢ U))
 (hd : ∀ s ∈ Ω, ∀ z, z ∈ U → HasDerivAt (fun t => h t z) (k s z) s)
 (s : ℂ) (hs : s ∈ Ω) (z : E) (hz : z ∈ U) :
 HasDerivAt (fun t => fderiv ℝ (h t) z) (fderiv ℝ (k s) z) s := by
 have hlocal := hh.contDiffAt ((hΩ.prod hU).mem_nhds (show (s,z) ∈ Ω ×ˢ U from ⟨hs,hz⟩))
 have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
     (fun q : ℂ × E => h q.1 q.2) (s,z) := hlocal
 have hder : DifferentiableAt ℝ (fun t => fderiv ℝ (h t) z) s := by
   have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
       (Function.uncurry (fun t x => h t x)) (s,z) := hlocal
   exact (h2.fderiv (g := fun _ : ℂ => z) (m := (⊤ : ℕ∞)) contDiffAt_const (by simp)).differentiableAt (by simp)
 have heq : (ContinuousLinearMap.toSpanSingleton ℂ (fderiv ℝ (k s) z)).restrictScalars ℝ =
     fderiv ℝ (fun t => fderiv ℝ (h t) z) s := by
   ext d w
   rw [chartMixedPartial h s z hlocal d w]
   have ht : (fun x => (fderiv ℝ (fun t => h t x) s) d) =ᶠ[𝓝 z]
       (fun x => d • k s x) := by
     filter_upwards [hU.mem_nhds hz] with x hx
     rw [((hd s hs x hx).hasFDerivAt.restrictScalars ℝ).fderiv]
     rfl
   have hp := (hk.contDiffAt ((hΩ.prod hU).mem_nhds (show (s,z) ∈ Ω ×ˢ U from ⟨hs,hz⟩))).comp
     z (contDiffAt_const.prodMk contDiffAt_id)
   have hf := hp.differentiableAt (by simp)
   have hswap : ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry (fun x t => h t x)) (z,s) :=
     hlocal.comp (z,s) (contDiff_snd.prodMk contDiff_fst).contDiffAt
   have happ := (ContinuousLinearMap.apply ℝ Y d).hasFDerivAt.comp z
     ((hswap.fderiv (g := fun _ : E => s) (m := (⊤ : ℕ∞)) contDiffAt_const (by simp)).differentiableAt (by simp)).hasFDerivAt
   have he : (fderiv ℝ (fun x => (fderiv ℝ (fun t => h t x) s) d) z) w =
       ((fderiv ℝ (fun x => fderiv ℝ (fun t => h t x) s) z) w) d := by
     have he := happ.fderiv
     dsimp only [Function.comp_def] at he
     convert congrArg (fun T : E →L[ℝ] Y => T w) he using 1 <;> rfl
   rw [← he, ht.fderiv_eq]
   have hf' : DifferentiableAt ℝ (k s) z := hf
   change (d • fderiv ℝ (k s) z) w = (fderiv ℝ (d • k s) z) w
   rw [fderiv_const_smul hf' d]
 exact hasFDerivAt_of_restrictScalars ℝ hder.hasFDerivAt heq

section Words
variable {B : Type*}
open RightFrame.PullbackWords

private lemma joint_word (Ω : Set ℂ) (hΩ : IsOpen Ω) (O : Set E) (hO : IsOpen O)
    (fields : B → E → E) (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) O)
    (h : ℂ → E → ℂ)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry h) (Ω ×ˢ O)) (w : List B) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℂ × E => directionalWord fields w (h p.1) p.2) (Ω ×ˢ O) := by
  induction w with
  | nil => exact hh
  | cons b w ih =>
    intro p hp
    have hlocal := ih.contDiffAt ((hΩ.prod hO).mem_nhds hp)
    have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q : (ℂ × E) × E => directionalWord fields w (h q.1.1) q.2) (p,p.2) :=
      hlocal.comp (p,p.2) (contDiff_fst.fst.prodMk contDiff_snd).contDiffAt
    have hd := ContDiffAt.fderiv (f := fun q : ℂ × E => directionalWord fields w (h q.1))
      (g := fun q : ℂ × E => q.2) (m := (⊤ : ℕ∞)) hcomp contDiff_snd.contDiffAt (by simp)
    exact (hd.clm_apply ((hfields b).contDiffAt (hO.mem_nhds hp.2) |>.comp p contDiffAt_snd)).contDiffWithinAt

theorem word_hasDeriv (Ω : Set ℂ) (hΩ : IsOpen Ω) (O : Set E) (hO : IsOpen O)
    (fields : B → E → E) (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) O)
    (h k : ℂ → E → ℂ)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry h) (Ω ×ˢ O))
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry k) (Ω ×ˢ O))
    (hd : ∀ s ∈ Ω, ∀ x ∈ O, HasDerivAt (fun z => h z x) (k s x) s)
    (w : List B) (s : ℂ) (hs : s ∈ Ω) (x : E) (hx : x ∈ O) :
    HasDerivAt (fun z => directionalWord fields w (h z) x)
      (directionalWord fields w (k s) x) s := by
  induction w generalizing s x with
  | nil => exact hd s hs x hx
  | cons b w ih =>
    have hp := partial_snd_hasDeriv
      (fun z x => directionalWord fields w (h z) x)
      (fun z x => directionalWord fields w (k z) x) Ω hΩ O hO
      (joint_word Ω hΩ O hO fields hfields h hh w)
      (joint_word Ω hΩ O hO fields hfields k hk w) ih s hs x hx
    let ev : (E →L[ℝ] ℂ) →L[ℂ] ℂ :=
      { toFun := fun T => T (fields b x)
        map_add' := by intros; rfl
        map_smul' := by intros; rfl
        cont := (ContinuousLinearMap.apply ℝ ℂ (fields b x)).continuous }
    exact ev.hasFDerivAt.comp_hasDerivAt s hp

end Words

end ParameterChart

section ActualSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U) (f : ℂ → S)

private theorem term_holomorphic
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (q : Q F) (g : G F ζ hζ) :
    DifferentiableOn ℂ (fun s => term F ζ hζ U ι f q s g) V := by
  let ev : S →ₗ[ℂ] ℂ :=
    (LinearMap.proj (lift F ζ hζ q * g)).comp
      (KPContActualSphericalFlatStage.L F ζ hζ U ι 0)
  have hev : DifferentiableOn ℂ (fun s => ev (f s)) KPContinuation.spectralDomain :=
    ((⟨ev, ev.continuous_of_finiteDimensional⟩ : S →L[ℂ] ℂ).differentiable.comp_differentiableOn hf)
  have heq : (fun s => term F ζ hζ U ι f q s g) = fun s =>
      Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ (lift F ζ hζ q * g) : ℂ)) *
        ev (f s) := by
    funext s
    simp only [term, ev, LinearMap.comp_apply, LinearMap.proj_apply,
      KPContFlatCommonLevelKernel.L_formula, zero_mul, Complex.exp_zero, one_mul]
  rw [heq]
  apply ((Differentiable.differentiableOn (by fun_prop)).mul hev).mono
  intro z hz; change -(1 : ℝ)/6 < z.re; change (1 : ℝ)/3 < z.re at hz; linarith

theorem actual_parameterTerm_hasDeriv
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (q : Q F)
    (k : ℕ) (s : ℂ) (hs : s ∈ V) (g : G F ζ hζ) :
    HasDerivAt (fun z => mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] z g)
      (mixedJet F ζ hζ (term F ζ hζ U ι f q) (k+1) [] s g) s := by
  have hd := ((term_holomorphic F ζ hζ U ι f hf q g).contDiffOn
    (n := ⊤) KPChamberL2Defect.chamber_isOpen).differentiableOn_iteratedDerivWithin
    (m := k) (by simp) KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
  have hh := (hd.differentiableAt (KPChamberL2Defect.chamber_isOpen.mem_nhds hs)).hasDerivAt
  change HasDerivAt (fun z => iteratedDerivWithin k (fun t => term F ζ hζ U ι f q t g) V z)
    (iteratedDerivWithin (k+1) (fun t => term F ζ hζ U ι f q t g) V s) s
  rw [iteratedDerivWithin_succ, derivWithin_of_isOpen KPChamberL2Defect.chamber_isOpen hs]
  exact hh

private theorem alpha_right_chart_smooth (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => (KPContFlatSourceRecipe.alpha F ζ hζ
        (g * KPGlobalResidualConstruction.archChart F ζ hζ x) : ℂ))
      (KPGlobalResidualConstruction.archDomain F) := by
  apply contDiffOn_of_locally_contDiffOn
  intro x₀ hx₀
  obtain ⟨O, q, hO, hxO, hq, hqO, heq⟩ :=
    KPLiteralChamber.literal_right_to_left_chart_local_transition F ζ hζ g x₀ hx₀
  refine ⟨O, hO, hxO, ?_⟩
  have hleft := (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (KPContFlatLogNormSmooth.alpha_groupArchChart_mul_contDiffOn F ζ hζ
      (g * KPGlobalResidualConstruction.archChart F ζ hζ x₀))).of_le
    (show (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ ω by simp)
  have hc := hleft.comp hq hqO
  apply (hc.congr (fun x hx => congrArg
    (fun g => (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ)) (heq x hx))).mono
  exact Set.inter_subset_right

theorem actual_parameterSection_joint_right_chart_smooth
    (m : ℕ) (v : S) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℂ × KPGlobalResidualConstruction.ArchCoordinates F =>
        KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
          (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι) m p.1 v
          (g * KPGlobalResidualConstruction.archChart F ζ hζ p.2))
      (Set.univ ×ˢ KPGlobalResidualConstruction.archDomain F) := by
  have hmaps : Set.MapsTo (fun p : ℂ × KPGlobalResidualConstruction.ArchCoordinates F => p.2)
      (Set.univ ×ˢ KPGlobalResidualConstruction.archDomain F)
      (KPGlobalResidualConstruction.archDomain F) := fun p hp => hp.2
  have hα := (alpha_right_chart_smooth F ζ hζ g).comp contDiffOn_snd hmaps
  have hzero := (actual_parameterSection_right_chart_smooth F ζ hζ U ι 0 0 v g).comp
    contDiffOn_snd hmaps
  have heq : (fun p : ℂ × KPGlobalResidualConstruction.ArchCoordinates F =>
      KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
        (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι) m p.1 v
        (g * KPGlobalResidualConstruction.archChart F ζ hζ p.2)) =
      fun p => (KPContFlatSourceRecipe.alpha F ζ hζ
        (g * KPGlobalResidualConstruction.archChart F ζ hζ p.2) : ℂ)^m *
      Complex.exp (p.1 * (KPContFlatSourceRecipe.alpha F ζ hζ
        (g * KPGlobalResidualConstruction.archChart F ζ hζ p.2) : ℂ)) *
      KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
        (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι) 0 0 v
        (g * KPGlobalResidualConstruction.archChart F ζ hζ p.2) := by
    funext p
    simp only [KPContFlatStageJetHolomorphy.parameterSection,
      KPContFlatStageJetHolomorphy.L, KPContFlatSourceRecipe.flatR_formula,
      pow_zero, zero_mul, Complex.exp_zero, one_mul]
    ring
  rw [heq]
  exact ((hα.pow m).mul (contDiffOn_fst.mul hα).cexp).mul hzero

theorem actual_parameterTerm_joint_right_chart_smooth
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (q : Q F)
    (k : ℕ) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℂ × KPGlobalResidualConstruction.ArchCoordinates F =>
        mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] p.1
          (g * KPGlobalResidualConstruction.archChart F ζ hζ p.2))
      (V ×ˢ KPGlobalResidualConstruction.archDomain F) := by
  let B := Module.finBasis ℂ S
  have hVΩ : V ⊆ KPContinuation.spectralDomain := by
    intro z hz; change -(1 : ℝ)/6 < z.re; change (1 : ℝ)/3 < z.re at hz; linarith
  have hc (i : Fin (Module.finrank ℂ S)) (j : ℕ) :
      ContDiffOn ℝ (⊤ : ℕ∞)
        (iteratedDerivWithin j (fun z => B.repr (f z) i) V) V := by
    have hh : DifferentiableOn ℂ (fun z => B.repr (f z) i) V :=
      ((⟨B.coord i, (B.coord i).continuous_of_finiteDimensional⟩ : S →L[ℂ] ℂ).differentiable.comp_differentiableOn
        (hf.mono hVΩ))
    exact (((hh.contDiffOn (n := ⊤) KPChamberL2Defect.chamber_isOpen).differentiableOn_iteratedDerivWithin
      (m := j) (by simp) KPChamberL2Defect.chamber_isOpen.uniqueDiffOn).contDiffOn
      (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) KPChamberL2Defect.chamber_isOpen).restrict_scalars ℝ
  apply ContDiffOn.congr _ (fun p hp =>
    actual_parameterTerm_formula F ζ hζ U ι f hf q k p.1 hp.1 _)
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  have hcoeff := (hc i j).comp contDiffOn_fst
    (show Set.MapsTo (fun p : ℂ × KPGlobalResidualConstruction.ArchCoordinates F => p.1)
      (V ×ˢ KPGlobalResidualConstruction.archDomain F) V from fun p hp => hp.1)
  have hsection := (actual_parameterSection_joint_right_chart_smooth F ζ hζ U ι (k-j)
    (B i) (lift F ζ hζ q * g)).mono (Set.prod_mono (Set.subset_univ V) Set.Subset.rfl)
  exact (contDiffOn_const.mul hcoeff).mul (by simpa only [mul_assoc] using hsection)

theorem actual_mixedTerm_hasDeriv
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (q : Q F)
    (k : ℕ) (w : Word F) (s : ℂ) (hs : s ∈ V) (g : G F ζ hζ) :
    HasDerivAt (fun z => mixedJet F ζ hζ (term F ζ hζ U ι f q) k w z g)
      (mixedJet F ζ hζ (term F ζ hζ U ι f q) (k+1) w s g) s := by
  obtain ⟨O, fields, hOo, hb, hOD, hfields, hword⟩ :=
    PositiveChart.rightWord_chart_realization F ζ hζ
  let H := fun (j : ℕ) (z : ℂ) (x : KPGlobalResidualConstruction.ArchCoordinates F) =>
    mixedJet F ζ hζ (term F ζ hζ U ι f q) j [] z
      (g * KPGlobalResidualConstruction.archChart F ζ hζ x)
  have hH (j : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (H j)) (V ×ˢ O) :=
    (actual_parameterTerm_joint_right_chart_smooth F ζ hζ U ι f hf q j g).mono
      (Set.prod_mono Set.Subset.rfl hOD)
  have hd : ∀ z ∈ V, ∀ x ∈ O, HasDerivAt (fun t => H k t x) (H (k+1) z x) z := by
    intro z hz x hx
    exact actual_parameterTerm_hasDeriv F ζ hζ U ι f hf q k z hz _
  have hp := ParameterChart.word_hasDeriv V KPChamberL2Defect.chamber_isOpen
    O hOo fields hfields (H k) (H (k+1)) (hH k) (hH (k+1)) hd w s hs
    (KPGlobalResidualConstruction.archBase F) hb
  have heq (j : ℕ) (z : ℂ) (hz : z ∈ V) :
      mixedJet F ζ hζ (term F ζ hζ U ι f q) j w z g =
        RightFrame.PullbackWords.directionalWord fields w (H j z)
          (KPGlobalResidualConstruction.archBase F) := by
    have hh := hword (mixedJet F ζ hζ (term F ζ hζ U ι f q) j [] z)
      (actual_parameterTerm_right_chart_smooth F ζ hζ U ι f hf q j z hz) w g
      (KPGlobalResidualConstruction.archBase F) hb
    simpa only [KPInterface.ResidueConstruction.Raw.archChart_base, mul_one, H,
      mixedJet, rightWord, List.foldr_nil] using hh
  rw [← heq (k+1) s hs] at hp
  exact hp.congr_of_eventuallyEq (Filter.Eventually.mono
    (KPChamberL2Defect.chamber_isOpen.mem_nhds hs) (fun z hz => heq k z hz))

end ActualSource

theorem actual_term_word_parameter
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (f : ℂ → S) (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (q : Q F) (k : ℕ) (w : Word F) (s : ℂ) (hs : s ∈ V) (g : G F ζ hζ) :
    (iteratedDerivWithin k (fun z => rightWord F ζ hζ w (term F ζ hζ U ι f q z) g) V s =
      mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s g) ∧
    HasDerivAt (fun z => mixedJet F ζ hζ (term F ζ hζ U ι f q) k w z g)
      (mixedJet F ζ hζ (term F ζ hζ U ι f q) (k + 1) w s g) s := by
  have heq (j : ℕ) (z : ℂ) (hz : z ∈ V) :
      iteratedDerivWithin j (fun t => rightWord F ζ hζ w (term F ζ hζ U ι f q t) g) V z =
        mixedJet F ζ hζ (term F ζ hζ U ι f q) j w z g := by
    induction j generalizing z with
    | zero => simp only [mixedJet, iteratedDerivWithin_zero]
    | succ j ih =>
      rw [iteratedDerivWithin_succ]
      rw [derivWithin_congr (fun t ht => ih t ht) (ih z hz)]
      exact (actual_mixedTerm_hasDeriv F ζ hζ U ι f hf q j w z hz g).hasDerivWithinAt.derivWithin
        (KPChamberL2Defect.chamber_isOpen.uniqueDiffWithinAt hz)
  exact ⟨heq k s hs, actual_mixedTerm_hasDeriv F ζ hζ U ι f hf q k w s hs g⟩

end DedekindZetaZeroFree.KPContinuation.ChamberNormalTerm

end

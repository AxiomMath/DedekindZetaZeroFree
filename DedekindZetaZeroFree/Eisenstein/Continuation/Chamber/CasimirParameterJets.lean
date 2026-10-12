module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Iwasawa.LocalSmoothFrame
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.CompactKernelRepresentatives
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.NormalSeries
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestFriedrichsRealization
public import DedekindZetaZeroFree.Geometry.Hyperbolic.Laplacian.IsometryNaturality

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualChamberCasimirJets

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

abbrev V : Set ℂ := KPContActualChamberNormalSeries.V
abbrev d : ℕ := Module.finrank ℚ F / 2
abbrev level := KPContActualChamberNormalSeries.atlasLevel F ζ hζ C R P H U
abbrev M := HyperbolicChart.Space (d F)

def lambda (s : ℂ) : ℂ := KPContinuation.spectralCoordinate (d F : ℤ) s

def lambdaJet (j : ℕ) (s : ℂ) : ℂ := iteratedDerivWithin j (lambda F) V s

theorem dimension_pos (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : 0 < d F := by
  have h := KPArch.complex_places_of_primitive_twelfth_root F ζ hζ
  show 0 < Module.finrank ℚ F / 2
  rw [← h.2.1]
  exact h.2.2

theorem spectral_jets (s : ℂ) (hs : s ∈ V) :
    lambda F s = (d F : ℂ) * (1 - (1 / 3 + 2 * s) ^ 2) ∧
    lambdaJet F 0 s = lambda F s ∧
    lambdaJet F 1 s = -4 * (d F : ℂ) * (1 / 3 + 2 * s) ∧
    lambdaJet F 2 s = -8 * (d F : ℂ) ∧
    (∀ j : ℕ, 2 < j → lambdaJet F j s = 0) := by
  have hU : UniqueDiffOn ℂ V := KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
  have key : ∀ j : ℕ, iteratedDerivWithin j (lambda F) V s = iteratedDeriv j (lambda F) s := by
    intro j
    refine iteratedDerivWithin_eq_iteratedDeriv hU ?_ hs
    show ContDiffAt ℂ (j : ℕ∞) (KPContinuation.spectralCoordinate (d F : ℤ)) s
    unfold KPContinuation.spectralCoordinate
    fun_prop
  have hderiv1 : deriv (lambda F) = fun z => -4 * (d F : ℂ) * (1 / 3 + 2 * z) := by
    funext z
    change deriv (KPContinuation.spectralCoordinate (d F : ℤ)) z =
      -4 * (d F : ℂ) * (1 / 3 + 2 * z)
    rw [(KPContinuation.spectralCoordinate_hasDerivAt (d F : ℤ) z).deriv]
    simp only [Int.cast_natCast]
  have hderiv2 : deriv (fun z : ℂ => -4 * (d F : ℂ) * (1 / 3 + 2 * z)) =
      fun _ => -8 * (d F : ℂ) := by
    funext z
    have h1 : HasDerivAt (fun z : ℂ => (1 : ℂ) / 3 + 2 * z) 2 z := by
      simpa using ((hasDerivAt_id z).const_mul (2 : ℂ)).const_add ((1 : ℂ) / 3)
    have h2 : HasDerivAt (fun z : ℂ => -4 * (d F : ℂ) * (1 / 3 + 2 * z))
        (-8 * (d F : ℂ)) z := by
      have hh := h1.const_mul (-4 * (d F : ℂ))
      rw [show (-4 * (d F : ℂ)) * 2 = -8 * (d F : ℂ) by ring_nf] at hh
      exact hh
    exact h2.deriv
  have h1 : iteratedDeriv 1 (lambda F) = fun z => -4 * (d F : ℂ) * (1 / 3 + 2 * z) := by
    rw [iteratedDeriv_one]; exact hderiv1
  have h2 : iteratedDeriv 2 (lambda F) = fun _ => -8 * (d F : ℂ) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, h1]; exact hderiv2
  have h3 : iteratedDeriv 3 (lambda F) = 0 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, h2]
    funext z; simp
  have hk : ∀ j : ℕ, 3 ≤ j → iteratedDeriv j (lambda F) = 0 := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact h3
    | succ n hn ih =>
        rw [iteratedDeriv_succ, ih]
        funext z; simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show KPContinuation.spectralCoordinate (d F : ℤ) s =
      (d F : ℂ) * (1 - (1 / 3 + 2 * s) ^ 2)
    unfold KPContinuation.spectralCoordinate
    simp only [Int.cast_natCast]
  · show iteratedDerivWithin 0 (lambda F) V s = lambda F s
    simp only [key 0, iteratedDeriv_zero]
  · show iteratedDerivWithin 1 (lambda F) V s = -4 * (d F : ℂ) * (1 / 3 + 2 * s)
    simp only [key 1, h1]
  · show iteratedDerivWithin 2 (lambda F) V s = -8 * (d F : ℂ)
    simp only [key 2, h2]
  · intro j hj
    show iteratedDerivWithin j (lambda F) V s = 0
    rw [key j, hk j (by omega)]
    rfl

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (f : ℂ → S)

def jet (k : ℕ) (s : ℂ) (g : KPContActualChamberNormalSeries.G F ζ hζ) : ℂ :=
  iteratedDerivWithin k (fun z => KPContActualChamberNormalSeries.E F ζ hζ U ι f z g) V s

theorem jet_genuine (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    (fun x => jet F ζ hζ U ι f k s
      (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U x)) ∈
        KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ
          (level F ζ hζ C R P H U) := by
  obtain ⟨e, he, -, -⟩ :=
    KPContActualChamberNormalSeries.descent_series F ζ hζ C R P H U ι f hι hf
  have hval : ∀ w ∈ V, ∀ x,
      (e w).val x = KPContActualChamberNormalSeries.E F ζ hζ U ι f w
        (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U x) := by
    intro w hw x
    rw [← he w hw (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U x),
      KPContActualChamberNormalSeries.coveredRepresentative_projection]
  intro ε v
  have hB : iteratedDerivWithin k
        (fun w => KPContActualChamberNormalSeries.E F ζ hζ U ι f w
          (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
            (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v))) V s =
      iteratedDerivWithin k
        (fun w => (e w).val
          (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v)) V s :=
    ((iteratedDerivWithin_congr (fun w hw => hval w hw
      (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v))) hs).symm
  have hgen : iteratedDerivWithin k
        (fun w => (e w).val
          (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v)) V s =
      iteratedDerivWithin k
        (fun w => (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) * (e w).val v) V s :=
    (iteratedDerivWithin_congr (fun w _ => (e w).property ε v)) hs
  have hcm : iteratedDerivWithin k
        (fun w => (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) * (e w).val v) V s =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
        iteratedDerivWithin k (fun w => (e w).val v) V s :=
    iteratedDerivWithin_const_mul_field _ _
  have hA : iteratedDerivWithin k (fun w => (e w).val v) V s =
      iteratedDerivWithin k
        (fun w => KPContActualChamberNormalSeries.E F ζ hζ U ι f w
          (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U v)) V s :=
    (iteratedDerivWithin_congr (fun w hw => hval w hw v)) hs
  show jet F ζ hζ U ι f k s
      (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
        (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v)) =
    (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
      jet F ζ hζ U ι f k s
        (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U v)
  unfold jet
  rw [hB, hgen, hcm, hA]

def coveredJet (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (k : ℕ) (s : ℂ) :
    KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ (level F ζ hζ C R P H U) :=
  if hs : s ∈ V then
    ⟨_, jet_genuine F ζ hζ C R P H U ι f hι hf k s hs⟩
  else 0

def lineJet (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (k : ℕ) (s : ℂ) :=
  KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H
    (coveredJet F ζ hζ C R P H U ι f hι hf k s)

theorem coveredJet_projection (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (s : ℂ) (hs : s ∈ V) (g : KPContActualChamberNormalSeries.G F ζ hζ) :
    (coveredJet F ζ hζ C R P H U ι f hι hf k s).val
      (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ (level F ζ hζ C R P H U)
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) =
          jet F ζ hζ U ι f k s g := by
  obtain ⟨e, he, -, -⟩ :=
    KPContActualChamberNormalSeries.descent_series F ζ hζ C R P H U ι f hι hf
  have hval : ∀ w ∈ V, ∀ x,
      (e w).val x = KPContActualChamberNormalSeries.E F ζ hζ U ι f w
        (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U x) := by
    intro w hw x
    rw [← he w hw (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U x),
      KPContActualChamberNormalSeries.coveredRepresentative_projection]
  have hEq : iteratedDerivWithin k
        (fun w => KPContActualChamberNormalSeries.E F ζ hζ U ι f w
          (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
            (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ (level F ζ hζ C R P H U)
              (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)))) V s =
      iteratedDerivWithin k
        (fun w => KPContActualChamberNormalSeries.E F ζ hζ U ι f w g) V s :=
    (iteratedDerivWithin_congr (fun w hw =>
      (hval w hw (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ
        (level F ζ hζ C R P H U) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g))).symm.trans
        (he w hw g))) hs
  simp only [coveredJet, dif_pos hs]
  show jet F ζ hζ U ι f k s
      (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
        (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ (level F ζ hζ C R P H U)
          (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g))) = jet F ζ hζ U ι f k s g
  unfold jet
  rw [hEq]

namespace FrameCalculus
open RightFrame.PullbackWords
variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype B]
private theorem cauchy_identify (O : Set ℂ) (hO : IsOpen O)
    (h : ℂ → E → ℂ) (s : ℂ) (hs : s ∈ O)
    (r : ℝ) (hr : 0 < r) (hdisk : Metric.closedBall s r ⊆ O)
    (x : E) (hx : DifferentiableOn ℂ (fun z => h z x) O) (k : ℕ) :
    iteratedDerivWithin k (fun z => h z x) O s =
      (k.factorial : ℂ) * RightFrame.CauchyCoefficient.cauchyCoefficient h s r k x := by
  rw [iteratedDerivWithin_of_isOpen hO hs]
  have hi := (hx.mono hdisk).circleIntegral_one_div_sub_center_pow_smul hr k
  have hkernel : (fun z => (z-s) ^ (-((k : ℤ)+1)) * h z x) =
      (fun z => (1 / (z-s) ^ (k+1)) • h z x) := by
    funext z
    rw [show -((k : ℤ)+1) = -((k+1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
    simp only [one_div, smul_eq_mul]
  unfold RightFrame.CauchyCoefficient.cauchyCoefficient
  rw [hkernel, hi, smul_eq_mul]
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  field_simp

private theorem parameter_jet_smooth
    (U : Set E) (hU : IsOpen U) (fields : B → E → E)
    (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
    (O : Set ℂ) (hO : IsOpen O) (h : ℂ → E → ℂ)
    (hsp : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (h z) U)
    (hj : ∀ w K, IsCompact K → K ⊆ U →
      ContinuousOn (fun p : ℂ × E => directionalWord fields w (h p.1) p.2) (O ×ˢ K))
    (hhol : ∀ w x, x ∈ U →
      DifferentiableOn ℂ (fun z => directionalWord fields w (h z) x) O)
    (k : ℕ) (s : ℂ) (hs : s ∈ O) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => iteratedDerivWithin k (fun z => h z x) O s) U := by
  obtain ⟨ε,hε,hεO⟩ := Metric.isOpen_iff.mp hO s hs
  let r := ε/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hdisk : Metric.closedBall s r ⊆ O := fun z hz =>
    hεO (lt_of_le_of_lt hz (by change ε / 2 < ε; linarith))
  have hc := RightFrame.CauchyCoefficient.coefficient_smooth U hU fields hf hframe
    O hO h s r hr hdisk hsp
    (fun w K hK hKU => (hj w K hK hKU).mono (Set.prod_mono hdisk (Set.Subset.refl K)))
    (fun x hx => hhol [] x hx) k
  exact (contDiffOn_const.mul hc).congr
    (fun x hx => cauchy_identify O hO h s hs r hr hdisk x (hhol [] x hx) k)

omit [FiniteDimensional ℝ E] [Fintype B] in
private theorem word_smooth (U : Set E) (hU : IsOpen U) (fields : B → E → E)
    (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (u : E → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (w : List B) :
    ContDiffOn ℝ (⊤ : ℕ∞) (directionalWord fields w u) U := by
  induction w with
  | nil => exact hu
  | cons b w ih => exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply (hf b)
omit [FiniteDimensional ℝ E] [Fintype B] in
private theorem word_const_mul (U : Set E) (hU : IsOpen U) (fields : B → E → E)
    (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (u : E → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (c : ℂ) (w : List B) :
    ∀ x ∈ U, directionalWord fields w (fun y => c * u y) x =
      c * directionalWord fields w u x := by
  induction w with
  | nil => intro x hx; rfl
  | cons b w ih =>
    intro x hx
    change (fderiv ℝ (directionalWord fields w (fun y => c * u y)) x) (fields b x) = _
    have he : directionalWord fields w (fun y => c * u y) =ᶠ[𝓝 x]
        fun y => c * directionalWord fields w u y :=
      Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => ih y hy)
    rw [he.fderiv_eq]
    have hd := ((word_smooth U hU fields hf u hu w) x hx).contDiffAt (hU.mem_nhds hx)
    have he' : (fun y => c * directionalWord fields w u y) =
        fun y => c • directionalWord fields w u y := rfl
    rw [he', fderiv_fun_const_smul (hd.differentiableAt (by simp))]
    rfl
private theorem parameter_word_commute
    (U : Set E) (hU : IsOpen U) (fields : B → E → E)
    (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
    (O : Set ℂ) (hO : IsOpen O) (h : ℂ → E → ℂ)
    (hsp : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (h z) U)
    (hj : ∀ w K, IsCompact K → K ⊆ U →
      ContinuousOn (fun p : ℂ × E => directionalWord fields w (h p.1) p.2) (O ×ˢ K))
    (hhol : ∀ w x, x ∈ U →
      DifferentiableOn ℂ (fun z => directionalWord fields w (h z) x) O)
    (k : ℕ) (s : ℂ) (hs : s ∈ O) (w : List B) (x : E) (hx : x ∈ U) :
    directionalWord fields w (fun y => iteratedDerivWithin k (fun z => h z y) O s) x =
      iteratedDerivWithin k (fun z => directionalWord fields w (h z) x) O s := by
  obtain ⟨ε,hε,hεO⟩ := Metric.isOpen_iff.mp hO s hs
  let r := ε/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hdisk : Metric.closedBall s r ⊆ O := fun z hz =>
    hεO (lt_of_le_of_lt hz (by change ε / 2 < ε; linarith))
  have hj' := fun w K hK hKU => (hj w K hK hKU).mono (Set.prod_mono hdisk (Set.Subset.refl K))
  have hc := RightFrame.CauchyCoefficient.coefficient_smooth U hU fields hf hframe
    O hO h s r hr hdisk hsp hj' (fun x hx => hhol [] x hx) k
  have he : (fun y => iteratedDerivWithin k (fun z => h z y) O s) =ᶠ[𝓝 x]
      fun y => (k.factorial : ℂ) * RightFrame.CauchyCoefficient.cauchyCoefficient h s r k y :=
    Filter.eventually_of_mem (hU.mem_nhds hx)
      (fun y hy => cauchy_identify O hO h s hs r hr hdisk y (hhol [] y hy) k)
  have word_local {u v : E → ℂ} (heq : u =ᶠ[𝓝 x] v) :
      directionalWord fields w u x = directionalWord fields w v x := by
    have heq' : ∀ w, directionalWord fields w u =ᶠ[𝓝 x] directionalWord fields w v := by
      intro w
      induction w with
      | nil => exact heq
      | cons b w ih =>
        have hd := ih.fderiv (𝕜 := ℝ)
        filter_upwards [hd] with y hy
        change fderiv ℝ (directionalWord fields w u) y (fields b y) =
          fderiv ℝ (directionalWord fields w v) y (fields b y)
        rw [hy]
    exact (heq' w).self_of_nhds
  rw [word_local he, word_const_mul U hU fields hf _ hc _ w x hx,
    RightFrame.CauchyCoefficient.word_commute U hU fields hf hframe O hO h s r hr hdisk
      hsp hj' (fun y hy => hhol [] y hy) k w x hx]
  exact (cauchy_identify O hO (fun z => directionalWord fields w (h z)) s hs r hr hdisk
    x (hhol w x hx) k).symm

  private theorem pullback_parameter_word_commute
      {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
      (U : Set E) (hU : IsOpen U) (fields : B → E → E)
      (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
      (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
      (O : Set ℂ) (hO : IsOpen O) (h : ℂ → E → ℂ)
      (hsp : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (h z) U)
      (hj : ∀ w K, IsCompact K → K ⊆ U →
        ContinuousOn (fun p : ℂ × E => directionalWord fields w (h p.1) p.2) (O ×ˢ K))
      (hhol : ∀ w x, x ∈ U → DifferentiableOn ℂ (fun z => directionalWord fields w (h z) x) O)
      (W : Set P) (hW : IsOpen W) (ψ : P → E)
      (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ W) (hψU : Set.MapsTo ψ W U)
      (k : ℕ) (s : ℂ) (hs : s ∈ O) (w : List P) (x : P) (hx : x ∈ W) :
      constantDirectionWord w (fun y => iteratedDerivWithin k (fun z => h z (ψ y)) O s) x =
        iteratedDerivWithin k (fun z => constantDirectionWord w (h z ∘ ψ) x) O s := by
    obtain ⟨N,c,r,hc,hr,he⟩ := transport U W hU hW fields hf hframe ψ hψ hψU w
    have hjet := parameter_jet_smooth U hU fields hf hframe O hO h hsp hj hhol k s hs
    change constantDirectionWord w ((fun y => iteratedDerivWithin k (fun z => h z y) O s) ∘ ψ) x = _
    rw [he _ hjet x hx]
    have hz : Set.EqOn (fun z => constantDirectionWord w (h z ∘ ψ) x)
        (fun z => ∑ i : Fin N, c i x • directionalWord fields (r i) (h z) (ψ x)) O :=
      fun z hz => he _ (hsp z hz) x hx
    rw [iteratedDerivWithin_congr hz hs]
    have hd (i : Fin N) : ContDiffWithinAt ℂ (k : ℕ∞)
        (fun z => c i x • directionalWord fields (r i) (h z) (ψ x)) O s :=
      ((hhol (r i) (ψ x) (hψU hx)).const_smul (c i x)).contDiffOn hO |>.contDiffWithinAt hs
    rw [show iteratedDerivWithin k
        (fun z => ∑ i : Fin N, c i x • directionalWord fields (r i) (h z) (ψ x)) O s =
        ∑ i : Fin N, iteratedDerivWithin k
          (fun z => c i x • directionalWord fields (r i) (h z) (ψ x)) O s by
      simpa only [Finset.sum_fn] using iteratedDerivWithin_sum (I := Finset.univ) hs hO.uniqueDiffOn (fun i _ => hd i)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [parameter_word_commute U hU fields hf hframe O hO h hsp hj hhol k s hs (r i) (ψ x) (hψU hx)]
    exact (iteratedDerivWithin_const_smul hs hO.uniqueDiffOn _
      (((hhol (r i) (ψ x) (hψU hx)).contDiffOn hO).contDiffWithinAt hs)).symm

  private theorem pullback_word_holomorphic
      {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
      (U : Set E) (hU : IsOpen U) (fields : B → E → E)
      (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
      (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ E, ∀ b, e b = fields b x)
      (O : Set ℂ) (hO : IsOpen O) (h : ℂ → E → ℂ)
      (hsp : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (h z) U)
      (hhol : ∀ w x, x ∈ U → DifferentiableOn ℂ (fun z => directionalWord fields w (h z) x) O)
      (W : Set P) (hW : IsOpen W) (ψ : P → E)
      (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ W) (hψU : Set.MapsTo ψ W U)
      (w : List P) (x : P) (hx : x ∈ W) :
      DifferentiableOn ℂ (fun z => constantDirectionWord w (h z ∘ ψ) x) O := by
    obtain ⟨N,c,r,hc,hr,he⟩ := transport U W hU hW fields hf hframe ψ hψ hψU w
    have hd : DifferentiableOn ℂ (fun z => ∑ i : Fin N, c i x • directionalWord fields (r i) (h z) (ψ x)) O := by
      simpa only [Finset.sum_fn, Pi.smul_apply] using
        (DifferentiableOn.sum (u := Finset.univ) (fun i _ => (hhol (r i) (ψ x) (hψU hx)).const_smul (c i x)))
    exact hd.congr (fun z hz => he _ (hsp z hz) x hx)

end FrameCalculus

private theorem compact_right_pullback (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    {X : Type*} [TopologicalSpace X] (O : Set X)
    (ℓ : X → KPContActualChamberNormalSeries.G F ζ hζ) (hℓ : ContinuousOn ℓ O)
    (K : Set X) (hK : IsCompact K) (hKO : K ⊆ O)
    (w : KPContActualChamberNormalSeries.Word F) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j V ∧ ∀ z ∈ V, ∀ x : K,
      j z x = KPContActualChamberNormalSeries.rightWord F ζ hζ w
        (KPContActualChamberNormalSeries.E F ζ hζ U ι f z) (ℓ x.val) := by
  let A := ℓ '' K
  have hA : IsCompact A := hK.image_of_continuousOn (hℓ.mono hKO)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let c : C(K,A) := ⟨fun x => ⟨ℓ x.val, ⟨x.val,x.property,rfl⟩⟩,
    (continuousOn_iff_continuous_restrict.mp (hℓ.mono hKO)).subtype_mk _⟩
  let g := KPContActualChamberNormalSeries.compactMixedJet F ζ hζ U ι f hι hf 0 w A
  refine ⟨fun z => (g z).comp c,
    (ContinuousMap.compCLM ℂ ℂ c).differentiable.comp_differentiableOn
      (KPContActualChamberNormalSeries.compactMixedJet_holomorphic F ζ hζ U ι f hι hf 0 w A hA), ?_⟩
  intro z hz x
  simp [g, c, KPContActualChamberNormalSeries.compactMixedJet, hz,
    KPContActualChamberNormalSeries.mixedJet]
  rfl

open scoped Manifold in
private theorem actualTerm_smooth (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (r : KPContActualChamberNormalSeries.Q F) (s : ℂ) (hs : s ∈ V) :
    KPMsGreenFlux.Smooth F ζ hζ (KPContActualChamberNormalSeries.term F ζ hζ U ι f r s) := by
  refine ⟨?_, ?_⟩
  · simpa only [KPContActualChamberNormalSeries.mixedJet, KPContActualChamberNormalSeries.rightWord,
      List.foldr_nil, iteratedDerivWithin_zero] using
      (KPContinuation.ChamberNormalTerm.actual_term_mixed_flow F ζ hζ U ι f hι hf r 0 [] s hs).1
  intro g
  obtain ⟨C, hC⟩ := KPSmoothActualFlowData.actual_archimedean_lie_data F
  letI := C
  obtain ⟨L, D, hD, hbasis, _⟩ := hC
  letI := L
  let q := fun (w : KPContActualChamberNormalSeries.Word F) (a : KPSmoothActualFlowData.GInfinity F) =>
    KPContActualChamberNormalSeries.mixedJet F ζ hζ (KPContActualChamberNormalSeries.term F ζ hζ U ι f r) 0 w s
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a)
  have hflow (b : KPSmoothActualFlowData.B F) (t : ℝ) :
      D.exponential (t • D.basis b) = KPSmoothActualFlowData.flow F b t := by
    rw [hD]
    congr 1
    funext c
    simp only [Pi.smul_apply, hbasis, smul_eq_mul]
    split_ifs <;> simp
  have hder (w : KPContActualChamberNormalSeries.Word F) (b : KPSmoothActualFlowData.B F) (a : KPSmoothActualFlowData.GInfinity F) :
      HasDerivAt (fun t : ℝ => q w (a * D.exponential (t • D.basis b))) (q (b :: w) a) 0 := by
    have hh := (KPContinuation.ChamberNormalTerm.actual_term_mixed_flow F ζ hζ U ι f hι hf r 0 w s hs).2 b
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a)
    have heq (t : ℝ) : q w (a * D.exponential (t • D.basis b)) =
        KPContActualChamberNormalSeries.mixedJet F ζ hζ (KPContActualChamberNormalSeries.term F ζ hζ U ι f r) 0 w s
          ((g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) *
            KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t)) := by
      dsimp [q]
      rw [hflow, (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1, ← mul_assoc]
    exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall heq)
  have hq (n : ℕ) : ∀ w, ContMDiff 𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F) 𝓘(ℝ, ℂ) n (q w) := by
    induction n with
    | zero =>
      intro w
      apply contMDiff_zero_iff.mpr
      exact ((KPContinuation.ChamberNormalTerm.actual_term_mixed_flow F ζ hζ U ι f hι hf r 0 w s hs).1).comp
        (show Continuous (fun a : KPSmoothActualFlowData.GInfinity F =>
          g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) from
          continuous_const.mul (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1)
    | succ n ih =>
      intro w
      exact SmoothWordOrbit.DomainToSmooth.contMDiff_succ_of_translated_basis_derivatives
        D.basis D.exponential D.exponential_zero D.exponential_add_ray D.exponential_smooth
        D.exponentialChart D.zero_mem_source D.chart_eq_exponential n (q w) (fun b => q (b::w))
        (((KPContinuation.ChamberNormalTerm.actual_term_mixed_flow F ζ hζ U ι f hι hf r 0 w s hs).1).comp
          (continuous_const.mul (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1))
        (fun b => ih (b::w)) (hder w)
  have htop : ContMDiff 𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (q []) :=
    contMDiff_infty.mpr (fun n => hq n [])
  have he : ContMDiff 𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F)
      𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F) (⊤ : ℕ∞) (KPSmoothActualFlowData.exponential F) :=
    hD ▸ D.exponential_smooth
  exact (htop.comp he).contDiff

private theorem group_chart_analytic (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (O : Set (KPSmoothActualFlowData.B F → ℝ))
    (ℓ : (KPSmoothActualFlowData.B F → ℝ) → KPContActualChamberNormalSeries.G F ζ hζ)
    (fields : KPSmoothActualFlowData.B F → (KPSmoothActualFlowData.B F → ℝ) → (KPSmoothActualFlowData.B F → ℝ))
    (hℓ : ContinuousOn ℓ O)
    (hpull : ∀ u, KPMsGreenFlux.Smooth F ζ hζ u →
      ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ ℓ) O ∧ ∀ w x, x ∈ O →
        KPContActualChamberNormalSeries.rightWord F ζ hζ w u (ℓ x) =
          RightFrame.PullbackWords.directionalWord fields w (u ∘ ℓ) x) :
    let h := fun z x => KPContActualChamberNormalSeries.E F ζ hζ U ι f z (ℓ x)
    (∀ z ∈ V, ContDiffOn ℝ (⊤ : ℕ∞) (h z) O) ∧
    (∀ w K, IsCompact K → K ⊆ O → ContinuousOn
      (fun p => RightFrame.PullbackWords.directionalWord fields w (h p.1) p.2) (V ×ˢ K)) ∧
    (∀ w x, x ∈ O → DifferentiableOn ℂ
      (fun z => RightFrame.PullbackWords.directionalWord fields w (h z) x) V) := by
  let h := fun z x => KPContActualChamberNormalSeries.E F ζ hζ U ι f z (ℓ x)
  have hsp : ∀ z ∈ V, ContDiffOn ℝ (⊤ : ℕ∞) (h z) O := fun z hz =>
    (hpull _ (KPContActualChamberNormalSeries.smooth F ζ hζ U ι f hι hf z hz)).1
  have hj : ∀ w K, IsCompact K → K ⊆ O →
      ContinuousOn (fun p => RightFrame.PullbackWords.directionalWord fields w (h p.1) p.2) (V ×ˢ K) := by
    intro w K hK hKO
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    obtain ⟨j,hj,heq⟩ := compact_right_pullback F ζ hζ U ι f hι hf O ℓ hℓ K hK hKO w
    have hcont : ContinuousOn (fun p : ℂ × K => j p.1 p.2) (V ×ˢ Set.univ) :=
      continuous_eval.comp_continuousOn ((hj.continuousOn.comp continuous_fst.continuousOn
        (fun _ hp => hp.1)).prodMk continuous_snd.continuousOn)
    apply continuousOn_iff_continuous_restrict.mpr
    let a : (V ×ˢ K) → ℂ × K := fun p => (p.val.1, ⟨p.val.2,p.property.2⟩)
    have ha : Continuous a := (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    refine (hcont.comp_continuous ha (fun p => ⟨p.property.1, Set.mem_univ _⟩)).congr ?_
    intro p
    dsimp only [Function.comp_def, a, Set.domRestrict]
    rw [heq p.val.1 p.property.1 ⟨p.val.2,p.property.2⟩]
    exact (hpull _ (KPContActualChamberNormalSeries.smooth F ζ hζ U ι f hι hf
      p.val.1 p.property.1)).2 w p.val.2 (hKO p.property.2)
  have hhol : ∀ w x, x ∈ O → DifferentiableOn ℂ
      (fun z => RightFrame.PullbackWords.directionalWord fields w (h z) x) V := by
    intro w x hx
    let K := ({x} : Set (KPSmoothActualFlowData.B F → ℝ))
    letI : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_singleton
    obtain ⟨j,hj,heq⟩ := compact_right_pullback F ζ hζ U ι f hι hf O ℓ hℓ K
      isCompact_singleton (Set.singleton_subset_iff.mpr hx) w
    refine ((ContinuousMap.evalCLM ℂ (⟨x,Set.mem_singleton x⟩ : K)).differentiable.comp_differentiableOn hj).congr ?_
    intro z hz
    change RightFrame.PullbackWords.directionalWord fields w (h z) x = j z ⟨x,Set.mem_singleton x⟩
    rw [heq z hz]
    exact ((hpull _ (KPContActualChamberNormalSeries.smooth F ζ hζ U ι f hι hf z hz)).2 w x hx).symm
  exact ⟨hsp,hj,hhol⟩

private theorem iwasawa_jet_smooth_from_geometry (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (c : KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ)
    (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (z₀ : KPContSectorCoveredQuotientVocabulary.SymmetricSpace F)
    (O : Set (KPSmoothActualFlowData.B F → ℝ))
    (W : Set (KPContSectorCoveredQuotientVocabulary.SymmetricSpace F))
    (ℓ : (KPSmoothActualFlowData.B F → ℝ) → KPContActualChamberNormalSeries.G F ζ hζ)
    (ψ : KPContSectorCoveredQuotientVocabulary.SymmetricSpace F → (KPSmoothActualFlowData.B F → ℝ))
    (fields : KPSmoothActualFlowData.B F → (KPSmoothActualFlowData.B F → ℝ) → (KPSmoothActualFlowData.B F → ℝ))
    (hO : IsOpen O) (hW : IsOpen W) (hz₀ : z₀ ∈ W)
    (hℓ : ContinuousOn ℓ O) (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ W) (hψO : Set.MapsTo ψ W O)
    (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) O)
    (hframe : ∀ x ∈ O, ∃ e : Module.Basis (KPSmoothActualFlowData.B F) ℝ
      (KPSmoothActualFlowData.B F → ℝ), ∀ b, e b = fields b x)
    (hrec : ∀ z ∈ W, ℓ (ψ z) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ z) * c.val)
    (hpull : ∀ u, KPMsGreenFlux.Smooth F ζ hζ u →
      ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ ℓ) O ∧ ∀ w x, x ∈ O →
        KPContActualChamberNormalSeries.rightWord F ζ hζ w u (ℓ x) =
          RightFrame.PullbackWords.directionalWord fields w (u ∘ ℓ) x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => jet F ζ hζ U ι f k s
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ z) * c.val)) z₀ := by
  let h := fun z x => KPContActualChamberNormalSeries.E F ζ hζ U ι f z (ℓ x)
  have hsp : ∀ z ∈ V, ContDiffOn ℝ (⊤ : ℕ∞) (h z) O := fun z hz =>
    (hpull _ (KPContActualChamberNormalSeries.smooth F ζ hζ U ι f hι hf z hz)).1
  have hj : ∀ w K, IsCompact K → K ⊆ O →
      ContinuousOn (fun p => RightFrame.PullbackWords.directionalWord fields w (h p.1) p.2) (V ×ˢ K) := by
    intro w K hK hKO
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    obtain ⟨j,hj,heq⟩ := compact_right_pullback F ζ hζ U ι f hι hf O ℓ hℓ K hK hKO w
    have hcont : ContinuousOn (fun p : ℂ × K => j p.1 p.2) (V ×ˢ Set.univ) :=
      continuous_eval.comp_continuousOn ((hj.continuousOn.comp continuous_fst.continuousOn
        (fun _ hp => hp.1)).prodMk continuous_snd.continuousOn)
    apply continuousOn_iff_continuous_restrict.mpr
    let a : (V ×ˢ K) → ℂ × K := fun p => (p.val.1, ⟨p.val.2,p.property.2⟩)
    have ha : Continuous a := (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    refine (hcont.comp_continuous ha (fun p => ⟨p.property.1, Set.mem_univ _⟩)).congr ?_
    intro p
    dsimp only [Function.comp_def, a, Set.domRestrict]
    rw [heq p.val.1 p.property.1 ⟨p.val.2,p.property.2⟩]
    exact (hpull _ (KPContActualChamberNormalSeries.smooth F ζ hζ U ι f hι hf
      p.val.1 p.property.1)).2 w p.val.2 (hKO p.property.2)
  have hhol : ∀ w x, x ∈ O → DifferentiableOn ℂ
      (fun z => RightFrame.PullbackWords.directionalWord fields w (h z) x) V := by
    intro w x hx
    let K := ({x} : Set (KPSmoothActualFlowData.B F → ℝ))
    letI : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_singleton
    obtain ⟨j,hj,heq⟩ := compact_right_pullback F ζ hζ U ι f hι hf O ℓ hℓ K
      isCompact_singleton (Set.singleton_subset_iff.mpr hx) w
    refine ((ContinuousMap.evalCLM ℂ (⟨x,Set.mem_singleton x⟩ : K)).differentiable.comp_differentiableOn hj).congr ?_
    intro z hz
    change RightFrame.PullbackWords.directionalWord fields w (h z) x = j z ⟨x,Set.mem_singleton x⟩
    rw [heq z hz]
    exact ((hpull _ (KPContActualChamberNormalSeries.smooth F ζ hζ U ι f hι hf z hz)).2 w x hx).symm
  have hjet := FrameCalculus.parameter_jet_smooth O hO fields hfields hframe V
    KPChamberL2Defect.chamber_isOpen h hsp hj hhol k s hs
  have hcomp := hjet.comp hψ hψO
  apply (hcomp.contDiffAt (hW.mem_nhds hz₀)).congr_of_eventuallyEq
  filter_upwards [hW.mem_nhds hz₀] with z hz
  simp only [Function.comp_def, h, jet]
  rw [hrec z hz]

private theorem line_jet_smooth_from_iwasawa (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (hsmooth : ∀ c : KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ,
      ContDiff ℝ (⊤ : ℕ∞) (fun z => jet F ζ hζ U ι f k s
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ z) * c.val))) :
    KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ (level F ζ hζ C R P H U)
      R P H (lineJet F ζ hζ C R P H U ι f hι hf k s) := by
  intro i
  have he : (fun z => (lineJet F ζ hζ C R P H U ι f hι hf k s i).val z) =
      fun z => jet F ζ hζ U ι f k s
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ z) *
            ((H.atlas (level F ζ hζ C R P H U)).representative i).val) := by
    funext z
    rw [← coveredJet_projection F ζ hζ C R P H U ι f hι hf k s hs]
    rw [KPContSectorQuotientRelationsComparison.piTilde_quotientMap,
      KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection]
    exact KPContSectorScalarLineAlgebra.S_apply F ζ hζ (level F ζ hζ C R P H U) R P H _ i z
  change ContDiff ℝ (⊤ : ℕ∞) (fun z => (lineJet F ζ hζ C R P H U ι f hι hf k s i).val z)
  rw [he]
  exact hsmooth _

theorem lineJet_smooth (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ (level F ζ hζ C R P H U)
      R P H (lineJet F ζ hζ C R P H U ι f hι hf k s) := by
  apply line_jet_smooth_from_iwasawa F ζ hζ C R P H U ι f hι hf k s hs
  intro c
  apply contDiff_iff_contDiffAt.mpr
  intro z₀
  obtain ⟨O, W, ℓ, ψ, fields, hO, hW, hz₀, hℓ, hψ, hψO, hfields, hframe, hrec, hpull⟩ :=
    KPContinuation.ChamberJetGeometry.local_iwasawa_frame F ζ hζ c z₀
  exact iwasawa_jet_smooth_from_geometry F ζ hζ U ι f hι hf c k s hs z₀
    O W ℓ ψ fields hO hW hz₀ hℓ hψ hψO hfields hframe hrec hpull

abbrev Frame (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount) :=
  KPContCotangentActualOverlap.LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := level F ζ hζ C R P H U) (R := R) (P := P) (H := H) i

def frameJet (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (k : ℕ) (s : ℂ)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (x : M F) : ℂ :=
  a.coefficient (lineJet F ζ hζ C R P H U ι f hι hf k s) x

namespace FlatCalculation

open KPContFlatCuspCasimirSpecialization
 def meanCLM (d : ℕ) : KPArch.Space d →L[ℝ] ℝ :=
  (d : ℝ)⁻¹ • ∑ k : Fin d, (ContinuousLinearMap.snd ℝ ℂ ℝ).comp (ContinuousLinearMap.proj k)
private theorem meanCLM_apply (d : ℕ) (z : KPArch.Space d) :
    meanCLM d z = KPCuspLogShape.meanHeight d z := by
  simp [meanCLM, KPCuspLogShape.meanHeight, div_eq_inv_mul]
private theorem meanCLM_dir (d : ℕ) (i : Fin d) (j : Fin 3) :
    meanCLM d (coordinateDirection d i j) = if j = 2 then (d : ℝ)⁻¹ else 0 := by
  simp only [meanCLM, ContinuousLinearMap.smul_apply, sum_apply, ContinuousLinearMap.comp_apply]
  rw [Finset.sum_eq_single i]
  · simp [coordinateDirection, Pi.single_eq_same]
    fin_cases j <;> norm_num
  · intro k _ hk
    simp [coordinateDirection, Pi.single_eq_of_ne hk]
  · simp
private theorem exp_mean_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (d : ℕ) (c : ℂ) (b : V) (z w : KPArch.Space d) :
    fderiv ℝ (fun y => Complex.exp (c * (meanCLM d y : ℂ)) • b) z w =
      (c * (meanCLM d w : ℂ) * Complex.exp (c * (meanCLM d z : ℂ))) • b := by
  have hm := (Complex.ofRealCLM.comp (meanCLM d)).hasFDerivAt (x := z)
  have he := (hm.const_smul c).cexp.smul_const b
  have he' : HasFDerivAt (fun y => Complex.exp (c * (meanCLM d y : ℂ)) • b)
      ((Complex.exp (c * (meanCLM d z : ℂ)) • c • (Complex.ofRealCLM.comp (meanCLM d))).smulRight b) z := by
    simpa [ContinuousLinearMap.comp_apply, smul_eq_mul] using he
  rw [he'.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  congr 1
  ring
private theorem exp_mean_second {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (d : ℕ) (c : ℂ) (b : V) (z w : KPArch.Space d) :
    fderiv ℝ (fun y => fderiv ℝ (fun x => Complex.exp (c * (meanCLM d x : ℂ)) • b) y w) z w =
      ((c * (meanCLM d w : ℂ)) ^ 2 * Complex.exp (c * (meanCLM d z : ℂ))) • b := by
  have hfun : (fun y => fderiv ℝ (fun x => Complex.exp (c * (meanCLM d x : ℂ)) • b) y w) =
      fun y => Complex.exp (c * (meanCLM d y : ℂ)) • ((c * (meanCLM d w : ℂ)) • b) := by
    funext y
    rw [exp_mean_fderiv]
    simp only [smul_smul]
    congr 1
    ring
  rw [hfun, exp_mean_fderiv, smul_smul]
  congr 1
  ring
private theorem exp_mean_laplacian {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (d : ℕ) (hd : 0 < d) (s : ℂ) (b : V) (z : KPArch.Space d) :
    Δloc d (fun y => KPIncomingCasimir.heightFactor d s (KPCuspLogShape.meanHeight d y) • b) z =
      KPContinuation.spectralCoordinate (d : ℤ) s •
        (KPIncomingCasimir.heightFactor d s (KPCuspLogShape.meanHeight d z) • b) := by
  have hf : ContDiff ℝ 2 (fun y : KPArch.Space d =>
      KPIncomingCasimir.heightFactor d s (KPCuspLogShape.meanHeight d y) • b) := by
    simp only [KPIncomingCasimir.heightFactor, ← meanCLM_apply]
    apply ContDiff.smul_const
    have hm : ContDiff ℝ 2 (fun y => (meanCLM d y : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (meanCLM d).contDiff
    exact ((contDiff_const.mul hm).cexp)
  rw [Δloc_coordinate_expression d _ hf]
  simp only [KPIncomingCasimir.heightFactor, ← meanCLM_apply]
  simp only [exp_mean_second]
  simp only [exp_mean_fderiv, meanCLM_dir]
  simp only [ite_true, show ¬ ((0 : Fin 3) = 2) from by decide,
    show ¬ ((1 : Fin 3) = 2) from by decide, ite_false,
    Complex.ofReal_zero, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), zero_smul,
    add_zero, sub_zero]
  simp only [smul_zero, sub_zero, ← neg_smul, smul_smul, ← add_smul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
  simp only [smul_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  congr 1
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  simp only [KPContinuation.spectralCoordinate, Int.cast_natCast]
  field_simp
  ring

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)

private theorem flat_height_formula (s : ℂ) (v : S)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (x : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPContActualSphericalFlatStage.L F ζ hζ U ι s v
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ x) * c.val) =
    KPIncomingCasimir.heightFactor (KPCuspLogShape.dimension F) s
      (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) x) *
        KPContActualSphericalFlatStage.L F ζ hζ U ι s v c.val := by
  rw [KPContinuation.ChamberFlatCasimir.iwasawa_insertion]
  let v₀ := (KPContActualSphericalFlatStage.Stage F ζ hζ U).subtype (ι v)
  change (KPContFlatSourceRecipe.flatR F ζ hζ s v₀).val
    ((KPGlobalTorusFunctionData.N F ζ hζ _ * _) * c.val) = _
  rw [mul_assoc]
  have hn := (KPContFlatSourceRecipe.flatR F ζ hζ s v₀).property 1
    (KPContinuation.ChamberFlatCasimir.horizontalAdele F ζ hζ x, 0)
    ((KPContFlatArchDiagonalMultiplier.aInfinity F ζ hζ
      (KPContinuation.ChamberFlatCasimir.heights F ζ hζ x)).val * c.val)
  have hn' : (KPContFlatSourceRecipe.flatR F ζ hζ s v₀).val
      (KPGlobalTorusFunctionData.N F ζ hζ
        (KPContinuation.ChamberFlatCasimir.horizontalAdele F ζ hζ x, 0) *
        ((KPContFlatArchDiagonalMultiplier.aInfinity F ζ hζ
          (KPContinuation.ChamberFlatCasimir.heights F ζ hζ x)).val * c.val)) =
      (KPContFlatSourceRecipe.flatR F ζ hζ s v₀).val
        ((KPContFlatArchDiagonalMultiplier.aInfinity F ζ hζ
          (KPContinuation.ChamberFlatCasimir.heights F ζ hζ x)).val * c.val) := by
    simpa [KPGlobalTorusFunctionData.deltaHalf] using hn
  rw [hn', KPContFlatArchDiagonalMultiplier.flatR_covariance]
  change Complex.exp ((4 / 3 + 2 * s) *
    ((∑ w, KPContinuation.ChamberFlatCasimir.heights F ζ hζ x w : ℝ) : ℂ)) *
    _ = _
  congr 1
  have he := (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ).sum_comp
    (fun i => (x i).2)
  unfold KPContinuation.ChamberFlatCasimir.heights
  rw [he, KPIncomingCasimir.heightFactor, KPCuspLogShape.meanHeight]
  have hnz : (KPCuspLogShape.dimension F : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (KPCuspLogShape.dimension_pos F
      (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).1))
  congr 1
  push_cast
  field_simp

end FlatCalculation

theorem flat_casimir (s : ℂ) (hs : s ∈ V) (v : S)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
      (fun x => KPContActualSphericalFlatStage.L F ζ hζ U ι s v
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ x) * c.val)) z =
    lambda F s * KPContActualSphericalFlatStage.L F ζ hζ U ι s v
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ z) * c.val) := by
  have hfun : (fun x : KPArch.Space (KPCuspLogShape.dimension F) =>
      KPContActualSphericalFlatStage.L F ζ hζ U ι s v
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ x) * c.val)) =
      fun x => KPIncomingCasimir.heightFactor (KPCuspLogShape.dimension F) s
        (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) x) •
          KPContActualSphericalFlatStage.L F ζ hζ U ι s v c.val := by
    funext x
    exact FlatCalculation.flat_height_formula F ζ hζ U ι s v c x
  rw [hfun]
  have hΔ := FlatCalculation.exp_mean_laplacian (KPCuspLogShape.dimension F)
    (KPCuspLogShape.dimension_pos F
      (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).1) s
    (KPContActualSphericalFlatStage.L F ζ hζ U ι s v c.val) z
  change KPContFlatCuspCasimirSpecialization.Δloc _ _ _ = _
  rw [hΔ, FlatCalculation.flat_height_formula F ζ hζ U ι s v c z]
  have hd : d F = KPCuspLogShape.dimension F :=
    KPContFlatArchDiagonalMultiplier.complexDimension_eq F ζ hζ
  simp only [smul_eq_mul, lambda, hd]

private theorem frameJet_eq (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (k : ℕ) (s : ℂ) (hs : s ∈ V)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (x : M F) :
    frameJet F ζ hζ C R P H U ι f hι hf k s a x =
      (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x) : ℂ) *
        jet F ζ hζ U ι f k s
          (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
            (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
              (level F ζ hζ C R P H U))
              (a.kind.representative • KPContCotangentActualOverlap.labeledA a.places x,
                (H.atlas (level F ζ hζ C R P H U)).representative i))) := by
  simp only [frameJet, lineJet, KPContCotangentActualOverlap.LiftedChart.coefficient,
    KPContSectorScalarLineAlgebra.S_apply, coveredJet, dif_pos hs]

theorem frameJet_eq_derivative (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (s : ℂ) (hs : s ∈ V)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (x : M F) (hx : x ∈ a.omega) :
    iteratedDerivWithin k
      (fun z => frameJet F ζ hζ C R P H U ι f hι hf 0 z a x) V s =
        frameJet F ζ hζ C R P H U ι f hι hf k s a x := by
  have heq : Set.EqOn (fun z => frameJet F ζ hζ C R P H U ι f hι hf 0 z a x)
      (fun z => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x) : ℂ) *
        jet F ζ hζ U ι f 0 z
          (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
            (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
              (level F ζ hζ C R P H U))
              (a.kind.representative • KPContCotangentActualOverlap.labeledA a.places x,
                (H.atlas (level F ζ hζ C R P H U)).representative i)))) V :=
    fun z hz => frameJet_eq F ζ hζ C R P H U ι f hι hf 0 z hz a x
  have heq2 : Set.EqOn (fun z => jet F ζ hζ U ι f 0 z
        (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
          (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
            (level F ζ hζ C R P H U))
            (a.kind.representative • KPContCotangentActualOverlap.labeledA a.places x,
              (H.atlas (level F ζ hζ C R P H U)).representative i))))
      (fun z => KPContActualChamberNormalSeries.E F ζ hζ U ι f z
        (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
          (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
            (level F ζ hζ C R P H U))
            (a.kind.representative • KPContCotangentActualOverlap.labeledA a.places x,
              (H.atlas (level F ζ hζ C R P H U)).representative i)))) V :=
    fun z _ => by simp only [jet, iteratedDerivWithin_zero]
  rw [(iteratedDerivWithin_congr heq) hs, iteratedDerivWithin_const_mul_field,
    frameJet_eq F ζ hζ C R P H U ι f hι hf k s hs a x, (iteratedDerivWithin_congr heq2) hs]
  rfl

def coordinateWord (w : List (Fin (d F) × Fin 3)) (u : M F → ℂ) : M F → ℂ :=
  w.foldr (fun b v => HyperbolicChart.coordinateDerivative (d F) b.1 b.2 v) u

def spatialOperator (J : Finset (List (Fin (d F) × Fin 3)))
    (c : List (Fin (d F) × Fin 3) → M F → ℂ) (u : M F → ℂ) (x : M F) : ℂ :=
  ∑ w ∈ J, c w x * coordinateWord F w u x

 def frameGroup {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (x : M F) : KPContActualChamberNormalSeries.G F ζ hζ :=
  KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ
      (a.kind.representative • KPContCotangentActualOverlap.labeledA a.places x)) *
        (H.atlas (level F ζ hζ C R P H U)).representative i
private theorem frameGroup_projection {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (x : M F) :
    KPContSectorQuotientRelationsComparison.piTilde F ζ hζ (level F ζ hζ C R P H U)
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (frameGroup F ζ hζ C R P H U a x)) =
    Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ (level F ζ hζ C R P H U))
      (a.kind.representative • KPContCotangentActualOverlap.labeledA a.places x,
        (H.atlas (level F ζ hζ C R P H U)).representative i) := by
  unfold frameGroup
  rw [KPContSectorQuotientRelationsComparison.piTilde_quotientMap]
  rw [KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection]
private theorem frameJet_literal (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (k : ℕ) (s : ℂ) (hs : s ∈ V)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (x : M F) :
    frameJet F ζ hζ C R P H U ι f hι hf k s a x =
      (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x) : ℂ) *
        jet F ζ hζ U ι f k s (frameGroup F ζ hζ C R P H U a x) := by
  rw [← coveredJet_projection F ζ hζ C R P H U ι f hι hf k s hs,
    frameGroup_projection]
  simp [frameJet, lineJet, KPContCotangentActualOverlap.LiftedChart.coefficient,
    KPContSectorScalarLineAlgebra.S_apply]

private theorem E_holo (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (g : KPContActualChamberNormalSeries.G F ζ hζ) :
    DifferentiableOn ℂ (fun s => KPContActualChamberNormalSeries.E F ζ hζ U ι f s g) V := by
  let A : Set (KPContActualChamberNormalSeries.G F ζ hζ) := {g}
  letI : CompactSpace A := isCompact_iff_compactSpace.mp isCompact_singleton
  have hh := KPContActualChamberNormalSeries.compactMixedJet_holomorphic F ζ hζ U ι f hι hf 0 [] A isCompact_singleton
  have hd := (ContinuousMap.evalCLM ℂ (⟨g,Set.mem_singleton g⟩ : A)).differentiable.comp_differentiableOn hh
  apply hd.congr
  intro s hs
  simp [KPContActualChamberNormalSeries.compactMixedJet, hs,
    KPContActualChamberNormalSeries.mixedJet, KPContActualChamberNormalSeries.rightWord]
private theorem frame_holo (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (x : M F) (hx : x ∈ a.omega) :
    DifferentiableOn ℂ (fun s => frameJet F ζ hζ C R P H U ι f hι hf 0 s a x) V := by
  let g := KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
    (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ (level F ζ hζ C R P H U))
      (a.kind.representative • KPContCotangentActualOverlap.labeledA a.places x,
        (H.atlas (level F ζ hζ C R P H U)).representative i))
  have hh := (E_holo F ζ hζ U ι f hι hf g).const_mul
    (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x) : ℂ)
  apply hh.congr
  intro s hs

  simp [frameJet, lineJet, KPContCotangentActualOverlap.LiftedChart.coefficient,
    KPContSectorScalarLineAlgebra.S_apply, coveredJet, hs, jet, g]
private theorem coordinateWord_eq (w : List (Fin (d F) × Fin 3)) (u : M F → ℂ) :
    coordinateWord F w u = RightFrame.PullbackWords.constantDirectionWord
      (w.map (fun b => HyperbolicChart.coordinateVector (d F) b.1 b.2)) u := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change (fun x => fderiv ℝ (coordinateWord F w u) x (HyperbolicChart.coordinateVector (d F) b.1 b.2)) =
      (fun x => fderiv ℝ (RightFrame.PullbackWords.constantDirectionWord
        (w.map (fun b => HyperbolicChart.coordinateVector (d F) b.1 b.2)) u) x
          (HyperbolicChart.coordinateVector (d F) b.1 b.2))
    rw [ih]

private theorem coordinateWord_local (w : List (Fin (d F) × Fin 3))
    {u v : M F → ℂ} {x : M F} (he : u =ᶠ[𝓝 x] v) :
    coordinateWord F w u x = coordinateWord F w v x := by
  have hh : ∀ w, coordinateWord F w u =ᶠ[𝓝 x] coordinateWord F w v := by
    intro w
    induction w with
    | nil => exact he
    | cons b w ih =>
      have hd := ih.fderiv (𝕜 := ℝ)
      filter_upwards [hd] with y hy
      change fderiv ℝ (coordinateWord F w u) y _ = fderiv ℝ (coordinateWord F w v) y _
      rw [hy]
  exact (hh w).self_of_nhds

private theorem rationalLift_eq_matrixRationalHom (γ : KPCuspArithmetic.PGL2 F) :
    KPMsClearedTruncationL2.rationalLift F ζ hζ γ =
      KPContFlatRationalCosetCovariance.matrixRationalHom F ζ hζ γ := by
  induction γ using Matrix.ProjGenLinGroup.induction_on with
  | mk m =>
    simp only [KPContFlatRationalCosetCovariance.matrixRationalHom,
      MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv_mk,
      KPRationalAdelicSplitting.rationalPGLHom_mk, KPMsClearedTruncationL2.rationalLift_mk]
    rfl

private theorem arch_comm_finite (r : KPSmoothActualFlowData.GInfinity F)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ r) c.val := by
  apply RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ r
    ⟨c.val, RepresentationTheory.ArchFiniteSplitting.arch_kernel_le_finite F ζ hζ ?_⟩
  have hc := c.property
  rw [MonoidHom.mem_ker] at hc ⊢
  obtain ⟨d, hd⟩ := QuotientGroup.mk'_surjective
    (KPAdelicCoverRestrictedProduct.splitScalarSubgroup F ζ hζ) c.val
  rw [← hd] at hc ⊢
  funext w
  have hw := congrFun hc w
  change Matrix.ProjGenLinGroup.mk
    (KPAdelicCoverRestrictedProduct.matrixEval F (Sum.inl w)
      (KPAdelicCoverRestrictedProduct.projection F ζ hζ d)) = 1 at hw
  have hh := congrArg
    (Matrix.ProjGenLinGroup.map
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom) hw
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map
    ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
        (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w)))
      (KPAdelicCoverRestrictedProduct.projection F ζ hζ d)) = 1
  simpa only [Matrix.ProjGenLinGroup.map_mk, map_one,
    Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply,
    KPAdelicCoverRestrictedProduct.matrixEval] using hh

open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability in
set_option maxHeartbeats 1600000 in
private theorem flat_fiber_formula (s : ℂ) (v : S) (hs : s ∈ V)
    (g : KPSmoothActualFlowData.GInfinity F) (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    KPContActualSphericalFlatStage.L F ζ hζ U ι s v
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ g * c.val) =
    KPContActualSphericalFlatStage.L F ζ hζ U ι s v
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ
          (KPMsFixedHaarDisintegration.archBasepoint F g)) * c.val) := by
  have hz := KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection F ζ hζ
    (KPMsFixedHaarDisintegration.archBasepoint F g)
  obtain ⟨k,hk⟩ := (KPContSectorArchSphericalFibers.archBasepoint_eq_iff F _ g).mp hz
  conv_lhs => rw [hk, (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  have hc := arch_comm_finite F ζ hζ k.val c
  rw [mul_assoc, hc.eq, ← mul_assoc]
  have hsΩ : s ∈ KPContinuation.spectralDomain := by
    change -(1 : ℝ)/6 < s.re
    change (1 : ℝ)/3 < s.re at hs
    linarith
  exact (KPContActualSphericalFlatStage.covariance F ζ hζ U ι s hsΩ).2.1 v _ k

set_option maxHeartbeats 1600000 in
private theorem term_arch_formula (s : ℂ) (hs : s ∈ V)
    (q : KPContActualChamberNormalSeries.Q F) (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    ∃ c' : KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      ∀ z : KPArch.Space (KPCuspLogShape.dimension F),
      KPContActualChamberNormalSeries.term F ζ hζ U ι f q s
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ z) * c.val) =
      KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s)
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ ((Quotient.out q) • z)) * c'.val) := by
  let σ : KPCuspArithmetic.PGL2 F := Quotient.out q
  obtain ⟨b,hb⟩ := KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.rationalLift_split F ζ hζ σ
  refine ⟨b*c,?_⟩
  intro z
  unfold KPContActualChamberNormalSeries.term KPContActualChamberNormalSeries.lift
  rw [← rationalLift_eq_matrixRationalHom F ζ hζ σ,hb]
  have hc := arch_comm_finite F ζ hζ (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ z) b
  rw [mul_assoc, ← mul_assoc b.val, ← hc.eq, ← mul_assoc, ← mul_assoc,
    ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  rw [mul_assoc]
  change KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s)
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.archRational σ *
        KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ z) * (b*c).val) = _
  rw [flat_fiber_formula F ζ hζ U ι s (f s) hs]
  rw [KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.archBasepoint_mul,
    KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection,
    KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.archRational_action σ z]
  rfl

private theorem frame_expansion
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (w : List (Fin (d F) × Fin 3))
    (x : M F) (hx : x ∈ a.omega) :
    ∃ N : ℕ, ∃ c : Fin N → ℂ, ∃ r : Fin N → KPContActualChamberNormalSeries.Word F,
      (∀ j, (r j).length ≤ w.length) ∧
      ∀ u : KPContActualChamberNormalSeries.G F ζ hζ → ℂ, KPMsGreenFlux.Smooth F ζ hζ u →
        coordinateWord F w (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ) *
          u (frameGroup F ζ hζ C R P H U a y)) x =
          ∑ j : Fin N, c j * KPContActualChamberNormalSeries.rightWord F ζ hζ (r j) u
            (frameGroup F ζ hζ C R P H U a x) := by
  let Lmap : M F → KPContSectorCoveredQuotientVocabulary.SymmetricSpace F :=
    fun y => a.kind.representative • KPContCotangentActualOverlap.labeledA a.places y
  have hA : ContDiff ℝ (⊤ : ℕ∞) (KPContCotangentActualOverlap.labeledA a.places) := by
    apply contDiff_pi.mpr
    intro j
    exact (contDiff_apply ℝ _ (a.places.symm j)).comp (CotangentLogCoframe.A (d F)).contDiff
  have hLmap : ContDiff ℝ (⊤ : ℕ∞) Lmap :=
    (CoreChartLocalizers.CutoffConstruction.StabilizerLinearization.rational_action_contDiff
      F a.kind.representative).comp hA
  obtain ⟨O,W,ℓ,ψ,fields,hO,hW,hxW,hℓ,hψ,hψO,hfields,hframe,hrec,hpull⟩ :=
    KPContinuation.ChamberJetGeometry.local_iwasawa_frame F ζ hζ
      ((H.atlas (level F ζ hζ C R P H U)).representative i) (Lmap x)
  let D : Set (M F) := a.omega ∩ Lmap ⁻¹' W
  have hD : IsOpen D := a.isOpen_omega.inter (hW.preimage hLmap.continuous)
  have hxD : x ∈ D := ⟨hx,hxW⟩
  let Ψ : M F → (KPSmoothActualFlowData.B F → ℝ) := ψ ∘ Lmap
  have hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ D := hψ.comp hLmap.contDiffOn (fun y hy => hy.2)
  have hΨO : Set.MapsTo Ψ D O := fun y hy => hψO hy.2
  let c₀ : ℂ := (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x) : ℂ)
  have hphase : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ)) =ᶠ[𝓝 x] (fun _ => c₀) := by
    have he := a.splitting_locallyConstant.comp (fun ε => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ))
    have hh := he.eventually_eq (⟨x,hx⟩ : a.omega)
    have hw : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ)) =ᶠ[𝓝[a.omega] x] (fun _ => c₀) := by
      rw [nhdsWithin_eq_map_subtype_coe hx]
      exact hh
    rwa [a.isOpen_omega.nhdsWithin_eq hx] at hw
  let w' := w.map (fun b => HyperbolicChart.coordinateVector (d F) b.1 b.2)
  obtain ⟨N,c,r,hc,hr,he⟩ := RightFrame.PullbackWords.transport O D hO hD fields hfields hframe Ψ hΨ hΨO w'
  refine ⟨N,fun j => c₀ * (c j x : ℂ),r,fun j => by simpa [w'] using hr j,?_⟩
  intro u hu
  have hlocal : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ) *
      u (frameGroup F ζ hζ C R P H U a y)) =ᶠ[𝓝 x] (fun y => c₀ * u (ℓ (Ψ y))) := by
    filter_upwards [hD.mem_nhds hxD,hphase] with y hy hp
    rw [hp]
    dsimp only [Ψ,Function.comp_def]
    rw [hrec (Lmap y) hy.2]
    rfl
  rw [coordinateWord_local F w hlocal, coordinateWord_eq]
  change RightFrame.PullbackWords.directionalWord (fun (v : M F) (_ : M F) => v) w'
    (fun y => c₀ * ((u ∘ ℓ) ∘ Ψ) y) x = _
  rw [FrameCalculus.word_const_mul D hD (fun (v : M F) (_ : M F) => v)
    (fun _ => contDiffOn_const) _ ((hpull u hu).1.comp hΨ hΨO) c₀ w' x hxD]
  change c₀ * RightFrame.PullbackWords.constantDirectionWord w' ((u ∘ ℓ) ∘ Ψ) x = _
  rw [he _ (hpull u hu).1 x hxD, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← (hpull u hu).2 (r j) (Ψ x) (hΨO hxD)]
  have hrex : ℓ (Ψ x) = frameGroup F ζ hζ C R P H U a x := hrec (Lmap x) hxW
  rw [hrex]
  simp only [smul_eq_mul, Complex.real_smul]
  ring

private theorem coordinateWord_frame_tsum (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (s : ℂ) (hs : s ∈ V)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (w : List (Fin (d F) × Fin 3))
    (x : M F) (hx : x ∈ a.omega) :
    coordinateWord F w (frameJet F ζ hζ C R P H U ι f hι hf 0 s a) x =
      ∑' q : KPContActualChamberNormalSeries.Q F, coordinateWord F w
        (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ) *
          KPContActualChamberNormalSeries.term F ζ hζ U ι f q s
            (frameGroup F ζ hζ C R P H U a y)) x := by
  have hfun : frameJet F ζ hζ C R P H U ι f hι hf 0 s a =
      fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ) *
        KPContActualChamberNormalSeries.E F ζ hζ U ι f s (frameGroup F ζ hζ C R P H U a y) := by
    funext y
    simpa only [jet,iteratedDerivWithin_zero] using frameJet_literal F ζ hζ C R P H U ι f hι hf 0 s hs a y
  obtain ⟨N,c,r,hr,he⟩ := frame_expansion F ζ hζ C R P H U a w x hx
  rw [hfun, he _ (KPContActualChamberNormalSeries.smooth F ζ hζ U ι f hι hf s hs)]
  simp_rw [he _ (actualTerm_smooth F ζ hζ U ι f hι hf _ s hs)]
  have hj (j : Fin N) : Summable (fun q => c j * KPContActualChamberNormalSeries.rightWord F ζ hζ (r j)
      (KPContActualChamberNormalSeries.term F ζ hζ U ι f q s) (frameGroup F ζ hζ C R P H U a x)) := by
    have hh := (KPContActualChamberNormalSeries.mixed_summable F ζ hζ U ι f hι hf 0 (r j) s hs
      (frameGroup F ζ hζ C R P H U a x)).of_norm
    simpa only [KPContActualChamberNormalSeries.mixedJet,iteratedDerivWithin_zero] using hh.mul_left (c j)
  rw [Summable.tsum_finsetSum (s := Finset.univ) (fun j _ => hj j)]
  apply Finset.sum_congr rfl
  intro j hjmem
  rw [tsum_mul_left]
  congr 1
  simpa only [KPContActualChamberNormalSeries.mixedJet,iteratedDerivWithin_zero] using
    KPContActualChamberNormalSeries.mixedJet_eq_tsum F ζ hζ U ι f hι hf 0 (r j) s hs
      (frameGroup F ζ hζ C R P H U a x)

private theorem frameWord_data (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (w : List (Fin (d F) × Fin 3))
    (x : M F) (hx : x ∈ a.omega) :
    DifferentiableOn ℂ (fun z => coordinateWord F w (frameJet F ζ hζ C R P H U ι f hι hf 0 z a) x) V ∧
    ∀ k s, s ∈ V → coordinateWord F w (frameJet F ζ hζ C R P H U ι f hι hf k s a) x =
      iteratedDerivWithin k
        (fun z => coordinateWord F w (frameJet F ζ hζ C R P H U ι f hι hf 0 z a) x) V s := by
  let Lmap : M F → KPContSectorCoveredQuotientVocabulary.SymmetricSpace F :=
    fun y => a.kind.representative • KPContCotangentActualOverlap.labeledA a.places y
  have hA : ContDiff ℝ (⊤ : ℕ∞) (KPContCotangentActualOverlap.labeledA a.places) := by
    apply contDiff_pi.mpr
    intro j
    exact (contDiff_apply ℝ _ (a.places.symm j)).comp (CotangentLogCoframe.A (d F)).contDiff
  have hLmap : ContDiff ℝ (⊤ : ℕ∞) Lmap :=
    (CoreChartLocalizers.CutoffConstruction.StabilizerLinearization.rational_action_contDiff
      F a.kind.representative).comp hA
  obtain ⟨O,W,ℓ,ψ,fields,hO,hW,hxW,hℓ,hψ,hψO,hfields,hframe,hrec,hpull⟩ :=
    KPContinuation.ChamberJetGeometry.local_iwasawa_frame F ζ hζ
      ((H.atlas (level F ζ hζ C R P H U)).representative i) (Lmap x)
  let D : Set (M F) := a.omega ∩ Lmap ⁻¹' W
  have hD : IsOpen D := a.isOpen_omega.inter (hW.preimage hLmap.continuous)
  have hxD : x ∈ D := ⟨hx,hxW⟩
  let Ψ : M F → (KPSmoothActualFlowData.B F → ℝ) := ψ ∘ Lmap
  have hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ D := hψ.comp hLmap.contDiffOn (fun y hy => hy.2)
  have hΨO : Set.MapsTo Ψ D O := fun y hy => hψO hy.2
  let h := fun z y => KPContActualChamberNormalSeries.E F ζ hζ U ι f z (ℓ y)
  obtain ⟨hsp,hj,hhol⟩ := group_chart_analytic F ζ hζ U ι f hι hf O ℓ fields hℓ hpull
  let c : ℂ := (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x) : ℂ)
  have hphase : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ)) =ᶠ[𝓝 x] (fun _ => c) := by
    have he := a.splitting_locallyConstant.comp (fun ε => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ))
    have hh := he.eventually_eq (⟨x,hx⟩ : a.omega)
    have hw : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ)) =ᶠ[𝓝[a.omega] x] (fun _ => c) := by
      rw [nhdsWithin_eq_map_subtype_coe hx]
      exact hh
    rwa [a.isOpen_omega.nhdsWithin_eq hx] at hw
  have he (k : ℕ) (s : ℂ) (hs : s ∈ V) :
      frameJet F ζ hζ C R P H U ι f hι hf k s a =ᶠ[𝓝 x]
        (fun y => c * iteratedDerivWithin k (fun z => h z (Ψ y)) V s) := by
    filter_upwards [hD.mem_nhds hxD,hphase] with y hy hp
    rw [frameJet_literal F ζ hζ C R P H U ι f hι hf k s hs a y, hp]
    simp only [jet,h,Ψ,Function.comp_def]
    rw [hrec (Lmap y) hy.2]
    rfl
  let w' := w.map (fun b => HyperbolicChart.coordinateVector (d F) b.1 b.2)
  have hw (k : ℕ) (s : ℂ) (hs : s ∈ V) :
      coordinateWord F w (frameJet F ζ hζ C R P H U ι f hι hf k s a) x =
        c * RightFrame.PullbackWords.constantDirectionWord w'
          (fun y => iteratedDerivWithin k (fun z => h z (Ψ y)) V s) x := by
    rw [coordinateWord_local F w (he k s hs), coordinateWord_eq]
    exact FrameCalculus.word_const_mul D hD (fun (v : M F) (_ : M F) => v)
      (fun _ => contDiffOn_const) _
      ((FrameCalculus.parameter_jet_smooth O hO fields hfields hframe V
        KPChamberL2Defect.chamber_isOpen h hsp hj hhol k s hs).comp hΨ hΨO) c w' x hxD
  have hg := FrameCalculus.pullback_word_holomorphic O hO fields hfields hframe V
    KPChamberL2Defect.chamber_isOpen h hsp hhol D hD Ψ hΨ hΨO w' x hxD
  refine ⟨(hg.const_mul c).congr (fun z hz => by simpa only [iteratedDerivWithin_zero, Function.comp_def] using hw 0 z hz), ?_⟩
  intro k s hs
  rw [hw k s hs, FrameCalculus.pullback_parameter_word_commute O hO fields hfields hframe V
    KPChamberL2Defect.chamber_isOpen h hsp hj hhol D hD Ψ hΨ hΨO k s hs w' x hxD]
  have he0 : Set.EqOn
      (fun z => coordinateWord F w (frameJet F ζ hζ C R P H U ι f hι hf 0 z a) x)
      (fun z => c * RightFrame.PullbackWords.constantDirectionWord w' (h z ∘ Ψ) x) V :=
    fun z hz => by simpa only [iteratedDerivWithin_zero, Function.comp_def] using hw 0 z hz
  rw [iteratedDerivWithin_congr he0 hs, iteratedDerivWithin_const_mul_field]

theorem spatial_commute (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (s : ℂ) (hs : s ∈ V)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i)
    (J : Finset (List (Fin (d F) × Fin 3)))
    (c : List (Fin (d F) × Fin 3) → M F → ℂ)
    (hc : ∀ w ∈ J, ContDiffOn ℝ (⊤ : ℕ∞) (c w) a.omega)
    (x : M F) (hx : x ∈ a.omega) :
    iteratedDerivWithin k
      (fun z => spatialOperator F J c (frameJet F ζ hζ C R P H U ι f hι hf 0 z a) x) V s =
    spatialOperator F J c (frameJet F ζ hζ C R P H U ι f hι hf k s a) x := by
  unfold spatialOperator
  have hd : ∀ w ∈ J, ContDiffWithinAt ℂ (k : ℕ∞)
      (fun z => c w x * coordinateWord F w (frameJet F ζ hζ C R P H U ι f hι hf 0 z a) x) V s := by
    intro w hw
    exact (((frameWord_data F ζ hζ C R P H U ι f hι hf a w x hx).1.const_mul (c w x)).contDiffOn
      KPChamberL2Defect.chamber_isOpen).contDiffWithinAt hs
  rw [show iteratedDerivWithin k
      (fun z => ∑ w ∈ J, c w x * coordinateWord F w (frameJet F ζ hζ C R P H U ι f hι hf 0 z a) x) V s =
      ∑ w ∈ J, iteratedDerivWithin k
        (fun z => c w x * coordinateWord F w (frameJet F ζ hζ C R P H U ι f hι hf 0 z a) x) V s by
    simpa only [Finset.sum_fn] using iteratedDerivWithin_sum hs
      KPChamberL2Defect.chamber_isOpen.uniqueDiffOn hd]
  apply Finset.sum_congr rfl
  intro w hw
  rw [iteratedDerivWithin_const_mul_field,
    ← (frameWord_data F ζ hζ C R P H U ι f hι hf a w x hx).2 k s hs]

 def lapWords (d : ℕ) : Finset (List (Fin d × Fin 3)) :=
  Finset.univ.biUnion (fun i => {[(i,2),(i,2)], [(i,2)], [(i,0),(i,0)], [(i,1),(i,1)]})
 def lapCoeff (d : ℕ) (w : List (Fin d × Fin 3)) (x : HyperbolicChart.Space d) : ℂ :=
  ∑ i : Fin d, ((if w = [(i,2),(i,2)] then -1 else 0) +
    (if w = [(i,2)] then 2 else 0) +
    (if w = [(i,0),(i,0)] then -(Real.exp (2 * x (i,2)) : ℂ) else 0) +
    (if w = [(i,1),(i,1)] then -(Real.exp (2 * x (i,2)) : ℂ) else 0))
private theorem lapCoeff_smooth (w : List (Fin (d F) × Fin 3)) : ContDiff ℝ (⊤ : ℕ∞) (lapCoeff (d F) w) := by
  unfold lapCoeff
  apply ContDiff.sum; intro i hi
  have hr : ContDiff ℝ (⊤ : ℕ∞) (fun x : M F => Real.exp (2 * x (i,2))) := by fun_prop
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun x : M F => (Real.exp (2 * x (i,2)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr
  split_ifs <;> fun_prop (disch := assumption)
private theorem lapOperator (u : M F → ℂ) (x : M F) :
    spatialOperator F (lapWords (d F)) (lapCoeff (d F)) u x = HyperbolicChart.laplacian (d F) u x := by
  have hm (i : Fin (d F)) (k : Fin 3) : [(i,k),(i,k)] ∈ lapWords (d F) := by
    fin_cases k <;> simp [lapWords]
  have hs (i : Fin (d F)) : [(i,2)] ∈ lapWords (d F) := by simp [lapWords]
  simp only [spatialOperator, lapCoeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', hm, hs, if_true, neg_one_mul, neg_mul,
    coordinateWord, List.foldr_cons, List.foldr_nil, HyperbolicChart.laplacian]
  ring
private theorem rational_pullback (γ : KPCuspArithmetic.PGL2 F)
    (u : KPArch.Space (KPCuspLogShape.dimension F) → ℂ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
      (fun y => u (γ • y)) z =
      KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F) u (γ • z) := by
  obtain ⟨B,hB⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  have he : (fun y : KPArch.Space (KPCuspLogShape.dimension F) => γ • y) =
      KPArch.productAction (KPCuspLogShape.dimension F)
        (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding B) := by
    funext y
    rw [← hB]
    exact KPCuspSiegel.action_mk F B y
  simp_rw [show ∀ y, γ • y = KPArch.productAction (KPCuspLogShape.dimension F)
    (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding B) y from
      fun y => congrFun he y]
  exact KPContArchLaplacianNaturality.pullback _ _ _ hu z

private theorem flat_arch_smooth (s : ℂ) (v : S) (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => KPContActualSphericalFlatStage.L F ζ hζ U ι s v
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ z) * c.val)) := by
  have he := funext (FlatCalculation.flat_height_formula F ζ hζ U ι s v c)
  rw [he]
  simp only [KPIncomingCasimir.heightFactor, ← FlatCalculation.meanCLM_apply]
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun y => (FlatCalculation.meanCLM (KPCuspLogShape.dimension F) y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (FlatCalculation.meanCLM _).contDiff
  exact (contDiff_const.mul hm).cexp.mul contDiff_const

private theorem term_arch_casimir (s : ℂ) (hs : s ∈ V)
    (q : KPContActualChamberNormalSeries.Q F) (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
      (fun y => KPContActualChamberNormalSeries.term F ζ hζ U ι f q s
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ y) * c.val)) z =
    lambda F s * KPContActualChamberNormalSeries.term F ζ hζ U ι f q s
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ z) * c.val) := by
  obtain ⟨c',he⟩ := term_arch_formula F ζ hζ U ι f s hs q c
  simp_rw [he]
  rw [rational_pullback F (Quotient.out q) _ (flat_arch_smooth F ζ hζ U ι s (f s) c') z]
  exact flat_casimir F ζ hζ U ι s hs (f s) c' _

private theorem term_frame_casimir (s : ℂ) (hs : s ∈ V)
    (q : KPContActualChamberNormalSeries.Q F)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (x : M F) (hx : x ∈ a.omega) :
    HyperbolicChart.laplacian (d F)
      (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ) *
        KPContActualChamberNormalSeries.term F ζ hζ U ι f q s (frameGroup F ζ hζ C R P H U a y)) x =
    lambda F s * ((KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x) : ℂ) *
      KPContActualChamberNormalSeries.term F ζ hζ U ι f q s (frameGroup F ζ hζ C R P H U a x)) := by
  let u : KPArch.Space (KPCuspLogShape.dimension F) → ℂ := fun z =>
    KPContActualChamberNormalSeries.term F ζ hζ U ι f q s
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ z) *
          (H.atlas (level F ζ hζ C R P H U)).representative i)
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    obtain ⟨c',he⟩ := term_arch_formula F ζ hζ U ι f s hs q ((H.atlas (level F ζ hζ C R P H U)).representative i)
    change ContDiff ℝ (⊤ : ℕ∞) (fun z => _)
    simp_rw [he]
    exact (flat_arch_smooth F ζ hζ U ι s (f s) c').comp
      (CoreChartLocalizers.CutoffConstruction.StabilizerLinearization.rational_action_contDiff F (Quotient.out q))
  let v : KPArch.Space (KPCuspLogShape.dimension F) → ℂ := fun z => u (a.kind.representative • z)
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := hu.comp
    (CoreChartLocalizers.CutoffConstruction.StabilizerLinearization.rational_action_contDiff F a.kind.representative)
  let c₀ := (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x) : ℂ)
  have hp : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ)) =ᶠ[𝓝 x] (fun _ => c₀) := by
    have he := (a.splitting_locallyConstant.comp (fun ε => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ))).eventually_eq (⟨x,hx⟩ : a.omega)
    have hw : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ)) =ᶠ[𝓝[a.omega] x] (fun _ => c₀) := by
      rw [nhdsWithin_eq_map_subtype_coe hx]; exact he
    rwa [a.isOpen_omega.nhdsWithin_eq hx] at hw
  have he : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ) *
        KPContActualChamberNormalSeries.term F ζ hζ U ι f q s (frameGroup F ζ hζ C R P H U a y)) =ᶠ[𝓝 x]
      (fun y => c₀ * v (KPContCotangentActualOverlap.labeledA a.places y)) := by
    filter_upwards [hp] with y hy
    rw [hy]; rfl
  rw [← lapOperator]
  unfold spatialOperator
  simp_rw [coordinateWord_local F _ he]
  change spatialOperator F (lapWords (d F)) (lapCoeff (d F))
    (fun y => c₀ * v (KPContCotangentActualOverlap.labeledA a.places y)) x = _
  rw [lapOperator]
  have hb := KPContArchLaplacianCoordinateBridge.bridge_equiv (d F) (KPCuspLogShape.dimension F) a.places
    (fun y => c₀ * v y) (contDiff_const.mul hv) x
  change KPContActualSphericalFlatStage.localLaplacian _ (fun y => c₀ * v y)
    (KPContCotangentActualOverlap.labeledA a.places x) =
    HyperbolicChart.laplacian _ (fun y => c₀ * v (KPContCotangentActualOverlap.labeledA a.places y)) x at hb
  rw [← hb, KPContArchLaplacianNaturality.localLaplacian_const_mul _ _ hv,
    rational_pullback F a.kind.representative u hu,
    term_arch_casimir F ζ hζ U ι f s hs q]
  change c₀ * (lambda F s * u (a.kind.representative • KPContCotangentActualOverlap.labeledA a.places x)) = _
  dsimp [c₀,u,frameGroup]
  ring

private theorem coordinateWord_term_summable (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (s : ℂ) (hs : s ∈ V)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (w : List (Fin (d F) × Fin 3))
    (x : M F) (hx : x ∈ a.omega) :
    Summable (fun q : KPContActualChamberNormalSeries.Q F => coordinateWord F w
      (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ) *
        KPContActualChamberNormalSeries.term F ζ hζ U ι f q s (frameGroup F ζ hζ C R P H U a y)) x) := by
  obtain ⟨N,c,r,hr,he⟩ := frame_expansion F ζ hζ C R P H U a w x hx
  simp_rw [he _ (actualTerm_smooth F ζ hζ U ι f hι hf _ s hs)]
  apply summable_sum
  intro j hj
  have hh := (KPContActualChamberNormalSeries.mixed_summable F ζ hζ U ι f hι hf 0 (r j) s hs
    (frameGroup F ζ hζ C R P H U a x)).of_norm
  simpa only [KPContActualChamberNormalSeries.mixedJet,iteratedDerivWithin_zero] using hh.mul_left (c j)

theorem casimir (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (s : ℂ) (hs : s ∈ V)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (x : M F) (hx : x ∈ a.omega) :
    HyperbolicChart.laplacian (d F)
      (frameJet F ζ hζ C R P H U ι f hι hf 0 s a) x =
    lambda F s * frameJet F ζ hζ C R P H U ι f hι hf 0 s a x := by
  rw [← lapOperator]
  unfold spatialOperator
  simp_rw [coordinateWord_frame_tsum F ζ hζ C R P H U ι f hι hf s hs a _ x hx, ← tsum_mul_left]
  have hj : ∀ w ∈ lapWords (d F), Summable (fun q : KPContActualChamberNormalSeries.Q F =>
      lapCoeff (d F) w x * coordinateWord F w
        (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ) *
          KPContActualChamberNormalSeries.term F ζ hζ U ι f q s (frameGroup F ζ hζ C R P H U a y)) x) := by
    intro w hw
    exact (coordinateWord_term_summable F ζ hζ C R P H U ι f hι hf s hs a w x hx).mul_left _
  rw [← Summable.tsum_finsetSum hj]
  conv_lhs => arg 1; ext q; change spatialOperator F (lapWords (d F)) (lapCoeff (d F)) _ x
  simp_rw [lapOperator, term_frame_casimir F ζ hζ C R P H U ι f s hs _ a x hx]
  rw [tsum_mul_left, tsum_mul_left]
  rw [frameJet_literal F ζ hζ C R P H U ι f hι hf 0 s hs a x]
  simp only [jet,iteratedDerivWithin_zero, KPContActualChamberNormalSeries.E]

private theorem laplacian_commute (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (s : ℂ) (hs : s ∈ V)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (x : M F) (hx : x ∈ a.omega) :
    iteratedDerivWithin k
      (fun z => HyperbolicChart.laplacian (d F) (frameJet F ζ hζ C R P H U ι f hι hf 0 z a) x) V s =
    HyperbolicChart.laplacian (d F) (frameJet F ζ hζ C R P H U ι f hι hf k s a) x := by
  simp_rw [← lapOperator F]
  exact spatial_commute F ζ hζ C R P H U ι f hι hf k s hs a _ _
    (fun w hw => (lapCoeff_smooth F w).contDiffOn) x hx

theorem casimir_jets (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (s : ℂ) (hs : s ∈ V)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (x : M F) (hx : x ∈ a.omega) :
    HyperbolicChart.laplacian (d F)
      (frameJet F ζ hζ C R P H U ι f hι hf k s a) x =
    lambda F s * frameJet F ζ hζ C R P H U ι f hι hf k s a x +
      ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) * lambdaJet F j s *
        frameJet F ζ hζ C R P H U ι f hι hf (k - j) s a x := by
  have hV : UniqueDiffOn ℂ V := KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
  rw [← laplacian_commute F ζ hζ C R P H U ι f hι hf k s hs a x hx]
  have he : Set.EqOn
      (fun z => HyperbolicChart.laplacian (d F) (frameJet F ζ hζ C R P H U ι f hι hf 0 z a) x)
      (fun z => lambda F z * frameJet F ζ hζ C R P H U ι f hι hf 0 z a x) V :=
    fun z hz => casimir F ζ hζ C R P H U ι f hι hf z hz a x hx
  rw [(iteratedDerivWithin_congr he) hs]
  have hl : ContDiffWithinAt ℂ k (lambda F) V s := by
    unfold lambda KPContinuation.spectralCoordinate; fun_prop
  have ht : ContDiffWithinAt ℂ k (fun z => frameJet F ζ hζ C R P H U ι f hι hf 0 z a x) V s :=
    ((frame_holo F ζ hζ C R P H U ι f hι hf a x hx).contDiffOn KPChamberL2Defect.chamber_isOpen).contDiffWithinAt hs
  rw [show iteratedDerivWithin k (fun z => lambda F z * frameJet F ζ hζ C R P H U ι f hι hf 0 z a x) V s =
      ∑ j ∈ Finset.range (k+1), (Nat.choose k j : ℂ) * iteratedDerivWithin j (lambda F) V s *
        iteratedDerivWithin (k-j) (fun z => frameJet F ζ hζ C R P H U ι f hι hf 0 z a x) V s by
    exact iteratedDerivWithin_mul hs hV hl ht]
  simp_rw [frameJet_eq_derivative F ζ hζ C R P H U ι f hι hf _ s hs a x hx]
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.sub_zero, iteratedDerivWithin_zero, Nat.cast_one, one_mul]
  rw [add_comm]
  apply congrArg (fun z => lambda F s * frameJet F ζ hζ C R P H U ι f hι hf k s a x + z)
  have hb (j : ℕ) : iteratedDerivWithin j (lambda F) V s = lambdaJet F j s := rfl
  simp_rw [hb]
  let T := fun j => (Nat.choose k j : ℂ) * lambdaJet F j s *
    frameJet F ζ hζ C R P H U ι f hι hf (k-j) s a x
  change (∑ j ∈ Finset.range k, T (j+1)) = ∑ j ∈ Finset.Icc 1 (min k 2), T j
  have hshift : (∑ j ∈ Finset.range k, T (j+1)) = ∑ j ∈ Finset.Icc 1 k, T j := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  rw [hshift]
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    exact ⟨hj.1, hj.2.trans (min_le_left _ _)⟩
  · intro j hj hn
    have hlarge : 2 < j := by
      simp only [Finset.mem_Icc] at hj hn
      omega
    dsimp [T]
    rw [(spectral_jets F s hs).2.2.2.2 j hlarge]
    simp

theorem rightWord_commute (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (w : KPContActualChamberNormalSeries.Word F) (s : ℂ) (hs : s ∈ V)
    (g : KPContActualChamberNormalSeries.G F ζ hζ) :
    iteratedDerivWithin k
      (fun z => KPContActualChamberNormalSeries.rightWord F ζ hζ w
        (KPContActualChamberNormalSeries.E F ζ hζ U ι f z) g) V s =
      KPContActualChamberNormalSeries.rightWord F ζ hζ w (jet F ζ hζ U ι f k s) g := by
  show iteratedDerivWithin k
      (fun z => KPContActualChamberNormalSeries.rightWord F ζ hζ w
        (KPContActualChamberNormalSeries.E F ζ hζ U ι f z) g) V s =
    KPContActualChamberNormalSeries.rightWord F ζ hζ w
      (fun g' => iteratedDerivWithin k
        (fun z => KPContActualChamberNormalSeries.E F ζ hζ U ι f z g') V s) g
  exact KPContActualChamberNormalSeries.mixedJet_commute F ζ hζ U ι f hι hf k w s hs g

abbrev Cusps := KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U

def cuspSheet (a : Cusps F ζ hζ C R P H U) (k : ℕ) (s : ℂ)
    (t : ℝ) (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F)
    (ε : rootsOfUnity 3 F) : ℂ :=
  jet F ζ hζ U ι f k s
    (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a t x b ε)

theorem cusp_restriction_commute (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (a : Cusps F ζ hζ C R P H U) (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (t : ℝ) (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F)
    (ε : rootsOfUnity 3 F) :
    iteratedDerivWithin k (fun z => cuspSheet F ζ hζ C R P H U ι f a 0 z t x b ε) V s =
      cuspSheet F ζ hζ C R P H U ι f a k s t x b ε := by
  simp only [cuspSheet, jet, iteratedDerivWithin_zero]

def cuspProjection (a : Cusps F ζ hζ C R P H U)
    (μ : Measure (KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a))
    (k : ℕ) (s : ℂ) (t : ℝ) (b : KPCuspCharts.Shape F) :
    KPContFlatCuspIncomingEvaluation.ZeroFiber F ζ hζ C R P H U a :=
  KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a
    (fun ε => ∫ z : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a,
      cuspSheet F ζ hζ C R P H U ι f a k s t (Quotient.out z) b ε ∂μ)

namespace CuspAnalytic
set_option maxHeartbeats 1200000
open KPContFlatCuspIncomingEvaluation
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (hι : Function.Injective ι) (f : ℂ → S)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable (a : Cusps F ζ hζ C R P H U) (s : ℂ) (hs : s ∈ KPContActualChamberNormalSeries.V)

 theorem scalar_cusp_frame
    (e : KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ
      (atlasLevel F ζ hζ C R P H U))
    (z : KPArch.Space (KPCuspLogShape.dimension F)) (ε : rootsOfUnity 3 F) :
    (KPContSectorScalarLineAlgebra.J F ζ hζ (atlasLevel F ζ hζ C R P H U) e).val
      (z, finiteRepresentative F ζ hζ C R P H U a ε) =
    (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      (KPContSectorScalarLineAlgebra.S F ζ hζ (atlasLevel F ζ hζ C R P H U)
        R P H e a.1).val ((sigma F ζ hζ C R P H U a) • z) := by
  let j := KPContSectorScalarLineAlgebra.J F ζ hζ (atlasLevel F ζ hζ C R P H U) e
  have hr := j.property.1 z (finiteRepresentative F ζ hζ C R P H U a ε)
    (sigma F ζ hζ C R P H U a)
  have hc : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ
      (sigma F ζ hζ C R P H U a) * finiteRepresentative F ζ hζ C R P H U a ε =
      KPCuspGenuineMonodromy.central F ζ hζ ε * (atlas F ζ hζ C R P H U).representative a.1 := by
    have hcomm : ∀ c : KPCuspGenuineMonodromy.FiniteCover F ζ hζ,
        c * KPCuspGenuineMonodromy.central F ζ hζ ε =
          KPCuspGenuineMonodromy.central F ζ hζ ε * c := by
      intro c
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp
        (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
          (show (KPCuspGenuineMonodromy.central F ζ hζ ε :
            KPCuspGenuineMonodromy.Cover F ζ hζ) ∈
            (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ).range from ⟨ε, rfl⟩)) c
    rw [finiteRepresentative, ← mul_assoc, ← mul_assoc, hcomm]
    simp only [map_inv, mul_assoc, mul_inv_cancel_left]
  rw [hc, j.property.2.1] at hr
  rw [KPContSectorScalarLineAlgebra.S_apply]
  exact hr.symm

include hι hf hs in
private theorem sheet_frame
    (e : KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ
      (atlasLevel F ζ hζ C R P H U))
    (he : ∀ g, e.val (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ
      (atlasLevel F ζ hζ C R P H U) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) =
      KPContActualChamberNormalSeries.E F ζ hζ U ι f s g)
    (t : ℝ) (p : KPCuspCharts.Cross F) (ε : rootsOfUnity 3 F) :
    KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t p.1 p.2 ε =
    (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      (KPContSectorScalarLineAlgebra.S F ζ hζ (atlasLevel F ζ hζ C R P H U)
        R P H e a.1).val ((sigma F ζ hζ C R P H U a) • KPCuspCharts.toArch F (p,t)) := by
  simp only [KPContActualChamberCasimirJets.cuspSheet, KPContActualChamberCasimirJets.jet,
    iteratedDerivWithin_zero, cuspGroup]
  rw [(KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s hs).1, ← he]
  rw [localGroup, KPContSectorScalarLineAlgebra.group_lift_formula,
    KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection]
  exact scalar_cusp_frame F ζ hζ C R P H U a e _ ε

include hι hf hs

private theorem actualCuspSheet_crossAction
    (h : stabilizer F ζ hζ C R P H U a) (t : ℝ)
    (p : KPCuspCharts.Cross F) (ε : rootsOfUnity 3 F) :
    KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t
      ((geometry F ζ hζ C R P H U a).crossAction h p).1
      ((geometry F ζ hζ C R P H U a).crossAction h p).2 ε =
    (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a h) : ℂ) *
      KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t p.1 p.2 ε := by
  obtain ⟨e, he, _, _⟩ := KPContActualChamberNormalSeries.descent_series F ζ hζ C R P H U ι f hι hf
  rw [sheet_frame F ζ hζ C R P H U ι hι f hf a s hs (e s) (he s hs),
    sheet_frame F ζ hζ C R P H U ι hι f hf a s hs (e s) (he s hs)]
  obtain ⟨A, hA, hc⟩ := (parabolic F ζ hζ C R P H U a).upper h h.property
  have hact : (h : KPCuspArithmetic.PGL2 F) • KPCuspCharts.toArch F (p,t) =
      KPCuspCharts.toArch F ((geometry F ζ hζ C R P H U a).crossAction h p,t) := by
    change KPCuspSiegel.action F _ _ = _
    rw [(geometry F ζ hζ C R P H U a).actual_action h A hA hc,
      (geometry F ζ hζ C R P H U a).crossAction_formula h A hA hc]
    rfl
  rw [← hact]
  let γ := KPCuspGenuineMonodromy.cuspInclusion F (component F ζ hζ C R P H U a)
    (((atlas F ζ hζ C R P H U).cuspAtlas a.1).cusp a.2) (sigma F ζ hζ C R P H U a) h
  have heq : (sigma F ζ hζ C R P H U a) • ((h : KPCuspArithmetic.PGL2 F) •
      KPCuspCharts.toArch F (p,t)) = (γ : KPCuspArithmetic.PGL2 F) •
      ((sigma F ζ hζ C R P H U a) • KPCuspCharts.toArch F (p,t)) := by
    simp only [γ, KPCuspGenuineMonodromy.cuspInclusion_formula, mul_smul, inv_smul_smul]
  rw [heq, KPContSectorScalarLineAlgebra.S_equivariance]
  change _ = (KPCuspGenuineMonodromy.chi F ζ hζ
    (((atlas F ζ hζ C R P H U).line a.1).rho γ) : ℂ) * _
  change (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
    ((KPCuspGenuineMonodromy.chi F ζ hζ (((atlas F ζ hζ C R P H U).line a.1).rho γ) : ℂ) * _) = _
  ring

private theorem actualCuspSheet_translation
    (l : (parabolic F ζ hζ C R P H U a).L) (t : ℝ)
    (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t
      (x + KPCuspCharts.embedding F l.val) b ε =
    (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a
      ((parabolic F ζ hζ C R P H U a).inclusion (Multiplicative.ofAdd l))) : ℂ) *
      KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t x b ε := by
  let D := parabolic F ζ hζ C R P H U a
  let G := geometry F ζ hζ C R P H U a
  let h := D.inclusion (Multiplicative.ofAdd l)
  obtain ⟨A, hA, hc⟩ := D.upper h.val h.property
  have ha := G.actual_action h A hA hc ((x,b),0)
  rw [G.unipotent_action l ((x,b),0)] at ha
  have hp := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).injective ha
  have he : G.crossAction h (x,b) = (x + KPCuspCharts.embedding F l.val,b) := by
    rw [G.crossAction_formula h A hA hc]
    exact (congrArg Prod.fst hp).symm
  have hh := actualCuspSheet_crossAction F ζ hζ C R P H U ι hι f hf a s hs h t (x,b) ε
  change G.crossAction h (x,b) = _ at he
  change KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t
    (G.crossAction h (x,b)).1 (G.crossAction h (x,b)).2 ε = _ at hh
  rw [he] at hh
  exact hh

private theorem actualCuspSheet_kernel_representative
    (t : ℝ) (x y : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F)
    (ε : rootsOfUnity 3 F)
    (hxy : (QuotientAddGroup.mk x : KernelTorus F ζ hζ C R P H U a) = QuotientAddGroup.mk y) :
    KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t x b ε =
      KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t y b ε := by
  have hx : -x + y ∈ KPCuspCharts.translationLattice F
      (KPCuspGenuineMonodromy.kernelLattice (stabilizer F ζ hζ C R P H U a)
        (parabolic F ζ hζ C R P H U a) (rho F ζ hζ C R P H U a)) := by
    simpa [sub_eq_add_neg, add_comm] using (QuotientAddGroup.eq_iff_sub_mem).mp hxy.symm
  obtain ⟨l, hl, he⟩ := hx
  have hy : y = x + KPCuspCharts.embedding F l := by rw [he]; abel
  rw [hy, actualCuspSheet_translation F ζ hζ C R P H U ι hι f hf a s hs
    ⟨l, hl.1⟩, hl.2 hl.1, map_one, Units.val_one, one_mul]

omit ι hι f hf s hs in
private theorem kernel_borel : BorelSpace (KernelTorus F ζ hζ C R P H U a) := by
  obtain ⟨hd, -⟩ := (geometry F ζ hζ C R P H U a).lattice
  let N : AddSubgroup (KPCuspCharts.Horizontal F) :=
    KPCuspCharts.translationLattice F
      (KPCuspGenuineMonodromy.kernelLattice
        (KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U a)
        (KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U a)
        (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U a))
  have hle : N ≤ KPCuspCharts.translationLattice F
      (KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U a).L :=
    AddSubgroup.map_mono
      (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).kernel_le
  letI : DiscreteTopology (N : Set (KPCuspCharts.Horizontal F)) :=
    DiscreteTopology.of_subset hd hle
  haveI : IsClosed (N : Set (KPCuspCharts.Horizontal F)) :=
    AddSubgroup.isClosed_of_discreteTopology
  haveI : N.Normal := AddSubgroup.normal_of_isAddCommutative N
  haveI : T3Space (KPCuspCharts.Horizontal F ⧸ N) := QuotientAddGroup.instT3Space N
  exact AddCosetSpace.borelSpace

omit s hs in
private theorem jet_representative (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (t : ℝ) (x y : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F)
    (ε : rootsOfUnity 3 F)
    (hxy : (QuotientAddGroup.mk x : KernelTorus F ζ hζ C R P H U a) = QuotientAddGroup.mk y) :
    cuspSheet F ζ hζ C R P H U ι f a k s t x b ε =
      cuspSheet F ζ hζ C R P H U ι f a k s t y b ε := by
  rw [← cusp_restriction_commute F ζ hζ C R P H U ι f hι hf a k s hs t x b ε,
    ← cusp_restriction_commute F ζ hζ C R P H U ι f hι hf a k s hs t y b ε]
  exact iteratedDerivWithin_congr (fun z hz =>
    actualCuspSheet_kernel_representative F ζ hζ C R P H U ι hι f hf a z hz
      t x y b ε hxy) hs

omit s hs in
private theorem jet_continuous (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (t : ℝ) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    Continuous (fun z : KernelTorus F ζ hζ C R P H U a =>
      cuspSheet F ζ hζ C R P H U ι f a k s t (Quotient.out z) b ε) := by
  let u : KPCuspCharts.Horizontal F → ℂ := fun x =>
    cuspSheet F ζ hζ C R P H U ι f a k s t x b ε
  have hu : Continuous u := by
    have hh := KPContActualChamberNormalSeries.mixedJet_continuous F ζ hζ U ι f hι hf k [] s hs
    have harch : Continuous (fun x : KPCuspCharts.Horizontal F => KPCuspCharts.toArch F ((x,b),t)) :=
      (KPCuspCharts.toArch_contDiff F).continuous.comp
        ((continuous_id.prodMk continuous_const).prodMk continuous_const)
    have hsec := (KPContSectorArchSphericalFibers.section_continuous F ζ hζ).comp harch
    have hins := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp hsec
    simpa only [u, cuspSheet, jet, KPContActualChamberNormalSeries.mixedJet,
      KPContActualChamberNormalSeries.rightWord, List.foldr_nil,
      cuspGroup, localGroup, Function.comp_def, Pi.mul_apply] using
      hh.comp (continuous_const.mul (hins.mul continuous_const))
  have hrel : ∀ x y, (QuotientAddGroup.leftRel
      (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice
        (stabilizer F ζ hζ C R P H U a) (parabolic F ζ hζ C R P H U a)
        (rho F ζ hζ C R P H U a)))).r x y → u x = u y := by
    intro x y h
    exact jet_representative F ζ hζ C R P H U ι hι f hf a k s hs t x y b ε (Quotient.sound h)
  have heq : (fun z : KernelTorus F ζ hζ C R P H U a => u (Quotient.out z)) =
      Quotient.lift u hrel := by
    funext z
    conv_rhs => rw [← Quotient.out_eq z]
    rfl
  change Continuous (fun z : KernelTorus F ζ hζ C R P H U a => u (Quotient.out z))
  rw [heq]
  exact hu.quotient_lift hrel

omit ι hι f hf a s hs in
private theorem integral_extension {B T : Type*}
    [TopologicalSpace B] [CompactSpace B] [TopologicalSpace T] [CompactSpace T]
    [MeasurableSpace T] [BorelSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ]
    (π : C(B,T)) (hπ : Function.Surjective π) :
    ∃ I : C(B,ℂ) →L[ℂ] ℂ, ∀ u : C(T,ℂ), I (u.comp π) = ∫ q, u q ∂μ := by
  let J : C(T,ℂ) →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := fun u => ∫ q, u q ∂μ
      map_add' := fun u v => integral_add
        (u.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (v.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c u => integral_smul c u }
    1 (by
      intro u
      simpa using norm_integral_le_of_norm_le_const (μ := μ)
        (Filter.Eventually.of_forall (u.norm_coe_le_norm)))
  let i : C(T,ℂ) →ₗᵢ[ℂ] C(B,ℂ) :=
    { toLinearMap := (ContinuousMap.compCLM ℂ ℂ π).toLinearMap
      norm_map' := by
        intro u
        apply le_antisymm
        · exact (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
            (fun x => u.norm_coe_le_norm (π x))
        · exact (ContinuousMap.norm_le _ (norm_nonneg (u.comp π))).mpr (fun q => by
            obtain ⟨x, rfl⟩ := hπ q
            exact (u.comp π).norm_coe_le_norm x) }
  obtain ⟨I,hI,_⟩ := exists_extension_norm_eq i.toLinearMap.range
    (J.comp i.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨I, fun u => ?_⟩
  have h := hI (i.equivRange u)
  have hi : (i.equivRange u).val = u.comp π := by
    rw [LinearIsometry.equivRange_apply_coe]; rfl
  have hj : (J.comp i.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap)
      (i.equivRange u) = J u := by
    change J (i.equivRange.symm (i.equivRange u)) = J u
    rw [LinearIsometryEquiv.symm_apply_apply]
  rw [hi, hj] at h
  exact h

omit ι hι f hf a s hs in
private theorem clm_jet {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (I : E →L[ℂ] G) (g : ℂ → E) (W : Set ℂ) (hW : IsOpen W)
    (hg : DifferentiableOn ℂ g W) (k : ℕ) (s : ℂ) (hs : s ∈ W) :
    iteratedDerivWithin k (fun z => I (g z)) W s = I (iteratedDerivWithin k g W s) := by
  have hc := (hg.contDiffOn (n := (k : ℕ∞)) hW).contDiffWithinAt hs
  have h := congrArg (fun p => p (fun _ => (1 : ℂ)))
    (I.iteratedFDerivWithin_comp_left hc hW.uniqueDiffOn hs (i := k) le_rfl)
  simpa [iteratedDerivWithin, Function.comp_def] using h

omit s hs in
private theorem integral_model
    (μ : Measure (KernelTorus F ζ hζ C R P H U a)) [IsProbabilityMeasure μ]
    (t : ℝ) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    ∃ (B : Set (KPCuspCharts.Horizontal F)) (hB : IsCompact B),
      letI : CompactSpace B := isCompact_iff_compactSpace.mp hB
      ∃ (g : ℂ → C(B,ℂ)) (I : C(B,ℂ) →L[ℂ] ℂ),
        DifferentiableOn ℂ g V ∧ ∀ k s, s ∈ V →
          I (iteratedDerivWithin k g V s) =
            ∫ q : KernelTorus F ζ hζ C R P H U a,
              cuspSheet F ζ hζ C R P H U ι f a k s t (Quotient.out q) b ε ∂μ := by
  letI := (monodromy F ζ hζ C R P H U a).compact
  letI := kernel_borel F ζ hζ C R P H U a
  obtain ⟨B,hB,hrep⟩ := KPContinuation.ChamberModerateGrowth.compact_kernel_representatives
    F ζ hζ C R P H U a
  letI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let π : C(B, KernelTorus F ζ hζ C R P H U a) :=
    ⟨fun x => QuotientAddGroup.mk x.val, QuotientAddGroup.continuous_mk.comp continuous_subtype_val⟩
  have hπ : Function.Surjective π := fun q => by
    obtain ⟨x,hx,he⟩ := hrep q
    exact ⟨⟨x,hx⟩,he⟩
  obtain ⟨I,hI⟩ := integral_extension μ π hπ
  let c : KPCuspCharts.Horizontal F → KPContActualChamberNormalSeries.G F ζ hζ :=
    fun x => cuspGroup F ζ hζ C R P H U a t x b ε
  have hc : Continuous c := by
    have harch : Continuous (fun x : KPCuspCharts.Horizontal F => KPCuspCharts.toArch F ((x,b),t)) :=
      (KPCuspCharts.toArch_contDiff F).continuous.comp
        ((continuous_id.prodMk continuous_const).prodMk continuous_const)
    have hsec := (KPContSectorArchSphericalFibers.section_continuous F ζ hζ).comp harch
    have hins := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp hsec
    exact continuous_const.mul (hins.mul continuous_const)
  let A := c '' B
  have hA : IsCompact A := hB.image hc
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let cB : C(B,A) := ⟨fun x => ⟨c x.val, ⟨x.val,x.property,rfl⟩⟩,
    (hc.comp continuous_subtype_val).subtype_mk _⟩
  let g : ℂ → C(B,ℂ) := fun z =>
    (KPContActualChamberNormalSeries.compactMixedJet F ζ hζ U ι f hι hf 0 [] A z).comp cB
  have hg : DifferentiableOn ℂ g V :=
    (ContinuousMap.compCLM ℂ ℂ cB).differentiable.comp_differentiableOn
      (KPContActualChamberNormalSeries.compactMixedJet_holomorphic
        F ζ hζ U ι f hι hf 0 [] A hA)
  have hval (z : ℂ) (hz : z ∈ V) (x : B) :
      g z x = cuspSheet F ζ hζ C R P H U ι f a 0 z t x.val b ε := by
    simp [g, KPContActualChamberNormalSeries.compactMixedJet, hz, cB, c,
      KPContActualChamberNormalSeries.mixedJet, KPContActualChamberNormalSeries.rightWord,
      cuspSheet, jet]
  refine ⟨B,hB,g,I,hg,?_⟩
  intro k s hs
  let u : C(KernelTorus F ζ hζ C R P H U a,ℂ) :=
    ⟨fun q => cuspSheet F ζ hζ C R P H U ι f a k s t (Quotient.out q) b ε,
      jet_continuous F ζ hζ C R P H U ι hι f hf a k s hs t b ε⟩
  have he : iteratedDerivWithin k g V s = u.comp π := by
    ext x
    have hx := clm_jet (ContinuousMap.evalCLM ℂ x) g V
      KPChamberL2Defect.chamber_isOpen hg k s hs
    simp only [ContinuousMap.evalCLM_apply] at hx
    rw [← hx]
    rw [iteratedDerivWithin_congr (fun z hz => hval z hz x) hs,
      cusp_restriction_commute F ζ hζ C R P H U ι f hι hf a k s hs]
    exact jet_representative F ζ hζ C R P H U ι hι f hf a k s hs t x.val
      (Quotient.out (π x)) b ε (Quotient.out_eq (π x)).symm
  rw [he]
  exact hI u

end CuspAnalytic

theorem cusp_fiber_integrable (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (a : Cusps F ζ hζ C R P H U)
    (μ : Measure (KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a))
    [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (k : ℕ) (s : ℂ) (hs : s ∈ V) (t : ℝ) (b : KPCuspCharts.Shape F)
    (ε : rootsOfUnity 3 F) :
    Integrable (fun z : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a =>
      cuspSheet F ζ hζ C R P H U ι f a k s t (Quotient.out z) b ε) μ := by
  letI := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).compact
  letI := CuspAnalytic.kernel_borel F ζ hζ C R P H U a
  exact (CuspAnalytic.jet_continuous F ζ hζ C R P H U ι hι f hf a k s hs t b ε).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem cusp_integral_commute (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (a : Cusps F ζ hζ C R P H U)
    (μ : Measure (KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a))
    [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (k : ℕ) (s : ℂ) (hs : s ∈ V) (t : ℝ) (b : KPCuspCharts.Shape F)
    (ε : rootsOfUnity 3 F) :
    iteratedDerivWithin k
      (fun z => ∫ q : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a,
        cuspSheet F ζ hζ C R P H U ι f a 0 z t (Quotient.out q) b ε ∂μ) V s =
    ∫ q : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a,
      cuspSheet F ζ hζ C R P H U ι f a k s t (Quotient.out q) b ε ∂μ := by
  obtain ⟨B,hB,g,I,hg,hI⟩ := CuspAnalytic.integral_model F ζ hζ C R P H U ι hι f hf a μ t b ε
  letI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  calc
    _ = iteratedDerivWithin k (fun z => I (g z)) V s :=
      iteratedDerivWithin_congr (fun z hz => (hI 0 z hz).symm) hs
    _ = I (iteratedDerivWithin k g V s) :=
      CuspAnalytic.clm_jet I g V KPChamberL2Defect.chamber_isOpen hg k s hs
    _ = _ := hI k s hs

private theorem cusp_integral_holomorphic (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (a : Cusps F ζ hζ C R P H U)
    (μ : Measure (KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a))
    [IsProbabilityMeasure μ] (t : ℝ) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    DifferentiableOn ℂ (fun z =>
      ∫ q : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a,
        cuspSheet F ζ hζ C R P H U ι f a 0 z t (Quotient.out q) b ε ∂μ) V := by
  obtain ⟨B,hB,g,I,hg,hI⟩ := CuspAnalytic.integral_model F ζ hζ C R P H U ι hι f hf a μ t b ε
  letI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  exact (I.differentiable.comp_differentiableOn hg).congr (fun z hz => (hI 0 z hz).symm)

 def projectionFunctional (a : Cusps F ζ hζ C R P H U)
    (q : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a) :
    (rootsOfUnity 3 F → ℂ) →L[ℂ] ℂ := by
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  let l : (rootsOfUnity 3 F → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun e => (KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a e).val q
      map_add' := fun x y => by
        rw [map_add]; rfl
      map_smul' := fun c x => by
        rw [map_smul]; rfl }
  exact l.toContinuousLinearMap

theorem cusp_projection_commute (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (a : Cusps F ζ hζ C R P H U)
    (μ : Measure (KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a))
    [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (k : ℕ) (s : ℂ) (hs : s ∈ V) (t : ℝ) (b : KPCuspCharts.Shape F)
    (q : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a) :
    iteratedDerivWithin k
      (fun z => (cuspProjection F ζ hζ C R P H U ι f a μ 0 z t b).val q) V s =
        (cuspProjection F ζ hζ C R P H U ι f a μ k s t b).val q := by
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  let e : ℂ → rootsOfUnity 3 F → ℂ := fun z ε =>
    ∫ r : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a,
      cuspSheet F ζ hζ C R P H U ι f a 0 z t (Quotient.out r) b ε ∂μ
  have he : DifferentiableOn ℂ e V := by
    exact differentiableOn_pi.mpr (fun ε => cusp_integral_holomorphic F ζ hζ C R P H U ι f hι hf a μ t b ε)
  let L := projectionFunctional F ζ hζ C R P H U a q
  change iteratedDerivWithin k (fun z => L (e z)) V s = _
  rw [CuspAnalytic.clm_jet L e V KPChamberL2Defect.chamber_isOpen he k s hs]
  have hj : iteratedDerivWithin k e V s = fun ε =>
      ∫ r : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a,
        cuspSheet F ζ hζ C R P H U ι f a k s t (Quotient.out r) b ε ∂μ := by
    funext ε
    have h := CuspAnalytic.clm_jet (ContinuousLinearMap.proj ε) e V
      KPChamberL2Defect.chamber_isOpen he k s hs
    simp only [ContinuousLinearMap.proj_apply] at h
    rw [← h]
    exact cusp_integral_commute F ζ hζ C R P H U ι f hι hf a μ k s hs t b ε
  rw [hj]
  rfl

structure Properties (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) : Prop where
  dimension_pos : 0 < d F
  spectral_polynomial : ∀ s ∈ V,
    lambda F s = (d F : ℂ) * (1 - (1 / 3 + 2 * s) ^ 2)
  spectral_derivatives : ∀ s ∈ V,
    lambdaJet F 0 s = lambda F s ∧
    lambdaJet F 1 s = -4 * (d F : ℂ) * (1 / 3 + 2 * s) ∧
    lambdaJet F 2 s = -8 * (d F : ℂ) ∧
    (∀ j : ℕ, 2 < j → lambdaJet F j s = 0)
  descent : ∀ k s, s ∈ V → ∀ g,
    (coveredJet F ζ hζ C R P H U ι f hι hf k s).val
      (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ (level F ζ hζ C R P H U)
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) = jet F ζ hζ U ι f k s g
  smooth : ∀ k s, s ∈ V →
    KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ (level F ζ hζ C R P H U)
      R P H (lineJet F ζ hζ C R P H U ι f hι hf k s)
  frame_derivatives : ∀ k s, s ∈ V →
    ∀ (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
      (a : Frame F ζ hζ C R P H U i) (x : M F), x ∈ a.omega →
    iteratedDerivWithin k
      (fun z => frameJet F ζ hζ C R P H U ι f hι hf 0 z a x) V s =
        frameJet F ζ hζ C R P H U ι f hι hf k s a x
  casimir : ∀ k s, s ∈ V →
    ∀ (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
      (a : Frame F ζ hζ C R P H U i) (x : M F), x ∈ a.omega →
    HyperbolicChart.laplacian (d F)
      (frameJet F ζ hζ C R P H U ι f hι hf k s a) x =
    lambda F s * frameJet F ζ hζ C R P H U ι f hι hf k s a x +
      ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) * lambdaJet F j s *
        frameJet F ζ hζ C R P H U ι f hι hf (k - j) s a x
  spatial_commute : ∀ k s, s ∈ V →
    ∀ (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
      (a : Frame F ζ hζ C R P H U i)
      (J : Finset (List (Fin (d F) × Fin 3)))
      (c : List (Fin (d F) × Fin 3) → M F → ℂ),
      (∀ w ∈ J, ContDiffOn ℝ (⊤ : ℕ∞) (c w) a.omega) →
      ∀ x ∈ a.omega,
    iteratedDerivWithin k
      (fun z => spatialOperator F J c (frameJet F ζ hζ C R P H U ι f hι hf 0 z a) x) V s =
    spatialOperator F J c (frameJet F ζ hζ C R P H U ι f hι hf k s a) x
  right_commute : ∀ k (w : KPContActualChamberNormalSeries.Word F) s, s ∈ V → ∀ g,
    iteratedDerivWithin k
      (fun z => KPContActualChamberNormalSeries.rightWord F ζ hζ w
        (KPContActualChamberNormalSeries.E F ζ hζ U ι f z) g) V s =
      KPContActualChamberNormalSeries.rightWord F ζ hζ w (jet F ζ hζ U ι f k s) g
  cusp_restriction : ∀ (a : Cusps F ζ hζ C R P H U) k s, s ∈ V → ∀ t x b ε,
    iteratedDerivWithin k (fun z => cuspSheet F ζ hζ C R P H U ι f a 0 z t x b ε) V s =
      cuspSheet F ζ hζ C R P H U ι f a k s t x b ε
  cusp_integrable : ∀ (a : Cusps F ζ hζ C R P H U)
    (μ : Measure (KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a)),
    μ.IsAddHaarMeasure → IsProbabilityMeasure μ → ∀ k s, s ∈ V → ∀ t b ε,
    Integrable (fun z : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a =>
      cuspSheet F ζ hζ C R P H U ι f a k s t (Quotient.out z) b ε) μ
  cusp_integral : ∀ (a : Cusps F ζ hζ C R P H U)
    (μ : Measure (KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a)),
    μ.IsAddHaarMeasure → IsProbabilityMeasure μ → ∀ k s, s ∈ V → ∀ t b ε,
    iteratedDerivWithin k
      (fun z => ∫ q : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a,
        cuspSheet F ζ hζ C R P H U ι f a 0 z t (Quotient.out q) b ε ∂μ) V s =
    ∫ q : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a,
      cuspSheet F ζ hζ C R P H U ι f a k s t (Quotient.out q) b ε ∂μ
  cusp_projection : ∀ (a : Cusps F ζ hζ C R P H U)
    (μ : Measure (KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a)),
    μ.IsAddHaarMeasure → IsProbabilityMeasure μ → ∀ k s, s ∈ V → ∀ t b q,
    iteratedDerivWithin k
      (fun z => (cuspProjection F ζ hζ C R P H U ι f a μ 0 z t b).val q) V s =
        (cuspProjection F ζ hζ C R P H U ι f a μ k s t b).val q

end DedekindZetaZeroFree.KPContActualChamberCasimirJets

namespace DedekindZetaZeroFree

theorem kp_cont_actual_chamber_casimir_jets
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (hι : Function.Injective ι) (f : ℂ → S)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) :
    KPContActualChamberCasimirJets.Properties F ζ hζ C R P H U ι f hι hf := by
  refine ⟨KPContActualChamberCasimirJets.dimension_pos F ζ hζ,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (KPContActualChamberCasimirJets.spectral_jets F s hs).1
  · intro s hs
    exact (KPContActualChamberCasimirJets.spectral_jets F s hs).2
  · intro k s hs g
    exact KPContActualChamberCasimirJets.coveredJet_projection F ζ hζ C R P H U ι f hι hf k s hs g
  · intro k s hs
    exact KPContActualChamberCasimirJets.lineJet_smooth F ζ hζ C R P H U ι f hι hf k s hs
  · intro k s hs i a x hx
    exact KPContActualChamberCasimirJets.frameJet_eq_derivative F ζ hζ C R P H U ι f hι hf k s hs a x hx
  · intro k s hs i a x hx
    exact KPContActualChamberCasimirJets.casimir_jets F ζ hζ C R P H U ι f hι hf k s hs a x hx
  · intro k s hs i a J c hc x hx
    exact KPContActualChamberCasimirJets.spatial_commute F ζ hζ C R P H U ι f hι hf k s hs a J c hc x hx
  · intro k w s hs g
    exact KPContActualChamberCasimirJets.rightWord_commute F ζ hζ U ι f hι hf k w s hs g
  · intro a k s hs t x b ε
    exact KPContActualChamberCasimirJets.cusp_restriction_commute F ζ hζ C R P H U ι f hι hf a k s hs t x b ε
  · intro a μ hHaar hProb k s hs t b ε
    letI := hHaar
    letI := hProb
    exact KPContActualChamberCasimirJets.cusp_fiber_integrable F ζ hζ C R P H U ι f hι hf a μ k s hs t b ε
  · intro a μ hHaar hProb k s hs t b ε
    letI := hHaar
    letI := hProb
    exact KPContActualChamberCasimirJets.cusp_integral_commute F ζ hζ C R P H U ι f hι hf a μ k s hs t b ε
  · intro a μ hHaar hProb k s hs t b q
    letI := hHaar
    letI := hProb
    exact KPContActualChamberCasimirJets.cusp_projection_commute F ζ hζ C R P H U ι f hι hf a μ k s hs t b q

end DedekindZetaZeroFree

end

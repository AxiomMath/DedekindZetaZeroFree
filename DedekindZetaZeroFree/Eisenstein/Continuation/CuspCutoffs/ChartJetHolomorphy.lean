module

public import DedekindZetaZeroFree.Analysis.HolomorphicFunctions.SmoothFamilies.SpatialCauchyDifferentiation
public import DedekindZetaZeroFree.Analysis.HolomorphicFunctions.SmoothFamilies.UniformJetCauchyConvergence
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.SmoothDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff
open Topology

namespace DedekindZetaZeroFree.KPContActualCutoffChartJetHolomorphy

open KPContLocalNorm

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

abbrev dimension := KPContCotangentActualOverlap.d F * 3

abbrev Chart (i : Fin (H.atlas (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)).componentCount) :=
  KPContCotangentActualOverlap.LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)
    (R := R) (P := P) (H := H) i

def coordinates (x : Space (dimension F)) : KPContCotangentActualOverlap.M F :=
  WithLp.toLp 2 (fun ik => x (finProdFinEquiv ik))

variable {i : Fin (H.atlas (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)).componentCount}

def chartDomain (q : Chart F ζ hζ C R P H U i) : Set (Space (dimension F)) :=
  coordinates F ⁻¹' q.omega

def framePullback (q : Chart F ζ hζ C R P H U i)
    (w : KPContActualCutoffSmoothDescent.SmoothSections F ζ hζ C R P H U) :
    Space (dimension F) → ℂ :=
  fun x => q.coefficient w.val (coordinates F x)

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H T)
variable (Ω : Set ℂ) (f : ℂ → S)
variable (χ : KPContActualCutoffSmoothDescent.Cusps F ζ hζ C R P H U →
  KPCutoffSource.SmoothCuspCutoff T)

def pullback
    (D : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι buffer Ω f χ)
    (q : Chart F ζ hζ C R P H U i) (commutator : Bool) :
    ℂ → Space (dimension F) → ℂ :=
  fun s => framePullback F ζ hζ C R P H U q
    (if commutator then D.commutator s else D.cutoff s)

theorem coordinates_contDiff : ContDiff ℝ (⊤ : ℕ∞) (coordinates F) := by
  unfold coordinates
  have hh : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Space (dimension F) => fun ik : Fin (KPContCotangentActualOverlap.d F) × Fin 3 =>
        x (finProdFinEquiv ik)) := by
    apply contDiff_pi.mpr
    intro ik
    exact (EuclideanSpace.proj (𝕜 := ℝ) (finProdFinEquiv ik)).contDiff
  exact PiLp.contDiff_toLp.comp hh

theorem chartDomain_isOpen (q : Chart F ζ hζ C R P H U i) :
    IsOpen (chartDomain F ζ hζ C R P H U q) :=
  q.isOpen_omega.preimage (coordinates_contDiff F).continuous

theorem framePullback_smooth (q : Chart F ζ hζ C R P H U i)
    (w : KPContActualCutoffSmoothDescent.SmoothSections F ζ hζ C R P H U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (framePullback F ζ hζ C R P H U q w)
      (chartDomain F ζ hζ C R P H U q) := by
  have hA : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Space (dimension F) => KPContCotangentActualOverlap.labeledA q.places (coordinates F x)) := by
    apply contDiff_pi.mpr
    intro k
    exact ((contDiff_apply ℝ (ℂ × ℝ) (q.places.symm k)).comp
      (CotangentLogCoframe.A (KPContCotangentActualOverlap.d F)).contDiff).comp
        (coordinates_contDiff F)
  have hact : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : KPCuspGenuineMonodromy.SymmetricSpace F => q.kind.representative • x) := by
    obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective q.kind.representative
    rw [← hG]
    have he : (fun x : KPCuspGenuineMonodromy.SymmetricSpace F =>
        (Matrix.ProjGenLinGroup.mk G : KPCuspArithmetic.PGL2 F) • x) = KPCuspSiegel.glAction F G := by
      funext x; exact KPCuspSiegel.action_mk F G x
    rw [he]
    exact (KPArch.productAction_contDiff (KPCuspLogShape.dimension F)
      (fun k => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F k).embedding G)).of_le le_top
  have hphase : IsLocallyConstant
      (fun x : chartDomain F ζ hζ C R P H U q =>
        (KPCuspGenuineMonodromy.chi F ζ hζ (q.splitting (coordinates F x.val)) : ℂ)) := by
    exact (q.splitting_locallyConstant.comp_continuous
      (((coordinates_contDiff F).continuous.comp continuous_subtype_val).subtype_mk
        (fun x => x.property))).comp (fun ε => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ))
  have hphaseSmooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => (KPCuspGenuineMonodromy.chi F ζ hζ (q.splitting (coordinates F x)) : ℂ))
      (chartDomain F ζ hζ C R P H U q) := by
    intro x hx
    apply contDiffWithinAt_const.congr_of_eventuallyEq _ rfl
    rw [nhdsWithin_eq_map_subtype_coe hx]
    exact hphase.eventually_eq ⟨x, hx⟩
  exact hphaseSmooth.mul (((w.property i).comp (hact.comp hA)).contDiffOn)

theorem framePullback_scalar
    (q : Chart F ζ hζ C R P H U i)
    (w : KPContActualCutoffSmoothDescent.SmoothSections F ζ hζ C R P H U) (x : Space (dimension F)) :
    framePullback F ζ hζ C R P H U q w x =
      (KPCuspGenuineMonodromy.chi F ζ hζ (q.splitting (coordinates F x)) : ℂ) *
        KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U w
          (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
            (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U))
            (q.kind.representative • KPContCotangentActualOverlap.labeledA q.places (coordinates F x),
              (H.atlas (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)).representative i)) := by
  have hw : w.val = KPContSectorScalarLineAlgebra.S F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H
      ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
        (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H).symm w).val := by
    rw [← KPContSectorSmoothFramesSupport.smoothS_apply, LinearEquiv.apply_symm_apply]
  unfold framePullback KPContCotangentActualOverlap.LiftedChart.coefficient
  rw [hw, KPContSectorScalarLineAlgebra.S_apply]
  rfl

theorem pullback_formula
    (D : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι buffer Ω f χ)
    (q : Chart F ζ hζ C R P H U i) (b : Bool) (s : ℂ) (hs : s ∈ Ω)
    (x : Space (dimension F)) :
    pullback F ζ hζ C R P H U ι buffer Ω f χ D q b s x =
      (KPCuspGenuineMonodromy.chi F ζ hζ (q.splitting (coordinates F x)) : ℂ) *
        (if b then KPContActualCutoffSmoothDescent.commutatorScalar F ζ hζ C R P H U ι buffer χ f s
          else KPContActualCutoffSmoothDescent.cutoffScalar F ζ hζ C R P H U ι buffer χ f s)
          (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
            (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U))
            (q.kind.representative • KPContCotangentActualOverlap.labeledA q.places (coordinates F x),
              (H.atlas (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)).representative i)) := by
  cases b <;> simp only [pullback, Bool.false_eq_true, ↓reduceIte,
    framePullback_scalar, D.cutoff_formula s hs, D.commutator_formula s hs]

theorem pullback_smooth
    (D : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι buffer Ω f χ)
    (q : Chart F ζ hζ C R P H U i) (b : Bool) (s : ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (pullback F ζ hζ C R P H U ι buffer Ω f χ D q b s)
      (chartDomain F ζ hζ C R P H U q) :=
  framePullback_smooth F ζ hζ C R P H U q _

theorem parameter_derivatives_bounded {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {j : ℂ → E} (hj : DifferentiableOn ℂ j Ω) (k : ℕ)
    {Q : Set ℂ} (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Q, ‖iteratedDeriv k j s‖ ≤ M := by
  have hc : ContDiffOn ℂ (k : ℕ) j Ω := hj.contDiffOn hΩ
  have hcont : ContinuousOn (iteratedDeriv k j) Ω := by
    apply (hc.continuousOn_iteratedDerivWithin (le_refl _) hΩ.uniqueDiffOn).congr
    intro s hs
    exact (iteratedDerivWithin_eq_iteratedDeriv hΩ.uniqueDiffOn
      (hc.contDiffAt (hΩ.mem_nhds hs)) hs).symm
  obtain ⟨M, hM⟩ := hQ.exists_bound_of_continuousOn (hcont.mono hQΩ)
  exact ⟨max M 0, le_max_right _ _, fun s hs => (hM s hs).trans (le_max_left _ _)⟩

 theorem coordinateDerivativeList_contDiffOn {n : ℕ} {U : Set (Space n)}
    (hU : IsOpen U) (u : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (l : List (Fin n)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l u) U := by
  induction l with
  | nil => exact hu
  | cons i is ih =>
    exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

 def chartJet {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    (L : Set (Space n)) (hLU : L ⊆ U) (m : ℕ) (g : Space n → ℂ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) : CompactJets L m :=
  fun α => ⟨fun x => coordinateDerivative α g x,
    ((coordinateDerivativeList_contDiffOn hU g hg α.directions).continuousOn.mono hLU).restrict⟩

private theorem coordinateDerivativeList_const_mul_on {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    (u : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (c : ℂ)
    (l : List (Fin n)) : Set.EqOn (coordinateDerivativeList l (fun x => c * u x))
      (fun x => c * coordinateDerivativeList l u x) U := by
  induction l with
  | nil => intro x hx; rfl
  | cons i l ih =>
    intro x hx
    have hd : DifferentiableAt ℝ (coordinateDerivativeList l u) x :=
      ((coordinateDerivativeList_contDiffOn hU u hu l).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    change fderiv ℝ (coordinateDerivativeList l (fun x => c * u x)) x _ = _
    have he : coordinateDerivativeList l (fun x => c * u x) =ᶠ[𝓝 x]
        (fun x => c * coordinateDerivativeList l u x) :=
      (hU.eventually_mem hx).mono (fun y hy => ih hy)
    rw [he.fderiv_eq]
    simpa only [coordinateDerivativeList, ContinuousLinearMap.smul_apply, smul_eq_mul]
      using congrArg (fun L : Space n →L[ℝ] ℂ => L (EuclideanSpace.single i 1))
        (fderiv_const_mul hd c)

private theorem coordinateDerivativeList_add_on {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    (u v : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) (l : List (Fin n)) :
    Set.EqOn (coordinateDerivativeList l (fun x => u x + v x))
      (fun x => coordinateDerivativeList l u x + coordinateDerivativeList l v x) U := by
  induction l with
  | nil => intro x hx; rfl
  | cons i l ih =>
    intro x hx
    have hu' : DifferentiableAt ℝ (coordinateDerivativeList l u) x :=
      ((coordinateDerivativeList_contDiffOn hU u hu l).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hv' : DifferentiableAt ℝ (coordinateDerivativeList l v) x :=
      ((coordinateDerivativeList_contDiffOn hU v hv l).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have he : coordinateDerivativeList l (fun x => u x + v x) =ᶠ[𝓝 x]
        (fun x => coordinateDerivativeList l u x + coordinateDerivativeList l v x) :=
      (hU.eventually_mem hx).mono (fun y hy => ih hy)
    change fderiv ℝ (coordinateDerivativeList l (fun x => u x + v x)) x _ = _
    rw [he.fderiv_eq]
    simpa only [coordinateDerivativeList, ContinuousLinearMap.add_apply, Pi.add_def]
      using congrArg (fun L : Space n →L[ℝ] ℂ => L (EuclideanSpace.single i 1))
        (fderiv_add hu' hv')

private theorem coordinateDerivativeList_sum_on {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    {J : Type*} (I : Finset J) (u : J → Space n → ℂ)
    (hu : ∀ j ∈ I, ContDiffOn ℝ (⊤ : ℕ∞) (u j) U) (l : List (Fin n)) :
    Set.EqOn (coordinateDerivativeList l (fun x => ∑ j ∈ I, u j x))
      (fun x => ∑ j ∈ I, coordinateDerivativeList l (u j) x) U := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have hz : coordinateDerivativeList l (fun _ : Space n => (0 : ℂ)) = (fun _ => 0) := by
      induction l with
      | nil => rfl
      | cons i l ih => simp [coordinateDerivativeList, ih]
    intro x hx
    exact congrFun hz x
  | @insert j I hj ih =>
    have huj := hu j (Finset.mem_insert_self j I)
    have huI : ∀ k ∈ I, ContDiffOn ℝ (⊤ : ℕ∞) (u k) U :=
      fun k hk => hu k (Finset.mem_insert_of_mem hk)
    simp only [Finset.sum_insert hj]
    intro x hx
    rw [coordinateDerivativeList_add_on hU (u j) (fun x => ∑ k ∈ I, u k x) huj (ContDiffOn.sum huI) l hx]
    exact congrArg (fun a => coordinateDerivativeList l (u j) x + a) (ih huI hx)

theorem finite_separated_compactJets {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    {O : Set ℂ} {J : Type*} (I : Finset J) (a : J → ℂ → ℂ)
    (ha : ∀ j ∈ I, DifferentiableOn ℂ (a j) O)
    (ψ : J → Space n → ℂ) (hψ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (ψ j) U)
    (L : Set (Space n)) (hL : IsCompact L) (hLU : L ⊆ U) (m : ℕ) :
    letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
    ∃ jet : ℂ → CompactJets L m,
      DifferentiableOn ℂ jet O ∧
      ∀ s ∈ O, ∀ α, ∀ x : L,
        jet s α x = coordinateDerivative α (fun y => ∑ j ∈ I, a j s * ψ j y) x := by
  classical
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let v : J → CompactJets L m := fun j => chartJet hU L hLU m (ψ j) (hψ j)
  let jet : ℂ → CompactJets L m := fun s => ∑ j ∈ I, a j s • v j
  refine ⟨jet, ?_, ?_⟩
  · exact DifferentiableOn.fun_sum (fun j hj => (ha j hj).smul_const (v j))
  · intro s hs α x
    have hsum := coordinateDerivativeList_sum_on hU I (fun j y => a j s * ψ j y)
      (fun j hj => contDiffOn_const.mul (hψ j)) α.directions (hLU x.property)
    have hsmul : ∀ j ∈ I, coordinateDerivativeList α.directions
        (fun y => a j s * ψ j y) x = a j s * coordinateDerivativeList α.directions (ψ j) x :=
      fun j hj => coordinateDerivativeList_const_mul_on hU (ψ j) (hψ j) (a j s) α.directions (hLU x.property)
    dsimp [jet]
    simp only [Finset.sum_apply, Pi.smul_apply, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    change (∑ j ∈ I, a j s * coordinateDerivativeList α.directions (ψ j) x) = _
    exact (hsum.trans (Finset.sum_congr rfl hsmul)).symm

def ChartPowerSeriesOn (n : ℕ) (U : Set (Space n)) (O : Set ℂ)
    (g : ℂ → Space n → ℂ) : Prop :=
  ∀ z₀ ∈ O, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z₀ ρ ⊆ O ∧
    ∃ coeff : ℕ → Space n → ℂ,
      (∀ q, ContDiffOn ℝ (⊤ : ℕ∞) (coeff q) U) ∧
      (∀ z ∈ Metric.ball z₀ ρ, ContDiffOn ℝ (⊤ : ℕ∞) (g z) U) ∧
      ∀ (L : Set (Space n)), IsCompact L → L ⊆ U → ∀ m : ℕ, ∀ r : ℝ, 0 ≤ r → r < ρ →
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ M ≥ N, ∀ z ∈ Metric.closedBall z₀ r,
          ∀ α : MultiIndex n m, ∀ x : L,
            ‖(∑ q ∈ Finset.range M, (z - z₀) ^ q * coordinateDerivative α (coeff q) x) -
              coordinateDerivative α (g z) x‖ < ε

private theorem polynomial_limit_holomorphic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (z₀ : ℂ) (r : ℝ)
    (a : ℕ → E) (f : ℂ → E)
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ M ≥ N, ∀ z ∈ Metric.closedBall z₀ r,
      ‖(∑ q ∈ Finset.range M, (z - z₀) ^ q • a q) - f z‖ < ε) :
    DifferentiableOn ℂ f (Metric.ball z₀ r) := by
  have ht : TendstoUniformlyOn
      (fun M z => ∑ q ∈ Finset.range M, (z - z₀) ^ q • a q) f
      Filter.atTop (Metric.ball z₀ r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    exact Filter.eventually_atTop.mpr ⟨N, fun M hM z hz => by
      rw [dist_eq_norm, norm_sub_rev]
      exact hN M hM z (Metric.ball_subset_closedBall hz)⟩
  apply ht.tendstoLocallyUniformlyOn.differentiableOn _ Metric.isOpen_ball
  apply Filter.Eventually.of_forall
  intro M
  exact DifferentiableOn.fun_sum (fun q _ =>
    ((differentiableOn_id.sub_const z₀).pow q).smul_const (a q))

theorem chartPowerSeries_compactJets {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    {O : Set ℂ} (hO : IsOpen O) {g : ℂ → Space n → ℂ}
    (hps : ChartPowerSeriesOn n U O g) :
    ∀ (L : Set (Space n)) (hL : IsCompact L), L ⊆ U → ∀ m : ℕ,
      letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
      ∃ j : ℂ → CompactJets L m, DifferentiableOn ℂ j O ∧
        ∀ z ∈ O, ∀ α, ∀ x : L, j z α x = coordinateDerivative α (g z) x := by
  intro L hL hLU m
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hsmooth : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (g z) U := by
    intro z hz
    obtain ⟨ρ, hρ, _, _, _, hg, _⟩ := hps z hz
    exact hg z (Metric.mem_ball_self hρ)
  let j : ℂ → CompactJets L m := fun z =>
    if hz : z ∈ O then chartJet hU L hLU m (g z) (hsmooth z hz) else 0
  have hj : ∀ z ∈ O, ∀ α, ∀ x : L, j z α x = coordinateDerivative α (g z) x := by
    intro z hz α x
    dsimp [j]
    rw [dif_pos hz]
    rfl
  refine ⟨j, ?_, hj⟩
  intro z₀ hz₀
  obtain ⟨ρ, hρ, hball, coeff, hcoeff, hg, hconv⟩ := hps z₀ hz₀
  let aj : ℕ → CompactJets L m := fun q => chartJet hU L hLU m (coeff q) (hcoeff q)
  have hhalf : 0 < ρ / 2 := by positivity
  have hlim : ∀ ε > 0, ∃ N : ℕ, ∀ M ≥ N, ∀ z ∈ Metric.closedBall z₀ (ρ / 2),
      ‖(∑ q ∈ Finset.range M, (z - z₀) ^ q • aj q) - j z‖ < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hconv L hL hLU m (ρ / 2) hhalf.le
      (by linarith) (ε / 2) (by positivity)
    refine ⟨N, fun M hM z hz => ?_⟩
    have hzρ : z ∈ Metric.ball z₀ ρ := Metric.closedBall_subset_ball (by linarith) hz
    have hzO : z ∈ O := hball hzρ
    apply lt_of_le_of_lt _ (show ε / 2 < ε by linarith)
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro α
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro x
    have hb := hN M hM z hz α x
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
      ContinuousMap.sub_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul, hj z hzO]
    change ‖(∑ q ∈ Finset.range M, (z - z₀) ^ q * coordinateDerivative α (coeff q) x) -
      coordinateDerivative α (g z) x‖ ≤ ε / 2
    exact hb.le
  exact ((polynomial_limit_holomorphic z₀ (ρ / 2) aj j hlim).differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hhalf))).differentiableWithinAt

theorem chartSmoothHolomorphic_finset_sum {n : ℕ} (B : LocalBall n)
    {O : Set ℂ} {J : Type*} (I : Finset J) (g : J → ℂ → Space n → ℂ)
    (hg : ∀ j, KPCutoffSource.ChartSmoothHolomorphicOn B (g j) O) :
    KPCutoffSource.ChartSmoothHolomorphicOn B (fun s x => ∑ j ∈ I, g j s x) O := by
  classical
  refine ⟨fun s hs => ContDiffOn.sum (fun j hj => (hg j).1 s hs), ?_⟩
  intro K hK hKB m
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  choose jets hjets hspec using (fun j => (hg j).2 K hK hKB m)
  refine ⟨fun s => ∑ j ∈ I, jets j s, DifferentiableOn.fun_sum (fun j hj => hjets j), ?_⟩
  intro s hs α x
  simp only [Finset.sum_apply, ContinuousMap.sum_apply]
  change (∑ j ∈ I, jets j s α x) = _
  simp_rw [hspec _ s hs α x]
  exact (coordinateDerivativeList_sum_on Metric.isOpen_ball I (fun j => g j s)
    (fun j hj => (hg j).1 s hs) α.directions (hKB x.property)).symm

section BallwiseSeries
open KPContLocalHolomorphyUpgrade.CauchyAssembly

private theorem ballJet_continuous {n : ℕ} (A : LocalBall n)
    (Ω : Set ℂ) (h : ℂ → Space n → ℂ)
    (hh : KPCutoffSource.ChartSmoothHolomorphicOn A h Ω) : Raw.JetContinuousOn A h Ω := by
  intro z₀ hz₀ K hK hKA m ε hε
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨j, hj, hspec⟩ := hh.2 K hK hKA m
  have hc := hj.continuousOn z₀ hz₀
  have he : ∀ᶠ z in nhdsWithin z₀ Ω, ‖j z - j z₀‖ < ε := by
    simpa only [dist_eq_norm] using hc.eventually (Metric.ball_mem_nhds (j z₀) hε)
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨δ, hδ, ?_⟩
  intro z hz hdist α x
  have hb := hd ⟨hdist, hz⟩
  have hp := (ContinuousMap.norm_coe_le_norm ((j z - j z₀) α) x).trans
    (norm_le_pi_norm (j z - j z₀) α)
  change ‖j z α x - j z₀ α x‖ ≤ _ at hp
  rw [hspec z hz α x, hspec z₀ hz₀ α x] at hp
  rw [coordinateDerivative, finite_coordinate_derivative_sub A (hh.1 z hz) (hh.1 z₀ hz₀)
    α.directions (hKA x.property), ← coordinateDerivative, ← coordinateDerivative]
  exact hp.trans_lt hb

private theorem ballScalarJet_holomorphic {n : ℕ} (A : LocalBall n) (Ω : Set ℂ)
    (f : ℂ → Space n → ℂ) (hf : KPCutoffSource.ChartSmoothHolomorphicOn A f Ω)
    (m : ℕ) (α : MultiIndex n m) (x : Space n) (hx : x ∈ A.carrier) :
    DifferentiableOn ℂ (fun s => coordinateDerivative α (f s) x) Ω := by
  let K : Set (Space n) := {x}
  have hKA : K ⊆ A.carrier := Set.singleton_subset_iff.mpr hx
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_singleton : IsCompact K)
  obtain ⟨j, hj, hv⟩ := hf.2 K isCompact_singleton hKA m
  let L : CompactJets K m →L[ℂ] ℂ :=
    (ContinuousMap.evalCLM ℂ (⟨x, rfl⟩ : K)).comp (ContinuousLinearMap.proj α)
  exact (L.differentiable.comp_differentiableOn hj).congr (fun s hs => (hv s hs α ⟨x, rfl⟩).symm)

private theorem closedContainedBall_at {n : ℕ} (hn : 0 < n) {U : Set (Space n)} (hU : IsOpen U)
    {x : Space n} (hx : x ∈ U) :
    ∃ B : LocalBall n, B.center = x ∧ Metric.closedBall B.center B.radius ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  refine ⟨⟨hn, x, r / 2, by positivity⟩, rfl, ?_⟩
  exact (Metric.closedBall_subset_ball (by linarith)).trans hrU

theorem chartPowerSeries_of_ballwise {n : ℕ} (hn : 0 < n) {U : Set (Space n)} (hU : IsOpen U)
    {O : Set ℂ} (hO : IsOpen O) (g : ℂ → Space n → ℂ)
    (hsmooth : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (g z) U)
    (hball : ∀ B : LocalBall n, Metric.closedBall B.center B.radius ⊆ U →
      KPCutoffSource.ChartSmoothHolomorphicOn B g O) :
    ChartPowerSeriesOn n U O g := by
  intro c hc
  obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hc)
  let ρ := r / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hclosed : Metric.closedBall c ρ ⊆ O :=
    (Metric.closedBall_subset_ball (by dsimp [ρ]; linarith)).trans hrO
  let a : ℕ → Space n → ℂ := fun j x =>
    (cauchyPowerSeries (fun z => g z x) c ρ j) (fun _ => (1 : ℂ))
  have hcoef (B : LocalBall n) (hBU : Metric.closedBall B.center B.radius ⊆ U) (j : ℕ) :=
    ContourLift.coefficient_smooth_and_derivatives B O g (hball B hBU).1
      (ballJet_continuous B O g (hball B hBU)) c ρ hρ hclosed j
  refine ⟨ρ, hρ, Metric.ball_subset_closedBall.trans hclosed, a, ?_, ?_, ?_⟩
  · intro j x hx
    obtain ⟨B, hBx, hBU⟩ := closedContainedBall_at hn hU hx
    have hxB : x ∈ B.carrier := by rw [← hBx]; exact Metric.mem_ball_self B.radius_pos
    exact ((hcoef B hBU j).1.contDiffAt (Metric.isOpen_ball.mem_nhds hxB)).contDiffWithinAt
  · intro z hz
    exact hsmooth z (hclosed (Metric.ball_subset_closedBall hz))
  · intro L hL hLU m t ht htρ ε hε
    classical
    let Balls := {B : LocalBall n // Metric.closedBall B.center B.radius ⊆ U}
    have hcover : L ⊆ ⋃ B : Balls, Metric.ball B.val.center (B.val.radius / 2) := by
      intro x hx
      obtain ⟨B, hBx, hBU⟩ := closedContainedBall_at hn hU (hLU hx)
      apply Set.mem_iUnion.mpr
      refine ⟨⟨B, hBU⟩, ?_⟩
      rw [← hBx]
      exact Metric.mem_ball_self (half_pos B.radius_pos)
    obtain ⟨I, hI⟩ := hL.elim_finite_subcover
      (fun B : Balls => Metric.ball B.val.center (B.val.radius / 2))
      (fun _ => Metric.isOpen_ball) hcover
    have hlocal (B : Balls) : ∃ N : ℕ, ∀ M ≥ N, ∀ z ∈ Metric.closedBall c t,
        ∀ α : MultiIndex n m, ∀ x : ↥(L ∩ Metric.closedBall B.val.center (B.val.radius / 2)),
        ‖(∑ j ∈ Finset.range M, (z - c) ^ j * coordinateDerivative α (a j) x) -
          coordinateDerivative α (g z) x‖ < ε := by
      let K := L ∩ Metric.closedBall B.val.center (B.val.radius / 2)
      have hK : IsCompact K := hL.inter_right Metric.isClosed_closedBall
      have hKB : K ⊆ B.val.carrier := fun x hx =>
        Metric.closedBall_subset_ball (by linarith [B.val.radius_pos]) hx.2
      obtain ⟨N, hN⟩ := ContourLift.scalar_jet_cauchy_uniform B.val O g
        (hball B.val B.property).1 (ballJet_continuous B.val O g (hball B.val B.property))
        c ρ hρ hclosed (fun m α x hx =>
          (ballScalarJet_holomorphic B.val O g (hball B.val B.property) m α x hx).mono
            (Metric.ball_subset_closedBall.trans hclosed)) K hK hKB m t ht htρ ε hε
      refine ⟨N, ?_⟩
      intro M hM z hz α x
      have he : ∀ j, coordinateDerivative α (a j) x =
          (cauchyPowerSeries (fun w => coordinateDerivative α (g w) x) c ρ j) (fun _ => (1 : ℂ)) :=
        fun j => (hcoef B.val B.property j).2 m α (hKB x.property)
      simp_rw [he]
      exact hN M hM z hz α x
    choose N hN using hlocal
    refine ⟨I.sup N, ?_⟩
    intro M hM z hz α x
    obtain ⟨B, hBI, hxB⟩ := Set.mem_iUnion₂.mp (hI x.property)
    exact hN B M ((Finset.le_sup hBI).trans hM) z hz α
      ⟨x.val, x.property, Metric.ball_subset_closedBall hxB⟩

end BallwiseSeries

private theorem chartSmoothHolomorphicOn_congr {n : ℕ} (B : LocalBall n) {O : Set ℂ}
    {g g' : ℂ → Space n → ℂ} (h : ∀ s ∈ O, ∀ x, g s x = g' s x)
    (hg : KPCutoffSource.ChartSmoothHolomorphicOn B g' O) :
    KPCutoffSource.ChartSmoothHolomorphicOn B g O := by
  refine ⟨?_, ?_⟩
  · intro s hs
    rw [funext (h s hs)]
    exact hg.1 s hs
  · intro K hK hKB m
    obtain ⟨j, hj, hspec⟩ := hg.2 K hK hKB m
    exact ⟨j, hj, fun s hs α x => by
      rw [funext (h s hs)]; exact hspec s hs α x⟩

theorem pullback_chartPowerSeries
    (hΩ : IsOpen Ω)
    (hΩspectral : Ω ⊆ KPContinuation.spectralDomain)
    (hf : DifferentiableOn ℂ f Ω)
    (hι : Function.Injective ι)
    (hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (D : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι buffer Ω f χ)
    (q : Chart F ζ hζ C R P H U i) (b : Bool) :
    ChartPowerSeriesOn (dimension F) (chartDomain F ζ hζ C R P H U q) Ω
      (pullback F ζ hζ C R P H U ι buffer Ω f χ D q b) := by
  have hn : 0 < dimension F := by
    show 0 < KPContCotangentActualOverlap.d F * 3
    have hd : 0 < KPContCotangentActualOverlap.d F := by
      rw [KPContCotangentActualOverlap.d,
        (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.1.symm]
      exact (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.2
    positivity
  apply chartPowerSeries_of_ballwise (n := dimension F) hn
    (chartDomain_isOpen F ζ hζ C R P H U q) hΩ
    (pullback F ζ hζ C R P H U ι buffer Ω f χ D q b)
  · intro z _
    exact pullback_smooth F ζ hζ C R P H U ι buffer Ω f χ D q b z
  · intro B hB
    let term : KPContActualCutoffSmoothDescent.Cusps F ζ hζ C R P H U →
        ℂ → Space (dimension F) → ℂ := fun a s x =>
      (KPCuspGenuineMonodromy.chi F ζ hζ (q.splitting (coordinates F x)) : ℂ) *
        (KPContActualCutoffSmoothDescent.ends F ζ hζ C R P H U buffer a).indicator
          (fun y =>
            (if b then KPCutoffSource.incomingCommutatorMultiplier (Module.finrank ℚ F / 2)
                (χ a).toFun s
                (KPContActualCutoffSmoothDescent.height F ζ hζ C R P H U buffer a y)
              else (((χ a).toFun
                (KPContActualCutoffSmoothDescent.height F ζ hζ C R P H U buffer a y)) : ℂ)) *
            KPContActualCutoffSmoothDescent.incomingRealization F ζ hζ C R P H U ι buffer
              s (f s) y)
          (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
              (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U))
            (q.kind.representative • KPContCotangentActualOverlap.labeledA q.places
                (coordinates F x),
              (H.atlas (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)).representative i))
    have hg : ∀ a, KPCutoffSource.ChartSmoothHolomorphicOn B (term a) Ω := fun a =>
      KPContActualCutoffSmoothDescent.actual_incoming_cutoff_chart_jets
        F ζ hζ C R P H U ι buffer Ω hΩ hΩspectral f hf hι hStage χ a q b B hB
    refine chartSmoothHolomorphicOn_congr (B := B) (O := Ω)
      (g := pullback F ζ hζ C R P H U ι buffer Ω f χ D q b)
      (g' := fun s x => ∑ a, term a s x) (fun s hs x => ?_)
      (chartSmoothHolomorphic_finset_sum B Finset.univ term hg)
    rw [pullback_formula F ζ hζ C R P H U ι buffer Ω f χ D q b s hs x]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [KPContActualCutoffSmoothDescent.cutoffScalar, KPCutoffSource.cutoffSum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp only [term, Set.indicator_apply, Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte]
      rw [KPContActualCutoffSmoothDescent.commutatorScalar, KPCutoffSource.commutatorSum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp only [term, Set.indicator_apply, Bool.false_eq_true, ↓reduceIte]

theorem compact_jets_holomorphic
    (hΩ : IsOpen Ω)
    (hΩspectral : Ω ⊆ KPContinuation.spectralDomain)
    (hf : DifferentiableOn ℂ f Ω)
    (hι : Function.Injective ι)
    (hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (D : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι buffer Ω f χ)
    (q : Chart F ζ hζ C R P H U i) (b : Bool)
    (L : Set (Space (dimension F))) (hL : IsCompact L)
    (hLD : L ⊆ chartDomain F ζ hζ C R P H U q) (m : ℕ) :
    letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
    ∃ j : ℂ → CompactJets L m,
      DifferentiableOn ℂ j Ω ∧
      ∀ s ∈ Ω, ∀ α, ∀ x : L, j s α x = coordinateDerivative α
        (pullback F ζ hζ C R P H U ι buffer Ω f χ D q b s) x :=
  chartPowerSeries_compactJets (chartDomain_isOpen F ζ hζ C R P H U q) hΩ
    (pullback_chartPowerSeries F ζ hζ C R P H U ι buffer Ω f χ hΩ hΩspectral hf hι hStage D q b) L hL hLD m

structure Conclusions
    (D : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι buffer Ω f χ)
    (q : Chart F ζ hζ C R P H U i) (B : LocalBall (dimension F)) : Prop where
  smooth : ∀ b : Bool, ∀ s ∈ Ω,
    ContDiffOn ℝ (⊤ : ℕ∞)
      (pullback F ζ hζ C R P H U ι buffer Ω f χ D q b s)
      (chartDomain F ζ hζ C R P H U q)
  compact_jets : ∀ b : Bool, ∀ (L : Set (Space (dimension F))) (hL : IsCompact L),
    L ⊆ chartDomain F ζ hζ C R P H U q → ∀ m : ℕ,
      letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
      ∃ j : ℂ → CompactJets L m,
        DifferentiableOn ℂ j Ω ∧
        (∀ s ∈ Ω, ∀ α, ∀ x : L, j s α x = coordinateDerivative α
          (pullback F ζ hζ C R P H U ι buffer Ω f χ D q b s) x) ∧
        (∀ k : ℕ, ∀ (Q : Set ℂ), IsCompact Q → Q ⊆ Ω →
          ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Q, ‖iteratedDeriv k j s‖ ≤ M)
  on_ball : ∀ b : Bool, KPCutoffSource.ChartSmoothHolomorphicOn B
    (pullback F ζ hζ C R P H U ι buffer Ω f χ D q b) Ω

theorem Conclusions.of_compact_jets
    (hΩ : IsOpen Ω)
    (D : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι buffer Ω f χ)
    (q : Chart F ζ hζ C R P H U i) (B : LocalBall (dimension F))
    (hB : Metric.closedBall B.center B.radius ⊆ chartDomain F ζ hζ C R P H U q)
    (hj : ∀ b : Bool, ∀ (L : Set (Space (dimension F))) (hL : IsCompact L),
      L ⊆ chartDomain F ζ hζ C R P H U q → ∀ m : ℕ,
        letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
        ∃ j : ℂ → CompactJets L m, DifferentiableOn ℂ j Ω ∧
          ∀ s ∈ Ω, ∀ α, ∀ x : L, j s α x = coordinateDerivative α
            (pullback F ζ hζ C R P H U ι buffer Ω f χ D q b s) x) :
    Conclusions F ζ hζ C R P H U ι buffer Ω f χ D q B := by
  have hB' : B.carrier ⊆ chartDomain F ζ hζ C R P H U q :=
    Metric.ball_subset_closedBall.trans hB
  refine ⟨fun b s _ => pullback_smooth F ζ hζ C R P H U ι buffer Ω f χ D q b s, ?_, ?_⟩
  · intro b L hL hLD m
    letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
    obtain ⟨j, hhol, heq⟩ := hj b L hL hLD m
    exact ⟨j, hhol, heq, fun k Q hQ hQΩ => parameter_derivatives_bounded hΩ hhol k hQ hQΩ⟩
  · intro b
    refine ⟨fun s _ => (pullback_smooth F ζ hζ C R P H U ι buffer Ω f χ D q b s).mono hB', ?_⟩
    intro L hL hLB m
    exact hj b L hL (hLB.trans hB') m

end DedekindZetaZeroFree.KPContActualCutoffChartJetHolomorphy

namespace DedekindZetaZeroFree

theorem kp_cont_actual_cutoff_chart_jet_holomorphy
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (_hR : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H)
    {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U) R P H T)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (_hι : Function.Injective ι)
    (_hStage : KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι)
    (Ω : Set ℂ) (_hΩ : Ω ⊆ KPContinuation.spectralDomain) (_hopen : IsOpen Ω)
    (f : ℂ → S) (_hf : DifferentiableOn ℂ f Ω)
    (χ : KPContActualCutoffSmoothDescent.Cusps F ζ hζ C R P H U →
      KPCutoffSource.SmoothCuspCutoff T) :
    ∀ D : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι buffer Ω f χ,
    ∀ i : Fin (H.atlas (KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U)).componentCount,
    ∀ q : KPContActualCutoffChartJetHolomorphy.Chart F ζ hζ C R P H U i,
    ∀ B : KPContLocalNorm.LocalBall (KPContActualCutoffChartJetHolomorphy.dimension F),
      Metric.closedBall B.center B.radius ⊆
        KPContActualCutoffChartJetHolomorphy.chartDomain F ζ hζ C R P H U q →
      KPContActualCutoffChartJetHolomorphy.Conclusions F ζ hζ C R P H U
        ι buffer Ω f χ D q B := by
  intro D i q B hB
  apply KPContActualCutoffChartJetHolomorphy.Conclusions.of_compact_jets
    F ζ hζ C R P H U ι buffer Ω f χ _hopen D q B hB
  intro b L hL hLD m

  exact KPContActualCutoffChartJetHolomorphy.compact_jets_holomorphic
    F ζ hζ C R P H U ι buffer Ω f χ _hopen _hΩ _hf _hι _hStage D q b L hL hLD m

end DedekindZetaZeroFree

end

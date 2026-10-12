module

public import DedekindZetaZeroFree.Eisenstein.Sections.FlatRightWordJets
public import DedekindZetaZeroFree.Analysis.RightFrame.PullbackWords
public import DedekindZetaZeroFree.Eisenstein.Induction.SphericalFlatSection
public import DedekindZetaZeroFree.Eisenstein.Continuation.RationalSummands.MixedJets

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators Topology ContDiff Matrix Matrix.Norms.Operator

namespace DedekindZetaZeroFree.KPContinuation.ChamberNormalTerm

open KPContActualChamberNormalSeries

section ParameterSource

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
  {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
  (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
  (f : ℂ → S)

theorem actual_parameterTerm_formula
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (q : Q F) (k : ℕ) (s : ℂ) (hs : s ∈ V) (g : G F ζ hζ) :
    mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] s g =
      ∑ i : Fin (Module.finrank ℂ S), ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℂ) *
        iteratedDerivWithin j (fun z => (Module.finBasis ℂ S).repr (f z) i) V s *
        KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
          (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι)
          (k - j) s ((Module.finBasis ℂ S) i) (lift F ζ hζ q * g) := by
  let B := Module.finBasis ℂ S
  let α := fun g : G F ζ hζ => (KPContFlatSourceRecipe.alpha F ζ hζ (lift F ζ hζ q * g) : ℂ)
  let c := fun i : Fin (Module.finrank ℂ S) => fun z : ℂ => B.repr (f z) i
  let v := fun i : Fin (Module.finrank ℂ S) => fun g : G F ζ hζ =>
    KPContActualSphericalFlatStage.L F ζ hζ U ι 0 (B i) (lift F ζ hζ q * g)
  have hVΩ : V ⊆ KPContinuation.spectralDomain := by
    intro z hz; change -(1 : ℝ)/6 < z.re; change (1 : ℝ)/3 < z.re at hz; linarith
  have hc : ∀ i, ContDiffOn ℂ (⊤ : WithTop ℕ∞) (c i) V := by
    intro i
    exact ((⟨B.coord i, (B.coord i).continuous_of_finiteDimensional⟩ : S →L[ℂ] ℂ).differentiable.comp_differentiableOn
      (hf.mono hVΩ)).contDiffOn KPChamberL2Defect.chamber_isOpen
  have heq : (fun z => term F ζ hζ U ι f q z g) =
      fun z => ∑ i, (c i z * Complex.exp (α g * z)) * v i g := by
    funext z
    unfold term
    conv_lhs => rw [← B.sum_repr (f z)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [c, v, α, KPContFlatCommonLevelKernel.L_formula, zero_mul, Complex.exp_zero, one_mul]
    rw [mul_comm z]
    ring
  change iteratedDerivWithin k (fun z => term F ζ hζ U ι f q z g) V s = _
  have hsum : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℂ S))),
      ContDiffWithinAt ℂ (k : WithTop ℕ∞) (fun z => (c i z * Complex.exp (α g*z)) * v i g) V s := by
    intro i _
    exact ((hc i s hs).of_le (by simp)).mul (by fun_prop) |>.mul contDiffWithinAt_const
  rw [heq, iteratedDerivWithin_fun_sum hs KPChamberL2Defect.chamber_isOpen.uniqueDiffOn hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDerivWithin_mul_const_field]
  change iteratedDerivWithin k (c i * (fun z => Complex.exp (α g*z))) V s * _ = _
  rw [iteratedDerivWithin_mul hs KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
    ((hc i s hs).of_le (by simp)) (by fun_prop), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [iteratedDerivWithin_of_isOpen KPChamberL2Defect.chamber_isOpen hs,
    iteratedDeriv_cexp_const_mul]
  change _ = (k.choose j : ℂ) * iteratedDeriv j (c i) s *
    KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
      (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι) (k-j) s (B i) _
  simp only [KPContFlatStageJetHolomorphy.parameterSection,
    KPContFlatStageJetHolomorphy.L, KPContFlatCommonLevelKernel.L_formula, v,
    zero_mul, Complex.exp_zero, one_mul]
  change _ = _ * (α g ^ (k-j) * (Complex.exp (s * α g) * _))
  rw [mul_comm s]
  change _ = _ * (α g ^ (k-j) * (Complex.exp (α g * s) *
    (ι (B i)).val.val.val (lift F ζ hζ q * g)))
  ring

theorem actual_parameterSection_right_chart_smooth
    (m : ℕ) (s : ℂ) (v : S) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
        (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι) m s v
        (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archDomain F) := by
  apply contDiffOn_of_locally_contDiffOn
  intro x₀ hx₀
  obtain ⟨O, q, hO, hxO, hq, hqO, heq⟩ :=
    KPLiteralChamber.literal_right_to_left_chart_local_transition F ζ hζ g x₀ hx₀
  refine ⟨O, hO, hxO, ?_⟩
  have hleft := KPContFlatStageJetHolomorphy.parameterSection_contDiffOn F ζ hζ
    (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι)
    (KPContActualSphericalFlatStage.stage_smooth F ζ hζ U ι)
    (g * KPGlobalResidualConstruction.archChart F ζ hζ x₀) m s v
  have hc := hleft.comp hq hqO
  apply (hc.congr (fun x hx => congrArg
    (KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
      (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι) m s v)
    (heq x hx))).mono
  exact Set.inter_subset_right

theorem actual_parameterTerm_right_chart_smooth
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (q : Q F) (k : ℕ) (s : ℂ) (hs : s ∈ V) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] s
        (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archDomain F) := by
  simp_rw [actual_parameterTerm_formula F ζ hζ U ι f hf q k s hs]
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  apply contDiffOn_const.mul
  simpa only [mul_assoc] using
    actual_parameterSection_right_chart_smooth F ζ hζ U ι (k-j) s
      ((Module.finBasis ℂ S) i) (lift F ζ hζ q * g)

theorem actual_parameterSection_level (m : ℕ) (s : ℂ) (v : S)
    (g : G F ζ hζ) (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U) :
    KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
      (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι) m s v (g*u.val) =
    KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
      (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι) m s v g := by
  have hc := (ι v).property.1 g u
  change (KPContFlatSourceRecipe.alpha F ζ hζ (g*u.val) : ℂ)^m *
      KPContActualSphericalFlatStage.L F ζ hζ U ι s v (g*u.val) =
    (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ)^m *
      KPContActualSphericalFlatStage.L F ζ hζ U ι s v g
  rw [KPContFlatCommonLevelKernel.L_formula, KPContFlatCommonLevelKernel.L_formula, hc.1]
  rcases mul_eq_zero.mp hc.2 with ha | hz
  · have he : KPContFlatSourceRecipe.alpha F ζ hζ (g*u.val) =
        KPContFlatSourceRecipe.alpha F ζ hζ g := sub_eq_zero.mp (Complex.ofReal_eq_zero.mp ha)
    rw [he]
  · rw [hz]
    simp

theorem actual_parameterTerm_level
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (q : Q F) (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (g : G F ζ hζ) (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U) :
    mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] s (g*u.val) =
      mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] s g := by
  simp_rw [actual_parameterTerm_formula F ζ hζ U ι f hf q k s hs, ← mul_assoc,
    actual_parameterSection_level F ζ hζ U ι]

end ParameterSource

namespace PositiveChart
open Filter
open KPGlobalResidualConstruction
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def flowMatrix (b : KPSmoothActualFlowData.B F) (t : ℝ)
    (v : NumberField.InfinitePlace F) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KPSmoothActualFlowData.matrixExponential
    (KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = b then t else 0))
 def theta (b : KPSmoothActualFlowData.B F) (t : ℝ) : ArchCoordinates F :=
  fun v => KPContinuation.ChamberFlatSource.ChartMatrix.chartCoordinates (flowMatrix F b t v).val
private theorem flowMatrix_zero (b : KPSmoothActualFlowData.B F) (v : NumberField.InfinitePlace F) :
    flowMatrix F b 0 v = 1 := by
  apply Units.ext
  change (NormedSpace.exp _) = (1 : Matrix (Fin 2) (Fin 2) ℂ)
  rw [show KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = b then (0 : ℝ) else 0) = 0 by
    ext i j; fin_cases i <;> fin_cases j <;> simp [KPSmoothActualFlowData.sl2Matrix]]
  exact NormedSpace.exp_zero
private theorem theta_zero (b : KPSmoothActualFlowData.B F) : theta F b 0 = archBase F := by
  funext v i
  rw [theta, flowMatrix_zero]
  fin_cases i <;> simp [KPContinuation.ChamberFlatSource.ChartMatrix.chartCoordinates, archBase]
private theorem flowEntry_smooth (b : KPSmoothActualFlowData.B F)
    (v : NumberField.InfinitePlace F) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val i j) := by
  letI : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAlgebra
  let L : ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    { toFun := fun t => KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = b then t else 0)
      map_add' := by intro x y; ext i j; fin_cases i <;> fin_cases j <;>
        simp [KPSmoothActualFlowData.sl2Matrix]; all_goals split_ifs <;> simp <;> ring
      map_smul' := by intro x y; ext i j; fin_cases i <;> fin_cases j <;>
        simp [KPSmoothActualFlowData.sl2Matrix]; all_goals split_ifs <;> simp <;> ring }
  let ev : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have he : ContDiff ℝ (⊤ : ℕ∞) (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → _) :=
    (show AnalyticOnNhd ℝ (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → _) Set.univ from fun _ _ => NormedSpace.exp_analytic _).contDiff
  exact ev.toContinuousLinearMap.contDiff.comp (he.comp L.toContinuousLinearMap.contDiff)

private theorem theta_smooth (b : KPSmoothActualFlowData.B F) :
    ContDiffAt ℝ (⊤ : ℕ∞) (theta F b) 0 := by
  apply contDiffAt_pi.mpr; intro v
  apply contDiffAt_pi.mpr; intro i
  have hc (i j : Fin 2) : ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val i j) 0 :=
    (flowEntry_smooth F b v i j).contDiffAt
  have hn : (flowMatrix F b 0 v).val 1 1 ≠ 0 := by rw [flowMatrix_zero]; simp
  fin_cases i <;> simp only [theta, KPContinuation.ChamberFlatSource.ChartMatrix.chartCoordinates, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  · change ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val 0 1 / (flowMatrix F b t v).val 1 1) 0
    simpa only [div_eq_mul_inv] using! (hc 0 1).mul ((hc 1 1).inv hn)
  · change ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val.det / (flowMatrix F b t v).val 1 1 ^ 2) 0
    simp only [Matrix.det_fin_two]
    simpa only [div_eq_mul_inv] using! (((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))).mul
      (((hc 1 1).pow 2).inv (pow_ne_zero _ hn))
  · change ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val 1 0 / (flowMatrix F b t v).val 1 1) 0
    simpa only [div_eq_mul_inv] using! (hc 1 0).mul ((hc 1 1).inv hn)
private theorem theta_chart (b : KPSmoothActualFlowData.B F) :
    ∀ᶠ t in nhds (0 : ℝ), KPGlobalResidualConstruction.archChart F ζ hζ (theta F b t) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t) := by
  have hn : ∀ᶠ t in nhds (0 : ℝ), ∀ v : NumberField.InfinitePlace F,
      (flowMatrix F b t v).val 1 1 ≠ 0 := by
    rw [Filter.eventually_all]
    intro v
    have hc : ContinuousAt (fun t => (flowMatrix F b t v).val 1 1) 0 :=
      (flowEntry_smooth F b v 1 1).continuous.continuousAt
    exact hc.eventually_ne (by rw [flowMatrix_zero]; simp)
  filter_upwards [hn] with t ht
  rw [KPContinuation.ChamberFlatSource.ChartMatrix.archChart_eq_insertion_chartMatrix]
  congr 1
  funext v
  exact KPContinuation.ChamberFlatSource.ChartMatrix.chartCoordinates_reconstruct (flowMatrix F b t v) (ht v)
 def chartProduct (p : ArchCoordinates F × ArchCoordinates F) : ArchCoordinates F := fun q =>
  ![p.1 q 0 + p.1 q 1 * p.2 q 0 / (1 + p.1 q 2 * p.2 q 0),
    p.1 q 1 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)^2,
    p.2 q 2 + p.1 q 2 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)]
private theorem chartProduct_base_right (x : ArchCoordinates F) :
    chartProduct F (x,archBase F) = x := by
  funext q i
  fin_cases i <;> simp [chartProduct, archBase]
 def transport (b : KPSmoothActualFlowData.B F) (p : ArchCoordinates F × ℝ) : ArchCoordinates F :=
  chartProduct F (p.1, theta F b p.2)
 def field (b : KPSmoothActualFlowData.B F) (x : ArchCoordinates F) : ArchCoordinates F :=
  fderiv ℝ (transport F b) (x,0) (0,1)
private theorem transport_zero (b : KPSmoothActualFlowData.B F) (x : ArchCoordinates F) :
    transport F b (x,0) = x := by
  simp [transport, theta_zero, chartProduct_base_right]
private theorem transport_smooth (b : KPSmoothActualFlowData.B F)
    (V : Set (ArchCoordinates F)) (hVo : IsOpen V) (hb : archBase F ∈ V)
    (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (V ×ˢ V)) (x : ArchCoordinates F) (hx : x ∈ V) :
    ContDiffAt ℝ (⊤ : ℕ∞) (transport F b) (x,0) := by
  have hpair : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ArchCoordinates F × ℝ => (p.1,theta F b p.2)) (x,0) :=
    contDiffAt_fst.prodMk ((theta_smooth F b).comp (x,0) contDiffAt_snd)
  exact (hμ.contDiffAt ((hVo.prod hVo).mem_nhds ⟨hx, by simpa [theta_zero] using hb⟩)).comp (x,0) hpair
private theorem field_smooth (b : KPSmoothActualFlowData.B F)
    (V : Set (ArchCoordinates F)) (hVo : IsOpen V) (hb : archBase F ∈ V)
    (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (V ×ˢ V)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (field F b) V := by
  intro x hx
  have ht := transport_smooth F b V hVo hb hμ x hx
  have hd := (ht.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).comp x
    (contDiffAt_id.prodMk contDiffAt_const)
  exact (hd.clm_apply contDiffAt_const).contDiffWithinAt
private theorem transport_hasDeriv (b : KPSmoothActualFlowData.B F)
    (V : Set (ArchCoordinates F)) (hVo : IsOpen V) (hb : archBase F ∈ V)
    (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (V ×ˢ V)) (x : ArchCoordinates F) (hx : x ∈ V) :
    HasDerivAt (fun t => transport F b (x,t)) (field F b x) 0 := by
  have ht := (transport_smooth F b V hVo hb hμ x hx).differentiableAt (by simp)
  exact ht.hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_const 0 x).prodMk (hasDerivAt_id 0))

 def coordWord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} (fields : ι → E → E) : List ι → (E → ℂ) → E → ℂ
  | [], u => u
  | b :: w, u => fun x => fderiv ℝ (coordWord fields w u) x (fields b x)
private theorem coordWord_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} (fields : ι → E → E) (U : Set E)
    (hU : IsOpen U) (hf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (w : List ι) (u : E → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordWord fields w u) U := by
  induction w with
  | nil => exact hu
  | cons b w ih => exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply (hf b)

private theorem scalar_word_in_chart
    (u : KPContActualChamberNormalSeries.G F ζ hζ → ℂ)
    (huAll : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (V : Set (ArchCoordinates F)) (hVo : IsOpen V) (hb : archBase F ∈ V)
    (hVD : V ⊆ archDomain F)
    (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (V ×ˢ V))
    (hprod : ∀ y ∈ V, ∀ x ∈ V, archChart F ζ hζ (chartProduct F (y,x)) =
      archChart F ζ hζ y * archChart F ζ hζ x)
    (w : List (KPSmoothActualFlowData.B F)) (g : KPContActualChamberNormalSeries.G F ζ hζ) :
    ∀ x ∈ V,
      w.foldr (fun b v => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 v)
        (u) (g * archChart F ζ hζ x) =
      coordWord (field F) w (fun y => u (g * archChart F ζ hζ y)) x := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => u (g * archChart F ζ hζ y)) V :=
    (huAll g).mono hVD
  have hf := fun b => field_smooth F b V hVo hb hμ
  induction w with
  | nil => intro x hx; rfl
  | cons b w ih =>
    intro x hx
    let u₀ := fun y => u (g * archChart F ζ hζ y)
    let q := coordWord (field F) w u₀
    have hq : ContDiffOn ℝ (⊤ : ℕ∞) q V := coordWord_smooth (field F) V hVo hf w u₀ hu
    have hqt := ((hq.contDiffAt (hVo.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have htr := transport_hasDeriv F b V hVo hb hμ x hx
    have htr0 := transport_zero F b x
    have hder : HasDerivAt (fun t => q (transport F b (x,t)))
        (fderiv ℝ q x (field F b x)) 0 := by
      have hh := (show HasFDerivAt q (fderiv ℝ q x) (transport F b (x,0)) from htr0.symm ▸ hqt).comp_hasDerivAt 0 htr
      simpa only [htr0, Function.comp_def] using! hh
    have he : (fun t : ℝ =>
        w.foldr (fun b v => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 v)
          (u) ((g * archChart F ζ hζ x) *
            KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t)))
        =ᶠ[nhds 0] (fun t => q (transport F b (x,t))) := by
      have htV : ∀ᶠ t in nhds (0 : ℝ), theta F b t ∈ V :=
        (theta_smooth F b).continuousAt.eventually (by simpa [theta_zero] using hVo.mem_nhds hb)
      have hpV : ∀ᶠ t in nhds (0 : ℝ), transport F b (x,t) ∈ V :=
        htr.continuousAt.eventually (by simpa only [htr0] using (show ∀ᶠ y in nhds x, y ∈ V from hVo.mem_nhds hx))
      filter_upwards [theta_chart F ζ hζ b, htV, hpV] with t ht htV hpV
      rw [← ht, mul_assoc, ← hprod x hx (theta F b t) htV]
      exact ih (transport F b (x,t)) hpV
    change deriv _ 0 = fderiv ℝ q x (field F b x)
    rw [he.deriv_eq]
    exact hder.deriv

theorem rightWord_hasDerivAt_of_chart_smooth
    (u : KPContActualChamberNormalSeries.G F ζ hζ → ℂ)
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (w : Word F) (b : KPSmoothActualFlowData.B F) (g : KPContActualChamberNormalSeries.G F ζ hζ) :
    HasDerivAt (fun t : ℝ => rightWord F ζ hζ w u
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F b t)))
      (rightWord F ζ hζ (b :: w) u g) 0 := by
  obtain ⟨O, hOo, hb, hOD, hμ, hmaps, hprod, hthick, hcomm⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product F ζ hζ
  change ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (O ×ˢ O) at hμ
  change ∀ y ∈ O, ∀ x ∈ O, archChart F ζ hζ (chartProduct F (y,x)) =
    archChart F ζ hζ y * archChart F ζ hζ x at hprod
  let q := coordWord (field F) w (fun y => u (g * archChart F ζ hζ y))
  have hq : ContDiffOn ℝ (⊤ : ℕ∞) q O :=
    coordWord_smooth (field F) O hOo (fun b => field_smooth F b O hOo hb hμ)
      w _ ((hu g).mono hOD)
  have hθ := theta_smooth F b
  have hθO : ∀ᶠ t in nhds (0 : ℝ), theta F b t ∈ O :=
    hθ.continuousAt.eventually (by simpa [theta_zero] using hOo.mem_nhds hb)
  have he : (fun t : ℝ => rightWord F ζ hζ w u
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F b t))) =ᶠ[nhds 0]
      (fun t => q (theta F b t)) := by
    filter_upwards [theta_chart F ζ hζ b, hθO] with t ht htO
    rw [← ht]
    exact scalar_word_in_chart F ζ hζ u hu O hOo hb hOD hμ hprod w g _ htO
  have hd : DifferentiableAt ℝ (fun t => q (theta F b t)) 0 := by
    exact (((hq.contDiffAt (by simpa [theta_zero] using hOo.mem_nhds hb)).comp 0 hθ).differentiableAt (by simp))
  have hd' := hd.congr_of_eventuallyEq he
  exact hd'.hasDerivAt

theorem rightWord_level
    (u : KPContActualChamberNormalSeries.G F ζ hζ → ℂ)
    (a : KPContActualChamberNormalSeries.G F ζ hζ)
    (ha : ∀ x, Commute (archChart F ζ hζ x) a)
    (hu : ∀ g, u (g*a) = u g) (w : Word F)
    (g : KPContActualChamberNormalSeries.G F ζ hζ) :
    rightWord F ζ hζ w u (g*a) = rightWord F ζ hζ w u g := by
  induction w generalizing g with
  | nil => exact hu g
  | cons b w ih =>
    change deriv _ 0 = deriv _ 0
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [theta_chart F ζ hζ b] with t ht
    rw [← ht, mul_assoc, (ha (theta F b t)).eq.symm, ← mul_assoc]
    exact ih _

theorem rightWord_continuous_of_chart_smooth
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (u : KPContActualChamberNormalSeries.G F ζ hζ → ℂ)
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (hlevel : ∀ g, ∀ a : KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
      u (g*a.val) = u g) (w : Word F) :
    Continuous (rightWord F ζ hζ w u) := by
  letI : IsTopologicalGroup (KPContActualChamberNormalSeries.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨O, hOo, hb, hOD, hμ, hmaps, hprod, hthick, hcomm⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product F ζ hζ
  change ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (O ×ˢ O) at hμ
  change ∀ y ∈ O, ∀ x ∈ O, archChart F ζ hζ (chartProduct F (y,x)) =
    archChart F ζ hζ y * archChart F ζ hζ x at hprod
  apply continuous_iff_continuousAt.mpr
  intro g
  let q := coordWord (field F) w (fun y => u (g * archChart F ζ hζ y))
  have hq : ContDiffOn ℝ (⊤ : ℕ∞) q O :=
    coordWord_smooth (field F) O hOo (fun b => field_smooth F b O hOo hb hμ)
      w _ ((hu g).mono hOD)
  have hbase : q (archBase F) = rightWord F ζ hζ w u g := by
    have hh := scalar_word_in_chart F ζ hζ u hu O hOo hb hOD hμ hprod w g _ hb
    simpa only [KPInterface.ResidueConstruction.Raw.archChart_base, mul_one, rightWord, q] using hh.symm
  apply tendsto_def.mpr
  intro N hN
  have hn : q ⁻¹' N ∈ nhds (archBase F) :=
    (hq.continuousOn.continuousAt (hOo.mem_nhds hb)).preimage_mem_nhds (hbase.symm ▸ hN)
  obtain ⟨W, hWN, hWo, hbW⟩ := mem_nhds_iff.mp (Filter.inter_mem hn (hOo.mem_nhds hb))
  have hWO : W ⊆ O := fun x hx => (hWN hx).2
  have hT := hthick W hWo hbW hWO U
  change ∀ᶠ y in nhds (1 : KPContActualChamberNormalSeries.G F ζ hζ),
    ∃ x ∈ W, ∃ a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
      y = archChart F ζ hζ x * a at hT
  have hg : ∀ᶠ y in nhds g, ∃ x ∈ W,
      ∃ a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
        g⁻¹*y = archChart F ζ hζ x * a :=
    (show ContinuousAt (fun y : KPContActualChamberNormalSeries.G F ζ hζ => g⁻¹*y) g from
      continuousAt_const.mul continuousAt_id).eventually (by simpa using hT)
  filter_upwards [hg] with y hy
  obtain ⟨x, hx, a, ha, he⟩ := hy
  have hy' : y = (g * archChart F ζ hζ x)*a := by
    calc y = g*(g⁻¹*y) := by simp
         _ = _ := by rw [he, mul_assoc]
  change rightWord F ζ hζ w u y ∈ N
  rw [hy', rightWord_level F ζ hζ u a (fun x => hcomm U a ha x)
    (fun g => hlevel g ⟨a,ha⟩) w]
  change w.foldr (fun b v => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 v) u
    (g * archChart F ζ hζ x) ∈ N
  rw [scalar_word_in_chart F ζ hζ u hu O hOo hb hOD hμ hprod w g x (hWO hx)]
  exact (hWN hx).1

theorem rightWord_chart_realization :
    ∃ (O : Set (ArchCoordinates F)) (fields : KPSmoothActualFlowData.B F → ArchCoordinates F → ArchCoordinates F),
      IsOpen O ∧ archBase F ∈ O ∧ O ⊆ archDomain F ∧
      (∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) O) ∧
      ∀ (u : KPContActualChamberNormalSeries.G F ζ hζ → ℂ),
        (∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
          (fun x => u (g * archChart F ζ hζ x)) (archDomain F)) →
        ∀ (w : Word F) (g : KPContActualChamberNormalSeries.G F ζ hζ) (x : ArchCoordinates F),
          x ∈ O → rightWord F ζ hζ w u (g * archChart F ζ hζ x) =
            RightFrame.PullbackWords.directionalWord fields w
              (fun y => u (g * archChart F ζ hζ y)) x := by
  obtain ⟨O, hOo, hb, hOD, hμ, hmaps, hprod, hthick, hcomm⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product F ζ hζ
  change ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (O ×ˢ O) at hμ
  change ∀ y ∈ O, ∀ x ∈ O, archChart F ζ hζ (chartProduct F (y,x)) =
    archChart F ζ hζ y * archChart F ζ hζ x at hprod
  refine ⟨O, field F, hOo, hb, hOD, fun b => field_smooth F b O hOo hb hμ, ?_⟩
  intro u hu w g x hx
  have he : coordWord (field F) w = RightFrame.PullbackWords.directionalWord (field F) w := by
    induction w with
    | nil => rfl
    | cons b w ih => simp only [coordWord, RightFrame.PullbackWords.directionalWord, ih]
  rw [← he]
  exact scalar_word_in_chart F ζ hζ u hu O hOo hb hOD hμ hprod w g x hx

end PositiveChart

theorem actual_parameterTerm_word_flow
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (f : ℂ → S) (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (q : Q F) (k : ℕ) (w : Word F) (s : ℂ) (hs : s ∈ V)
    (b : KPSmoothActualFlowData.B F) (g : G F ζ hζ) :
    HasDerivAt (fun t : ℝ => mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F b t)))
      (mixedJet F ζ hζ (term F ζ hζ U ι f q) k (b :: w) s g) 0 := by
  exact PositiveChart.rightWord_hasDerivAt_of_chart_smooth F ζ hζ
    (mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] s)
    (actual_parameterTerm_right_chart_smooth F ζ hζ U ι f hf q k s hs) w b g

theorem actual_term_mixed_flow
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (f : ℂ → S) (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (q : Q F) (k : ℕ) (w : Word F) (s : ℂ) (hs : s ∈ V) :
    Continuous (mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s) ∧
    ∀ (b : KPSmoothActualFlowData.B F) (g : G F ζ hζ),
      HasDerivAt
        (fun t : ℝ => mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s
          (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t)))
        (mixedJet F ζ hζ (term F ζ hζ U ι f q) k (b :: w) s g) 0 := by
  constructor
  · exact PositiveChart.rightWord_continuous_of_chart_smooth F ζ hζ U
      (mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] s)
      (actual_parameterTerm_right_chart_smooth F ζ hζ U ι f hf q k s hs)
      (actual_parameterTerm_level F ζ hζ U ι f hf q k s hs) w
  · exact actual_parameterTerm_word_flow F ζ hζ U ι f hf q k w s hs

end DedekindZetaZeroFree.KPContinuation.ChamberNormalTerm

end

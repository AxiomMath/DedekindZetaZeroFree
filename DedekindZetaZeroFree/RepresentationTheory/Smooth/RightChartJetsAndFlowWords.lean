module

public import DedekindZetaZeroFree.Adeles.Approximation.ArchimedeanChartMultiplication
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.UpperAndLowerBigCellTransitions
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.UpperAndLowerBigCellTransitions

@[expose] public section

noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ContDiff Matrix Matrix.Norms.Operator

namespace DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

open Filter KPGlobalResidualConstruction
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def word : List (KPSmoothActualFlowData.B F) →
    (KPGlobalTorusFunctionData.G F ζ hζ → ℂ) → KPGlobalTorusFunctionData.G F ζ hζ → ℂ
  | [], u => u
  | b :: w, u => fun g => deriv (fun t : ℝ => word w u
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F b t))) 0

 def flowMatrix (b : KPSmoothActualFlowData.B F) (t : ℝ)
    (v : NumberField.InfinitePlace F) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KPSmoothActualFlowData.matrixExponential
    (KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = b then t else 0))
 def theta (b : KPSmoothActualFlowData.B F) (t : ℝ) : ArchCoordinates F :=
  fun v => KPLiteralChamber.rightCoordinates (flowMatrix F b t v).val
private theorem flowMatrix_zero (b : KPSmoothActualFlowData.B F) (v : NumberField.InfinitePlace F) :
    flowMatrix F b 0 v = 1 := by
  apply Units.ext
  change (NormedSpace.exp _) = (1 : Matrix (Fin 2) (Fin 2) ℂ)
  rw [show KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = b then (0 : ℝ) else 0) = 0 by
    ext i j; fin_cases i <;> fin_cases j <;> simp [KPSmoothActualFlowData.sl2Matrix]]
  exact NormedSpace.exp_zero
 theorem theta_zero (b : KPSmoothActualFlowData.B F) : theta F b 0 = archBase F := by
  funext v i
  rw [theta, flowMatrix_zero]
  fin_cases i <;> simp [KPLiteralChamber.rightCoordinates, archBase]
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
 theorem theta_smooth (b : KPSmoothActualFlowData.B F) :
    ContDiffAt ℝ (⊤ : ℕ∞) (theta F b) 0 := by
  apply contDiffAt_pi.mpr; intro v
  apply contDiffAt_pi.mpr; intro i
  have hc (i j : Fin 2) : ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val i j) 0 :=
    (flowEntry_smooth F b v i j).contDiffAt
  have hn : (flowMatrix F b 0 v).val 1 1 ≠ 0 := by rw [flowMatrix_zero]; simp
  fin_cases i <;> simp only [theta, KPLiteralChamber.rightCoordinates, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  · change ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val 0 1 / (flowMatrix F b t v).val 1 1) 0
    simpa only [div_eq_mul_inv] using! (hc 0 1).mul ((hc 1 1).inv hn)
  · change ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val.det / (flowMatrix F b t v).val 1 1 ^ 2) 0
    simp only [Matrix.det_fin_two]
    simpa only [div_eq_mul_inv] using! (((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))).mul
      (((hc 1 1).pow 2).inv (pow_ne_zero _ hn))
  · change ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t v).val 1 0 / (flowMatrix F b t v).val 1 1) 0
    simpa only [div_eq_mul_inv] using! (hc 1 0).mul ((hc 1 1).inv hn)
 theorem theta_chart (b : KPSmoothActualFlowData.B F) :
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
  rw [KPLiteralChamber.right_insertion]
  congr 1
  funext v
  exact KPLiteralChamber.rightCoordinates_reconstruct (flowMatrix F b t v) (ht v)
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
    (u : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (huAll : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (V : Set (ArchCoordinates F)) (hVo : IsOpen V) (hb : archBase F ∈ V)
    (hVD : V ⊆ archDomain F)
    (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (V ×ˢ V))
    (hprod : ∀ y ∈ V, ∀ x ∈ V, archChart F ζ hζ (chartProduct F (y,x)) =
      archChart F ζ hζ y * archChart F ζ hζ x)
    (w : List (KPSmoothActualFlowData.B F)) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ∀ x ∈ V,
      word F ζ hζ w u (g * archChart F ζ hζ x) =
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
        word F ζ hζ w u ((g * archChart F ζ hζ x) *
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
    (u : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (w : List (KPSmoothActualFlowData.B F)) (b : KPSmoothActualFlowData.B F) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    HasDerivAt (fun t : ℝ => word F ζ hζ w u
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F b t)))
      (word F ζ hζ (b :: w) u g) 0 := by
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
  have he : (fun t : ℝ => word F ζ hζ w u
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

 theorem word_add (u v : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (hv : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => v (g * archChart F ζ hζ x)) (archDomain F))
    (w : List (KPSmoothActualFlowData.B F)) :
    word F ζ hζ w (u + v) = word F ζ hζ w u + word F ζ hζ w v := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    funext g
    change deriv _ 0 = _
    simp only [ih, Pi.add_apply]
    exact ((rightWord_hasDerivAt_of_chart_smooth F ζ hζ u hu w b g).add
      (rightWord_hasDerivAt_of_chart_smooth F ζ hζ v hv w b g)).deriv

 theorem word_smul (c : ℂ) (u : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (w : List (KPSmoothActualFlowData.B F)) :
    word F ζ hζ w (c • u) = c • word F ζ hζ w u := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    funext g
    change deriv _ 0 = _
    simp only [ih, Pi.smul_apply]
    exact ((rightWord_hasDerivAt_of_chart_smooth F ζ hζ u hu w b g).const_smul c).deriv

end DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets

end

section

noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ContDiff Matrix Matrix.Norms.Operator

namespace DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

open Filter KPGlobalResidualConstruction
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem rightWord_level
    (u : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (a : KPGlobalTorusFunctionData.G F ζ hζ)
    (ha : ∀ x, Commute (archChart F ζ hζ x) a)
    (hu : ∀ g, u (g*a) = u g) (w : List (KPSmoothActualFlowData.B F))
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    word F ζ hζ w u (g*a) = word F ζ hζ w u g := by
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
    (u : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (hlevel : ∀ g, ∀ a : KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
      u (g*a.val) = u g) (w : List (KPSmoothActualFlowData.B F)) :
    Continuous (word F ζ hζ w u) := by
  letI : IsTopologicalGroup (KPGlobalTorusFunctionData.G F ζ hζ) :=
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
  have hbchart : archChart F ζ hζ (archBase F) = 1 := by
    rw [KPLiteralChamber.right_insertion]
    have hh : (fun v : NumberField.InfinitePlace F => Matrix.ProjGenLinGroup.mk
        (KPLiteralChamber.rightMatrix (archBase F v))) = 1 := by
      funext v
      have hm : KPLiteralChamber.rightMatrix (archBase F v) = 1 := by
        apply Units.ext
        rw [KPLiteralChamber.rightMatrix_val _ (by simp [archBase])]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [archBase]
      rw [hm, map_one]
      rfl
    rw [hh]
    exact (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1
  have hbase : q (archBase F) = word F ζ hζ w u g := by
    have hh := scalar_word_in_chart F ζ hζ u hu O hOo hb hOD hμ hprod w g _ hb
    simpa only [hbchart, mul_one, word, q] using hh.symm
  apply tendsto_def.mpr
  intro N hN
  have hn : q ⁻¹' N ∈ nhds (archBase F) :=
    (hq.continuousOn.continuousAt (hOo.mem_nhds hb)).preimage_mem_nhds (hbase.symm ▸ hN)
  obtain ⟨W, hWN, hWo, hbW⟩ := mem_nhds_iff.mp (Filter.inter_mem hn (hOo.mem_nhds hb))
  have hWO : W ⊆ O := fun x hx => (hWN hx).2
  have hT := hthick W hWo hbW hWO U
  change ∀ᶠ y in nhds (1 : KPGlobalTorusFunctionData.G F ζ hζ),
    ∃ x ∈ W, ∃ a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
      y = archChart F ζ hζ x * a at hT
  have hg : ∀ᶠ y in nhds g, ∃ x ∈ W,
      ∃ a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
        g⁻¹*y = archChart F ζ hζ x * a :=
    (show ContinuousAt (fun y : KPGlobalTorusFunctionData.G F ζ hζ => g⁻¹*y) g from
      continuousAt_const.mul continuousAt_id).eventually (by simpa using hT)
  filter_upwards [hg] with y hy
  obtain ⟨x, hx, a, ha, he⟩ := hy
  have hy' : y = (g * archChart F ζ hζ x)*a := by
    calc y = g*(g⁻¹*y) := by simp
         _ = _ := by rw [he, mul_assoc]
  change word F ζ hζ w u y ∈ N
  rw [hy', rightWord_level F ζ hζ u a (fun x => hcomm U a ha x)
    (fun g => hlevel g ⟨a,ha⟩) w]
  change word F ζ hζ w u
    (g * archChart F ζ hζ x) ∈ N
  rw [scalar_word_in_chart F ζ hζ u hu O hOo hb hOD hμ hprod w g x (hWO hx)]
  exact (hWN hx).1

variable (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
  (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
  (T : KPGlobalEisensteinData.CompactTypeStage
    ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)).comp D.K.subtype))

end DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets

end
end

section

noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ContDiff Matrix Matrix.Norms.Operator

namespace DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem scalar_smooth_native_right_chart
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (v : KPGlobalTorusFunctionData.BorelFunctions F ζ hζ Q)
    (hv : v ∈ KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ Q) :
    ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => v.val (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archDomain F) := by
  obtain ⟨b, rfl⟩ := LinearMap.mem_range.mp hv
  have hb : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (b.val.val
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)).val.val 1)
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
    apply Submodule.iSup_induction _ (motive := fun b => ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (b.val
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)).val.val 1)
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)) b.property
    · intro J b hb
      exact hb.1
    · intro g
      exact contDiffOn_const
    · intro b c hb hc g
      exact (hb g).add (hc g)
  intro g
  apply contDiffOn_of_locally_contDiffOn
  intro x₀ hx₀
  obtain ⟨O, q, hO, hxO, hq, hqO, heq⟩ :=
    KPLiteralChamber.literal_right_to_left_chart_local_transition F ζ hζ g x₀ hx₀
  refine ⟨O, hO, hxO, ?_⟩
  have hc := (hb (g * KPGlobalResidualConstruction.archChart F ζ hζ x₀)).comp hq hqO
  apply (hc.congr (fun x hx => ?_)).mono Set.inter_subset_right
  rw [KPGlobalTorusBorelTwistCompatibility.scalarSection_formula, heq x hx]
  rfl

open Filter KPGlobalResidualConstruction
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

variable (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
  (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
  (T : KPGlobalEisensteinData.CompactTypeStage
    ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)).comp D.K.subtype))

 theorem stage_chart_smooth (v : KPMsRationalCompactCrossPairing.sourceStage F ζ hζ D U T) :
    ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => v.val.val (g * archChart F ζ hζ x)) (archDomain F) :=
  scalar_smooth_native_right_chart _ v.val v.property.1.1

 theorem stage_level (v : KPMsRationalCompactCrossPairing.sourceStage F ζ hζ D U T) :
    ∀ g, ∀ u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
      v.val.val (g * u.val) = v.val.val g := by
  intro g u
  obtain ⟨j, hj, heq⟩ := u.property
  have hh := v.property.1.2 ⟨j, hj⟩
  have h := congrArg (fun f => f.val g) hh
  change v.val.val (g * j.val) = v.val.val g at h
  change j.val = u.val at heq
  rwa [heq] at h

def stageWords : List (KPSmoothActualFlowData.B F) →
    KPMsRationalCompactCrossPairing.sourceStage F ζ hζ D U T →ₗ[ℂ]
      C(KPGlobalTorusFunctionData.G F ζ hζ, ℂ) := fun w =>
  { toFun := fun v => ⟨word F ζ hζ w v.val.val,
      rightWord_continuous_of_chart_smooth F ζ hζ U v.val.val
        (stage_chart_smooth F ζ hζ D U T v) (stage_level F ζ hζ D U T v) w⟩
    map_add' := fun v u => ContinuousMap.ext fun g => congrFun
      (word_add F ζ hζ v.val.val u.val.val
        (stage_chart_smooth F ζ hζ D U T v) (stage_chart_smooth F ζ hζ D U T u) w) g
    map_smul' := fun c v => ContinuousMap.ext fun g => congrFun
      (word_smul F ζ hζ c v.val.val (stage_chart_smooth F ζ hζ D U T v) w) g }

end DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets

end
end

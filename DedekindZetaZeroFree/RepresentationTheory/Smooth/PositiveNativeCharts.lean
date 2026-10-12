module

public import DedekindZetaZeroFree.Adeles.Archimedean.RightLieWords
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.NativeLieWordReindexing
public import DedekindZetaZeroFree.Analysis.RightFrame.PullbackWords
public import DedekindZetaZeroFree.Metaplectic.Kubota.ArchimedeanChartMultiplication
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightInvariantDifferentialWords

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativePositiveChart
open KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification
open KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def rightDerivative (b : KPSmoothActualFlowData.B F)
    (u : G F ζ hζ → ℂ) (g : G F ζ hζ) : ℂ :=
  deriv (fun t : ℝ => u (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPSmoothActualFlowData.flow F b t))) 0

 theorem word_reindex (w : List (Fin (groupDimension F)))
    (u : G F ζ hζ → ℂ) :
    actualRightWord F ζ hζ w u =
      (w.map (fun b => actualBasisReindex F (lieEnumeration F b))).foldr
        (fun b v => rightDerivative F ζ hζ b v) u := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change actualRight F ζ hζ b (actualRightWord F ζ hζ w u) = _
    rw [ih]
    funext g
    change deriv (fun t : ℝ => _) 0 = deriv (fun t : ℝ => _) 0
    congr 1
    funext t
    rw [actual_frame_ray_eq_flow F]

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativePositiveChart

end

section

noncomputable section
open scoped NumberField Classical Topology ContDiff Matrix Matrix.Norms.Operator
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativePositiveChart
open Filter KPGlobalResidualConstruction
open KPContActualSphericalRightFieldIdentification
open KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeChartProduct renaming product → product
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeChartProduct renaming choose_domain → choose_domain
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeChartProduct renaming product_smooth → product_smooth
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeChartProduct renaming product_chart → product_chart
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private def flowMatrix (b : KPSmoothActualFlowData.B F) (t : ℝ)
    (v : NumberField.InfinitePlace F) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KPSmoothActualFlowData.matrixExponential
    (KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = b then t else 0))
private def theta (b : KPSmoothActualFlowData.B F) (t : ℝ) : ArchCoordinates F :=
  fun v => KPLiteralChamber.rightCoordinates (flowMatrix F b t v).val
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

private theorem theta_smooth (b : KPSmoothActualFlowData.B F) :
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
  rw [KPLiteralChamber.right_insertion]
  congr 1
  funext v
  exact KPLiteralChamber.rightCoordinates_reconstruct (flowMatrix F b t v) (ht v)
private def chartProduct (p : ArchCoordinates F × ArchCoordinates F) : ArchCoordinates F :=
  product F p
private theorem chartProduct_base_right (x : ArchCoordinates F) :
    chartProduct F (x,archBase F) = x := by
  funext q i
  fin_cases i <;> simp [chartProduct, product, archBase]
private def transport (b : KPSmoothActualFlowData.B F) (p : ArchCoordinates F × ℝ) : ArchCoordinates F :=
  chartProduct F (p.1, theta F b p.2)
private def field (b : KPSmoothActualFlowData.B F) (x : ArchCoordinates F) : ArchCoordinates F :=
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

private def coordWord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} (fields : ι → E → E) : List ι → (E → ℂ) → E → ℂ
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
    (u : KPGlobalResidualConstruction.G F ζ hζ → ℂ)
    (huAll : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (V : Set (ArchCoordinates F)) (hVo : IsOpen V) (hb : archBase F ∈ V)
    (hVD : V ⊆ archDomain F)
    (hμ : ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (V ×ˢ V))
    (hprod : ∀ y ∈ V, ∀ x ∈ V, archChart F ζ hζ (chartProduct F (y,x)) =
      archChart F ζ hζ y * archChart F ζ hζ x)
    (w : List (KPSmoothActualFlowData.B F)) (g : KPGlobalResidualConstruction.G F ζ hζ) :
    ∀ x ∈ V,
      w.foldr (fun b v => rightDerivative F ζ hζ b v)
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
        w.foldr (fun b v => rightDerivative F ζ hζ b v)
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

private theorem directional_map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : Type*} (fields : B → E → E) (f : A → B) (w : List A) (u : E → ℂ) :
    RightFrame.PullbackWords.directionalWord fields (w.map f) u =
      RightFrame.PullbackWords.directionalWord (fun a => fields (f a)) w u := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [List.map_cons, RightFrame.PullbackWords.directionalWord, ih]

theorem actual_rightWord_chart_realization :
    ∃ (O : Set (ArchCoordinates F))
      (fields : Fin (groupDimension F) → ArchCoordinates F → ArchCoordinates F),
      IsOpen O ∧ archBase F ∈ O ∧ O ⊆ archDomain F ∧
      (∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) O) ∧
      ∀ (u : G F ζ hζ → ℂ),
        (∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
          (fun x => u (g * archChart F ζ hζ x)) (archDomain F)) →
        ∀ (w : List (Fin (groupDimension F))) (g : G F ζ hζ) (x : ArchCoordinates F),
          x ∈ O → actualRightWord F ζ hζ w u (g * archChart F ζ hζ x) =
            RightFrame.PullbackWords.directionalWord fields w
              (fun y => u (g * archChart F ζ hζ y)) x := by
  obtain ⟨O, hOo, hb, hOD, hden⟩ := choose_domain F
  have hμ : ContDiffOn ℝ (⊤ : ℕ∞) (chartProduct F) (O ×ˢ O) :=
    product_smooth F O hden
  have hprod : ∀ y ∈ O, ∀ x ∈ O, archChart F ζ hζ (chartProduct F (y,x)) =
      archChart F ζ hζ y * archChart F ζ hζ x :=
    fun y hy x hx => product_chart F ζ hζ y x (hOD hy) (hOD hx)
      (hden y hy x hx)
  let reindex := fun b => actualBasisReindex F (lieEnumeration F b)
  refine ⟨O, fun b => field F (reindex b), hOo, hb, hOD,
    fun b => field_smooth F (reindex b) O hOo hb hμ, ?_⟩
  intro u hu w g x hx
  rw [word_reindex]
  have he : coordWord (field F) (w.map reindex) =
      RightFrame.PullbackWords.directionalWord (field F) (w.map reindex) := by
    generalize w.map reindex = r
    induction r with
    | nil => rfl
    | cons b r ih => simp only [coordWord, RightFrame.PullbackWords.directionalWord, ih]
  rw [← directional_map (field F) reindex w, ← he]
  exact scalar_word_in_chart F ζ hζ u hu O hOo hb hOD hμ hprod (w.map reindex) g x hx

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativePositiveChart

end
end

module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology Manifold ContDiff Matrix.Norms.Elementwise
open Filter Topology
namespace DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalSmoothBridge
open KPMsGreenFlux

private theorem smooth_arch_orbit
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    [C : ChartedSpace (KPSmoothActualFlowData.LieCoordinates F) (KPSmoothActualFlowData.GInfinity F)]
    [L : LieGroup (𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F)) (⊤ : ℕ∞) (KPSmoothActualFlowData.GInfinity F)]
    (D : PartialDiffeomorph 𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F)
      𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F)
      (KPSmoothActualFlowData.LieCoordinates F) (KPSmoothActualFlowData.GInfinity F) (⊤ : ℕ∞))
    (h0 : (0 : KPSmoothActualFlowData.LieCoordinates F) ∈ D.source)
    (hD : ∀ a ∈ D.source, D a = KPSmoothActualFlowData.exponential F a)
    (hz : KPSmoothActualFlowData.exponential F 0 = 1)
    (u : Cover F ζ hζ → ℂ) (hu : Smooth F ζ hζ u) (g : Cover F ζ hζ) :
    ContMDiff 𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (fun a => u (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a)) := by
  intro a
  let E := D.toOpenPartialHomeomorph
  let q : KPSmoothActualFlowData.GInfinity F → ℂ :=
    fun b => u (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ b)
  let φ : KPSmoothActualFlowData.LieCoordinates F → ℂ :=
    fun v => q (a * KPSmoothActualFlowData.exponential F v)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    convert hu.2 (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) using 1
    funext v
    dsimp [φ, q]
    rw [(KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1, mul_assoc]
  have h1 : E 0 = (1 : KPSmoothActualFlowData.GInfinity F) :=
    (hD 0 h0).trans hz
  have hi : ContMDiffAt 𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F)
      𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F) (⊤ : ℕ∞) E.symm
      (1 : KPSmoothActualFlowData.GInfinity F) := by
    exact h1 ▸ D.symm.contMDiffOn.contMDiffAt
      (E.open_target.mem_nhds (E.map_source h0))
  have hψ : ContMDiffAt 𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F)
      𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F) (⊤ : ℕ∞)
      (fun b : KPSmoothActualFlowData.GInfinity F => E.symm (a⁻¹ * b)) a :=
    hi.comp_of_eq (contMDiffAt_const.mul contMDiffAt_id) (inv_mul_cancel a)
  have hh := hφ.contMDiff.contMDiffAt.comp a hψ
  apply hh.congr_of_eventuallyEq
  have hn : ∀ᶠ b in 𝓝 a, a⁻¹ * b ∈ E.target :=
    (show ContinuousAt (fun b : KPSmoothActualFlowData.GInfinity F => a⁻¹ * b) a from
      continuousAt_const.mul continuousAt_id).preimage_mem_nhds (by
        change E.target ∈ 𝓝 (a⁻¹ * a)
        rw [inv_mul_cancel]
        exact E.open_target.mem_nhds (h1 ▸ E.map_source h0))
  filter_upwards [hn] with b hb
  dsimp [φ]
  rw [← hD _ (E.map_target hb)]
  change q b = q (a * E (E.symm (a⁻¹ * b)))
  rw [E.right_inv hb, ← mul_assoc, mul_inv_cancel, one_mul]

 def matrixClass (M : Matrix (Fin 2) (Fin 2) ℂ) : PGLComplex.Group :=
  Matrix.ProjGenLinGroup.mk (if h : M.det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero M h else 1)

open scoped Matrix.Norms.Operator in
private theorem matrixClass_continuousAt (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det ≠ 0) :
    ContinuousAt matrixClass M := by
  apply (QuotientGroup.continuous_mk).continuousAt.comp
  apply (Units.isOpenEmbedding_val (R := Matrix (Fin 2) (Fin 2) ℂ)).isEmbedding.isInducing.continuousAt_iff.mpr
  apply ContinuousAt.congr_of_eventuallyEq continuousAt_id
  filter_upwards [(isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds hM] with N hN
  change (if h : N.det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero N h else 1).val = N
  change N.det ≠ 0 at hN
  rw [dite_eq_left hN]
  rfl

private theorem matrixClass_contMDiffAt
    {C : ChartedSpace PGLComplex.Coordinates PGLComplex.Group}
    (hC : ∀ g : PGLComplex.Group, chartAt PGLComplex.Coordinates g =
      ((PGLComplex.affineChart.trans (Homeomorph.mulLeft g).toOpenPartialHomeomorph).symm))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (M : V → Matrix (Fin 2) (Fin 2) ℂ) (x : V)
    (hM : ContDiffAt ℝ (⊤ : ℕ∞) M x) (hx : (M x).det ≠ 0) :
    ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, PGLComplex.Coordinates) (⊤ : ℕ∞)
      (fun y => matrixClass (M y)) x := by
  have hc := (matrixClass_continuousAt (M x) hx).comp hM.continuousAt
  apply contMDiffAt_iff.mpr
  refine ⟨hc, ?_⟩
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.comp_id,
    extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp]
  rw [hC]
  let g := matrixClass (M x)
  let m := g.out⁻¹
  have hmg : Matrix.ProjGenLinGroup.mk m = g⁻¹ := by
    rw [map_inv]; exact congrArg Inv.inv (Quotient.out_eq g)
  simp only [Function.comp_def, PartialEquiv.refl_symm, PartialEquiv.refl_coe, Set.range_id]
  change ContDiffWithinAt ℝ (⊤ : ℕ∞)
    (fun y => PGLComplex.affineChart.symm (g⁻¹ * matrixClass (M y))) Set.univ x
  have hn : ∀ᶠ y in 𝓝 x, (M y).det ≠ 0 :=
    hM.continuousAt.preimage_mem_nhds
      ((isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds hx)
  have ht : ∀ᶠ y in 𝓝 x, g⁻¹ * matrixClass (M y) ∈ PGLComplex.affineTarget := by
    have hopen : IsOpen PGLComplex.affineTarget := by
      rw [← PGLComplex.affineChart_target]; exact PGLComplex.affineChart.open_target
    exact (continuousAt_const.mul hc).preimage_mem_nhds (by
      simpa [g] using hopen.mem_nhds PGLComplex.one_mem_affineTarget)
  have he : (fun y => PGLComplex.affineChart.symm (g⁻¹ * matrixClass (M y))) =ᶠ[𝓝 x]
      (fun y => PGLComplex.matrixRatios (m.val * M y)) := by
    filter_upwards [hn, ht] with y hy hyt
    rw [PGLComplex.affineChart_symm_apply _ hyt]
    have hmk : g⁻¹ * matrixClass (M y) =
        Matrix.ProjGenLinGroup.mk (m * Matrix.GeneralLinearGroup.mkOfDetNeZero (M y) hy) := by
      rw [map_mul, hmg]; simp [matrixClass, hy]
    rw [hmk, PGLComplex.matrixRatios_mk]
    rfl
  have hd : (m.val * M x) 0 0 ≠ 0 := by
    have hmk : Matrix.ProjGenLinGroup.mk (m * Matrix.GeneralLinearGroup.mkOfDetNeZero (M x) hx) = 1 := by
      rw [map_mul, hmg]
      change g⁻¹ * Matrix.ProjGenLinGroup.mk _ = 1
      rw [show Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero (M x) hx) = g by simp [g, matrixClass, hx]]
      exact inv_mul_cancel g
    have hh := PGLComplex.mk_mem_affineTarget_iff (m * Matrix.GeneralLinearGroup.mkOfDetNeZero (M x) hx)
    exact hh.mp (hmk ▸ PGLComplex.one_mem_affineTarget)
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.congr_of_eventuallyEq _ he
  have hmul : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => m.val * M y) x := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact (contDiffAt_const.mul (contDiffAt_pi.mp (contDiffAt_pi.mp hM 0) j)).add
      (contDiffAt_const.mul (contDiffAt_pi.mp (contDiffAt_pi.mp hM 1) j))
  exact (PGLComplex.contDiffAt_matrixRatios _ hd).comp x hmul

 theorem smooth_matrix_parametrization
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u : Cover F ζ hζ → ℂ) (hu : Smooth F ζ hζ u) (g : Cover F ζ hζ)
    (M : V → NumberField.InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ) (x : V)
    (hM : ContDiffAt ℝ (⊤ : ℕ∞) M x) (hx : ∀ w, (M x w).det ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y => u (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => matrixClass (M y w)))) x := by
  obtain ⟨C, L, hC⟩ := PGLComplex.affine_lie_structure
  letI := C
  letI := L
  obtain ⟨D, hD, _, _⟩ := PGLComplex.single_lie_exponential_data hC
  let CP := PGLComplex.productAffineChartedSpace (NumberField.InfinitePlace F) (C := C)
  letI := CP
  let LP := PGLComplex.productAffineLieGroup (NumberField.InfinitePlace F) (C := C)
  letI := LP
  let EP := PGLComplex.productExponentialDiffeomorph (NumberField.InfinitePlace F) D
  have h0 : (0 : KPSmoothActualFlowData.LieCoordinates F) ∈ EP.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    intro w hw
    simpa using D.zero_mem_source
  have he (a : KPSmoothActualFlowData.LieCoordinates F) (ha : a ∈ EP.source) :
      EP a = KPSmoothActualFlowData.exponential F a := by
    funext w
    change D.exponentialChart ((PGLComplex.productCoordinatesFlatten (NumberField.InfinitePlace F)).symm a w) = _
    have hw : (PGLComplex.productCoordinatesFlatten (NumberField.InfinitePlace F)).symm a w ∈ D.exponentialChart.source :=
      ha.2 w (Set.mem_univ w)
    rw [D.chart_eq_exponential _ hw, hD]
    rfl
  have hz : KPSmoothActualFlowData.exponential F 0 = 1 := by
    change PGLComplex.productExponential (NumberField.InfinitePlace F) 0 = 1
    exact PGLComplex.productExponential_zero _
  have ho := smooth_arch_orbit EP h0 he hz u hu g
  have hm : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F)
      (⊤ : ℕ∞) (fun y => fun w => matrixClass (M y w)) x := by
    have hi (w : NumberField.InfinitePlace F) :=
      matrixClass_contMDiffAt hC (fun y => M y w) x (contDiffAt_pi.mp hM w) (hx w)
    apply contMDiffAt_iff.mpr
    refine ⟨continuousAt_pi.mpr (fun w => (hi w).continuousAt), ?_⟩
    have hc (w : NumberField.InfinitePlace F) := (contMDiffAt_iff.mp (hi w)).2
    simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] at hc ⊢
    change ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun a => PGLComplex.productCoordinatesFlatten (NumberField.InfinitePlace F)
        (fun w => chartAt PGLComplex.Coordinates (matrixClass (M x w))
          (matrixClass (M ((extChartAt 𝓘(ℝ, V) x).symm a) w)))) _ _
    apply (PGLComplex.productCoordinatesFlatten (NumberField.InfinitePlace F)).contDiff.contDiffAt.comp_contDiffWithinAt
    exact contDiffWithinAt_pi.mpr hc
  exact (ho.contMDiffAt.comp x hm).contDiffAt

 def rightPolynomial {ι : Type*} (x : ι → Fin 3 → ℂ) : ι → Matrix (Fin 2) (Fin 2) ℂ :=
  fun w => !![x w 1 + x w 0 * x w 2, x w 0; x w 2, 1]

 theorem rightPolynomial_smooth {ι : Type*} [Fintype ι] :
    ContDiff ℝ (⊤ : ℕ∞) (rightPolynomial (ι := ι)) := by
  apply contDiff_pi.mpr
  intro w
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → Fin 3 → ℂ => x w 1 + x w 0 * x w 2)
    fun_prop
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → Fin 3 → ℂ => x w 0)
    fun_prop
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → Fin 3 → ℂ => x w 2)
    fun_prop
  · change ContDiff ℝ (⊤ : ℕ∞) (fun _ : ι → Fin 3 → ℂ => (1 : ℂ))
    fun_prop

 theorem rightPolynomial_det {ι : Type*} (x : ι → Fin 3 → ℂ) (w : ι) :
    (rightPolynomial x w).det = x w 1 := by
  simp [rightPolynomial, Matrix.det_fin_two]

end DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalSmoothBridge

end

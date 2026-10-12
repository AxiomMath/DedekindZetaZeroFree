module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdelicQuotients.CuspEndCoordinates
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.LaplacianJets
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.FiniteCoefficientReconstruction
public import DedekindZetaZeroFree.Eisenstein.Continuation.IncomingCuspModes.JetSpatialSmoothness
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.MeanZeroEnergyTails

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section
open scoped Classical NumberField BigOperators ContDiff ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContThreeL2CotangentHelpers

open KPContActualSectorSmoothTestModules KPContActualCotangentCountableShrinking
open KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy
open KPContCotangentOverlapRationalBranches KPContActualCotangentMeasurableFamilies

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem continuous_labeledA_self :
    Continuous (labeledA (placeEquiv F ζ hζ) : M F → KPCuspGenuineMonodromy.SymmetricSpace F) := by
  apply continuous_pi
  intro k
  exact (continuous_apply (placeEquiv F ζ hζ |>.symm k)).comp
    (CotangentLogCoframe.A (d F)).continuous

private theorem isOpen_omega (a : ActualChart (U := U) (H := H)) : IsOpen (omega a) :=
  a.domain_open.preimage continuous_labeledA_self

 def zext (a : ActualChart (U := U) (H := H)) (f : omega a → ℂ) : M F → ℂ :=
  fun x => if hx : x ∈ omega a then f ⟨x, hx⟩ else 0

private theorem smooth_zext {a : ActualChart (U := U) (H := H)} {f : omega a → ℂ}
    (hf : SmoothOnLift a f) : ContDiffOn ℝ (⊤ : ℕ∞) (zext a f) (omega a) := by
  obtain ⟨g, hg, he⟩ := hf
  refine hg.congr (f₁ := zext a f) ?_
  intro x hx
  simpa [zext, hx] using (he ⟨x, hx⟩).symm

private theorem smooth_differential {a : ActualChart (U := U) (H := H)} {f : omega a → ℂ}
    (hf : SmoothOnLift a f) : SmoothOnLift a (fun x => CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (zext a f) x.val)) := by
  refine ⟨fun x => CotangentLogCoframe.j (d F)
    (HyperbolicChart.differential (d F) (zext a f) x), ?_, fun _ => rfl⟩
  rw [contDiffOn_piLp]
  rintro ⟨i, k⟩
  have hd := (smooth_zext hf).fderiv_of_isOpen (isOpen_omega a) (m := (⊤ : ℕ∞)) (by simp)
  have hcd (k : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞)
      (HyperbolicChart.coordinateDerivative (d F) i k (zext a f)) (omega a) :=
    hd.clm_apply contDiffOn_const
  have hexp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : M F => (Real.exp (x (i, 2)) : ℂ)) (omega a) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.exp.contDiffOn)
  fin_cases k
  · simpa [CotangentLogCoframe.j, HyperbolicChart.differential] using hcd 2
  · simpa [CotangentLogCoframe.j, HyperbolicChart.differential] using hexp.mul (hcd 0)
  · simpa [CotangentLogCoframe.j, HyperbolicChart.differential] using hexp.mul (hcd 1)

private theorem measurable_smooth {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {a : ActualChart (U := U) (H := H)} {f : omega a → W} (hf : SmoothOnLift a f) :
    Measurable f := by
  obtain ⟨g, hg, he⟩ := hf
  have h : f = (omega a).domRestrict g := funext (fun x => (he x).symm)
  rw [h]
  exact hg.continuousOn.domRestrict.measurable

private theorem differential_frame (f : M F → ℂ) (x : M F) (k : Fin (d F) × Fin 3) :
    (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x)) k =
      fderiv ℝ f x (CotangentLogCoframe.H (d F) x
        (EuclideanSpace.basisFun _ ℝ k)) := by
  rcases k with ⟨i, k⟩
  fin_cases k
  · have hh : CotangentLogCoframe.H (d F) x (EuclideanSpace.basisFun _ ℝ (i, (0 : Fin 3))) =
        HyperbolicChart.coordinateVector (d F) i 2 := by
      ext ⟨j, k⟩
      fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        HyperbolicChart.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
    change (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x)) (i, (0 : Fin 3)) =
      fderiv ℝ f x (CotangentLogCoframe.H (d F) x
        (EuclideanSpace.basisFun _ ℝ (i, (0 : Fin 3))))
    rw [hh]
    simp [CotangentLogCoframe.j, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative]
  · have hh : CotangentLogCoframe.H (d F) x (EuclideanSpace.basisFun _ ℝ (i, (1 : Fin 3))) =
        Real.exp (x (i, 2)) • HyperbolicChart.coordinateVector (d F) i 0 := by
      ext ⟨j, k⟩
      fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        HyperbolicChart.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
      split_ifs with h <;> simp_all
    change (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x)) (i, (1 : Fin 3)) =
      fderiv ℝ f x (CotangentLogCoframe.H (d F) x
        (EuclideanSpace.basisFun _ ℝ (i, (1 : Fin 3))))
    rw [hh]
    simp [CotangentLogCoframe.j, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative, RCLike.real_smul_eq_coe_mul]
  · have hh : CotangentLogCoframe.H (d F) x (EuclideanSpace.basisFun _ ℝ (i, (2 : Fin 3))) =
        Real.exp (x (i, 2)) • HyperbolicChart.coordinateVector (d F) i 1 := by
      ext ⟨j, k⟩
      fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        HyperbolicChart.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
      split_ifs with h <;> simp_all
    change (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x)) (i, (2 : Fin 3)) =
      fderiv ℝ f x (CotangentLogCoframe.H (d F) x
        (EuclideanSpace.basisFun _ ℝ (i, (2 : Fin 3))))
    rw [hh]
    simp [CotangentLogCoframe.j, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative, RCLike.real_smul_eq_coe_mul]

private theorem differential_frame_sum (f : M F → ℂ) (x : M F) (v : V F) :
    fderiv ℝ f x (CotangentLogCoframe.H (d F) x v) =
      ∑ k, (v k : ℂ) *
        (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x)) k := by
  conv_lhs => rw [← OrthonormalBasis.sum_repr (EuclideanSpace.basisFun _ ℝ) v]
  simp only [EuclideanSpace.basisFun_repr, map_sum, map_smul, differential_frame,
    RCLike.real_smul_eq_coe_mul]
  rfl

private theorem differential_arrow_const {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) i}
    (e : Arrow a b) (c : ℂ) (f g : M F → ℂ) (x : M F) (hx : x ∈ e.domain)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (e.psi x))
    (he : (fun y => g (e.psi y)) =ᶠ[𝓝 x] c • f) :
    CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) g (e.psi x)) =
      c • KPContCotangentRealOrthogonalComplexification.operatorComplexification _ (Q e x)
        (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x)) := by
  have hψ : DifferentiableAt ℝ e.psi x :=
    ((smooth_metric e).1.differentiableOn (by simp) x hx).differentiableAt
      (e.isOpen_domain.mem_nhds hx)
  have hd : (fderiv ℝ g (e.psi x)).comp (fderiv ℝ e.psi x) = c • fderiv ℝ f x := by
    rw [← fderiv_comp x hg hψ]
    change fderiv ℝ (fun y => g (e.psi y)) x = _
    rw [he.fderiv_eq, fderiv_const_smul hf]
  ext k
  rw [differential_frame]
  let v := (KPContCotangentActualGenuineTwistIsotropy.q e x hx).symm
    (EuclideanSpace.basisFun _ ℝ k)
  have hh : fderiv ℝ e.psi x (CotangentLogCoframe.H (d F) x v) =
      CotangentLogCoframe.H (d F) (e.psi x) (EuclideanSpace.basisFun _ ℝ k) := by
    apply (CotangentLogCoframe.C (d F) (e.psi x)).injective
    change Q e x v = _
    change KPContCotangentActualGenuineTwistIsotropy.q e x hx v = _
    simp [v, CotangentLogCoframe.H]
  rw [← hh]
  have hdv := congrArg (fun A : M F →L[ℝ] ℂ => A (CotangentLogCoframe.H (d F) x v)) hd
  rw [ContinuousLinearMap.comp_apply, smul_apply,
    differential_frame_sum] at hdv
  rw [hdv]
  change _ = c *
    (KPContCotangentRealOrthogonalComplexification.operatorComplexification _ (Q e x)
      (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x))) k
  rw [KPContCotangentRealOrthogonalComplexification.operatorComplexification_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  have hv : v l = Q e x (EuclideanSpace.basisFun _ ℝ l) k := by
    have hi := (KPContCotangentActualGenuineTwistIsotropy.q e x hx).inner_map_map
      v (EuclideanSpace.basisFun _ ℝ l)
    have hvq : KPContCotangentActualGenuineTwistIsotropy.q e x hx v =
        EuclideanSpace.basisFun _ ℝ k := by simp [v]
    rw [hvq] at hi
    change inner ℝ (EuclideanSpace.basisFun _ ℝ k)
      (Q e x (EuclideanSpace.basisFun _ ℝ l)) =
      inner ℝ v (EuclideanSpace.basisFun _ ℝ l) at hi
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      EuclideanSpace.basisFun_apply, Pi.single_apply] using hi.symm
  rw [hv]

private theorem differential_arrow {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) i}
    (e : Arrow a b) (f g : M F → ℂ) (x : M F) (hx : x ∈ e.domain)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (e.psi x))
    (he : (fun y => g (e.psi y)) =ᶠ[𝓝 x] fun y => e.phase y * f y) :
    CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) g (e.psi x)) =
      T e x hx (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x)) := by
  have hp : e.phase =ᶠ[𝓝 x] fun _ => e.phase x := by
    have hopen := e.isOpen_domain.isOpenMap_subtype_val _
      ((unitary_phase e).1.isOpen_fiber (e.phase x))
    have hmem : x ∈ (Subtype.val : e.domain → M F) '' {y | e.phase y.val = e.phase x} :=
      ⟨⟨x, hx⟩, rfl, rfl⟩
    filter_upwards [hopen.mem_nhds hmem] with y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact hz
  change _ = e.phase x •
    KPContCotangentRealOrthogonalComplexification.operatorComplexification _ (Q e x) _
  apply differential_arrow_const e (e.phase x) f g x hx hf hg
  filter_upwards [he, hp] with y hy hpy
  simpa [hpy] using hy

private theorem differentiable_zext {a : ActualChart (U := U) (H := H)}
    {f : omega a → ℂ} (hf : SmoothOnLift a f) (x : omega a) :
    DifferentiableAt ℝ (zext a f) x.val :=
  ((smooth_zext hf).differentiableOn (by simp) x.val x.property).differentiableAt
    ((isOpen_omega a).mem_nhds x.property)

private theorem differential_measurable (f : ScalarFields F ζ hζ U R P H)
    (hf : ∀ a, SmoothOnLift a (f a)) (hc : ScalarCompatible f) :
    IsMeasurableCotangentFamily (fun a x => CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (zext a (f a)) x.val)) := by
  refine ⟨fun a => measurable_smooth (smooth_differential (hf a)), ?_, ?_⟩
  · intro a γ x hx
    apply differential_arrow (isotropyArrow a γ) (zext a (f a)) (zext a (f a)) x
      (omega_subset_larger a hx) (differentiable_zext (hf a) ⟨x, hx⟩)
      (differentiable_zext (hf a) ⟨_, isotropy_mem a γ x hx⟩)
    filter_upwards [(isOpen_omega a).mem_nhds hx] with y hy
    simpa [zext, hy, isotropy_mem a γ y hy] using hc.1 a γ y hy
  · intro a b e x hx
    apply differential_arrow e.arrow (zext a (f a)) (zext b (f b)) x hx
      (differentiable_zext (hf a) ⟨x, e.source_shrinking hx⟩)
      (differentiable_zext (hf b) ⟨_, e.target_shrinking hx⟩)
    filter_upwards [e.arrow.isOpen_domain.mem_nhds hx] with y hy
    simpa [zext, e.source_shrinking hy, e.target_shrinking hy] using hc.2 a b e y hy

private theorem section_smooth (s : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H)
    (hs : KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ U R P H s)
    (a : ActualChart (U := U) (H := H)) : SmoothOnLift a (sectionFields s a) := by
  refine ⟨fun x => (s a.component).val (labeledA (placeEquiv F ζ hζ) x), ?_, ?_⟩
  · have hla : ContDiff ℝ (⊤ : ℕ∞) (labeledA (placeEquiv F ζ hζ)) := by
      apply contDiff_pi.mpr
      intro k
      exact (ContinuousLinearMap.proj ((placeEquiv F ζ hζ).symm k) :
        KPArch.Space (d F) →L[ℝ] KPArch.H3).contDiff.comp (CotangentLogCoframe.A (d F)).contDiff
    exact ((hs a.component).comp hla).contDiffOn
  · intro x
    simp [sectionFields, LiftedChart.coefficient, isotropyChart, ChartKind.representative]

private theorem section_compatible (s : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H) :
    ScalarCompatible (sectionFields s) := by
  constructor
  · intro a γ x hx
    exact (unitary_phase (isotropyArrow a γ)).2.2.2 s x (omega_subset_larger a hx)
  · intro a b e x hx
    obtain ⟨hab, arr, hsource, htarget, hlarger⟩ := e
    cases a with
    | mk i ca oa da dao dac das dai =>
      cases b with
      | mk j cb ob db dbo dbc dbs dbi =>
        dsimp at hab
        subst j
        exact (unitary_phase arr).2.2.2 s x hx

 theorem smooth_section_differential
    (s : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H)
    (hs : KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ U R P H s) :
    IsMeasurableCotangentFamily (fun a =>
      KPContActualSectorTestDifferentialDescent.chartDifferential a (sectionFields s a)) := by
  exact differential_measurable (sectionFields s) (section_smooth s hs) (section_compatible s)

private theorem sum_real_basis {I : Type*} [Fintype I] [DecidableEq I]
    (b : OrthonormalBasis I ℝ (EuclideanSpace ℝ I)) (L : EuclideanSpace ℝ I →L[ℝ] ℝ) :
    ∑ i, (L (b i)) ^ 2 = ‖(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ I)).symm L‖ ^ 2 := by
  simpa only [InnerProductSpace.toDual_symm_apply] using
    b.sum_sq_inner_left ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ I)).symm L)

private theorem sum_complex_basis {I : Type*} [Fintype I] [DecidableEq I]
    (b c : OrthonormalBasis I ℝ (EuclideanSpace ℝ I)) (L : EuclideanSpace ℝ I →L[ℝ] ℂ) :
    ∑ i, ‖L (b i)‖ ^ 2 = ∑ i, ‖L (c i)‖ ^ 2 := by
  have hRe := (sum_real_basis b (Complex.reCLM.comp L)).trans
    (sum_real_basis c (Complex.reCLM.comp L)).symm
  have hIm := (sum_real_basis b (Complex.imCLM.comp L)).trans
    (sum_real_basis c (Complex.imCLM.comp L)).symm
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply] at hRe hIm
  simp only [Complex.sq_norm, Complex.normSq_apply, Finset.sum_add_distrib]
  simpa only [pow_two] using congrArg₂ (· + ·) hRe hIm

private theorem differential_frame_any (d : ℕ) (f : HyperbolicChart.Space d → ℂ) (x : HyperbolicChart.Space d) (k : Fin d × Fin 3) :
    (CotangentLogCoframe.j d (HyperbolicChart.differential d f x)) k =
      fderiv ℝ f x (CotangentLogCoframe.H d x
        (EuclideanSpace.basisFun _ ℝ k)) := by
  rcases k with ⟨i, k⟩
  fin_cases k
  · have hh : CotangentLogCoframe.H d x (EuclideanSpace.basisFun _ ℝ (i, (0 : Fin 3))) =
        HyperbolicChart.coordinateVector d i 2 := by
      ext ⟨j, k⟩
      fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        HyperbolicChart.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
    change (CotangentLogCoframe.j d (HyperbolicChart.differential d f x)) (i, (0 : Fin 3)) =
      fderiv ℝ f x (CotangentLogCoframe.H d x
        (EuclideanSpace.basisFun _ ℝ (i, (0 : Fin 3))))
    rw [hh]
    simp [CotangentLogCoframe.j, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative]
  · have hh : CotangentLogCoframe.H d x (EuclideanSpace.basisFun _ ℝ (i, (1 : Fin 3))) =
        Real.exp (x (i, 2)) • HyperbolicChart.coordinateVector d i 0 := by
      ext ⟨j, k⟩
      fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        HyperbolicChart.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
      split_ifs with h <;> simp_all
    change (CotangentLogCoframe.j d (HyperbolicChart.differential d f x)) (i, (1 : Fin 3)) =
      fderiv ℝ f x (CotangentLogCoframe.H d x
        (EuclideanSpace.basisFun _ ℝ (i, (1 : Fin 3))))
    rw [hh]
    simp [CotangentLogCoframe.j, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative, RCLike.real_smul_eq_coe_mul]
  · have hh : CotangentLogCoframe.H d x (EuclideanSpace.basisFun _ ℝ (i, (2 : Fin 3))) =
        Real.exp (x (i, 2)) • HyperbolicChart.coordinateVector d i 1 := by
      ext ⟨j, k⟩
      fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C,
        HyperbolicChart.coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
      split_ifs with h <;> simp_all
    change (CotangentLogCoframe.j d (HyperbolicChart.differential d f x)) (i, (2 : Fin 3)) =
      fderiv ℝ f x (CotangentLogCoframe.H d x
        (EuclideanSpace.basisFun _ ℝ (i, (2 : Fin 3))))
    rw [hh]
    simp [CotangentLogCoframe.j, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative, RCLike.real_smul_eq_coe_mul]

 theorem differential_norm_isometry (d : ℕ)
    (ψ : HyperbolicChart.Space d → HyperbolicChart.Space d)
    (x : HyperbolicChart.Space d)
    (hψ : DifferentiableAt ℝ ψ x)
    (hm : ∀ v w, HyperbolicChart.metric d (ψ x)
      (fderiv ℝ ψ x v) (fderiv ℝ ψ x w) = HyperbolicChart.metric d x v w)
    (f : HyperbolicChart.Space d → ℂ) (hf : DifferentiableAt ℝ f (ψ x)) :
    (∑ i, ∑ k, ‖HyperbolicChart.differential d (f ∘ ψ) x i k‖ ^ 2) =
    ∑ i, ∑ k, ‖HyperbolicChart.differential d f (ψ x) i k‖ ^ 2 := by
  let Q : EuclideanSpace ℝ (Fin d × Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin d × Fin 3) :=
    (CotangentLogCoframe.C d (ψ x)).toContinuousLinearMap.comp
      ((fderiv ℝ ψ x).comp (CotangentLogCoframe.H d x).toContinuousLinearMap)
  have hQ : ∀ v w, inner ℝ (Q v) (Q w) = inner ℝ v w := by
    intro v w
    change inner ℝ (CotangentLogCoframe.C d (ψ x)
      (fderiv ℝ ψ x (CotangentLogCoframe.H d x v)))
      (CotangentLogCoframe.C d (ψ x) (fderiv ℝ ψ x (CotangentLogCoframe.H d x w))) = _
    rw [CotangentLogCoframe.inner_C, hm, ← CotangentLogCoframe.inner_C]
    simp [CotangentLogCoframe.H]
  let q : EuclideanSpace ℝ (Fin d × Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d × Fin 3) :=
    LinearIsometryEquiv.ofSurjective
      {toLinearMap := Q.toLinearMap,
       norm_map' := (LinearMap.norm_map_iff_inner_map_map Q).2 hQ}
      (by
        apply LinearMap.surjective_of_injective
        exact (show EuclideanSpace ℝ (Fin d × Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d × Fin 3) from
          {toLinearMap := Q.toLinearMap,
           norm_map' := (LinearMap.norm_map_iff_inner_map_map Q).2 hQ}).injective)
  let L := (fderiv ℝ f (ψ x)).comp (CotangentLogCoframe.H d (ψ x)).toContinuousLinearMap
  have hh : ∀ v, fderiv ℝ ψ x (CotangentLogCoframe.H d x v) =
      CotangentLogCoframe.H d (ψ x) (q v) := by
    intro v
    apply (CotangentLogCoframe.C d (ψ x)).injective
    simp only [CotangentLogCoframe.H, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hsum := sum_complex_basis ((EuclideanSpace.basisFun (Fin d × Fin 3) ℝ).map q)
    (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ) L
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at hsum
  convert hsum using 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [← CotangentLogCoframe.j_apply d (HyperbolicChart.differential d (f ∘ ψ) x) i k,
      differential_frame_any, fderiv_comp x hf hψ]
    simp only [ContinuousLinearMap.comp_apply, hh, OrthonormalBasis.map_apply, L]
    rfl
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [← CotangentLogCoframe.j_apply d (HyperbolicChart.differential d f (ψ x)) i k,
      differential_frame_any]
    rfl

 def rationalCoordinates (F : Type) [Field F] [NumberField F]
    (places : Fin (KPContCotangentActualOverlap.d F) ≃ Fin (KPCuspLogShape.dimension F))
    (σ : KPCuspArithmetic.PGL2 F) (x : HyperbolicChart.Space (KPContCotangentActualOverlap.d F)) :=
  KPContCotangentActualOverlap.labeledAInv places
    (σ • KPContCotangentActualOverlap.labeledA places x)

private theorem rational_smooth_metric (F : Type) [Field F] [NumberField F]
    (places : Fin (KPContCotangentActualOverlap.d F) ≃ Fin (KPCuspLogShape.dimension F))
    (σ : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (rationalCoordinates F places σ) ∧
      ∀ x v w, HyperbolicChart.metric (KPContCotangentActualOverlap.d F)
        (rationalCoordinates F places σ x) (fderiv ℝ (rationalCoordinates F places σ) x v)
        (fderiv ℝ (rationalCoordinates F places σ) x w) =
        HyperbolicChart.metric (KPContCotangentActualOverlap.d F) x v w := by
  obtain ⟨B, hB⟩ := Matrix.ProjGenLinGroup.mk_surjective σ
  let n := KPContCotangentActualOverlap.d F
  let A := CotangentLogCoframe.A n
  let g := fun k => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F (places k)).embedding B
  have he : rationalCoordinates F places σ = fun x => A.symm (KPArch.productAction n g (A x)) := by
    funext x
    rw [← hB]
    unfold rationalCoordinates KPContCotangentActualOverlap.labeledAInv
    rw [show Matrix.ProjGenLinGroup.mk B • KPContCotangentActualOverlap.labeledA places x =
      KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk B)
        (KPContCotangentActualOverlap.labeledA places x) from rfl, KPCuspSiegel.action_mk]
    congr 1
    funext k
    simp [KPCuspSiegel.glAction, KPArch.productAction, KPContCotangentActualOverlap.labeledA, g, A]
    rfl
  rw [he]
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => A.symm (KPArch.productAction n g (A x))) :=
    A.symm.contDiff.comp (((KPArch.productAction_contDiff n g).of_le
      (show (⊤ : ℕ∞) ≤ (⊤ : ℕ∞ω) from le_top)).comp A.contDiff)
  refine ⟨hs, ?_⟩
  have hquad : ∀ x v, HyperbolicChart.metric n (A.symm (KPArch.productAction n g (A x)))
      (fderiv ℝ (fun x => A.symm (KPArch.productAction n g (A x))) x v)
      (fderiv ℝ (fun x => A.symm (KPArch.productAction n g (A x))) x v) =
      HyperbolicChart.metric n x v v := by
    intro x v
    have hder := A.symm.hasFDerivAt.comp x
      (((KPArch.productAction_contDiff n g).differentiable (by simp) (A x)).hasFDerivAt.comp x
        A.hasFDerivAt)
    change HasFDerivAt (fun x => A.symm (KPArch.productAction n g (A x))) _ x at hder
    rw [← CotangentLogCoframe.metric_A, hder.fderiv]
    change KPArch.metric n (A (A.symm (KPArch.productAction n g (A x))))
      (A ((A.symm.toContinuousLinearMap.comp
        ((fderiv ℝ (KPArch.productAction n g) (A x)).comp A.toContinuousLinearMap)) v)) = _
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
    exact (KPArch.metric_invariant n g (A x) (A v)).trans (CotangentLogCoframe.metric_A n x v)
  have hpolar : ∀ x u w, HyperbolicChart.metric n x (u+w) (u+w) =
      HyperbolicChart.metric n x u u + 2 * HyperbolicChart.metric n x u w +
        HyperbolicChart.metric n x w w := by
    intro x u w
    simp only [← CotangentLogCoframe.inner_C, map_add, inner_add_left, inner_add_right,
      real_inner_comm (CotangentLogCoframe.C n x w) (CotangentLogCoframe.C n x u)]
    ring
  intro x v w
  have hp := hquad x (v+w)
  rw [map_add, hpolar, hpolar, hquad x v, hquad x w] at hp
  linarith

open KPContSectorPhaseComponentCharts KPContSectorSmoothFramesSupport
open KPContActualSectorTestDifferentialDescent
private theorem shrink_at (i : Fin (H.atlas U).componentCount) (p : KPCuspGenuineMonodromy.SymmetricSpace F) :
    ∃ C : ShrunkChart F ζ hζ U R P H, C.component = i ∧ C.center = p ∧ p ∈ C.domain := by
  let O := Classical.choice (orbifoldChart_exists F ζ hζ U R P H i p)
  let : Finite (MulAction.stabilizer (Component F ζ hζ U R P H i) p) :=
    chart_stabilizer_finite F ζ hζ U R P H i p O
  let := Fintype.ofFinite (MulAction.stabilizer (Component F ζ hζ U R P H i) p)
  obtain ⟨W,hWo,hpW,hWsub,hWc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := p)) O.isOpen (Set.singleton_subset_iff.mpr O.center_mem)
  let V := ⋂ g : MulAction.stabilizer (Component F ζ hζ U R P H i) p,
    (fun x : KPCuspGenuineMonodromy.SymmetricSpace F => (g.val : KPCuspArithmetic.PGL2 F) • x) ⁻¹' W
  have hopen : IsOpen V := isOpen_iInter_of_finite fun g =>
    hWo.preimage (KPCuspSiegel.continuous_action F g.val.val)
  have hsub : V ⊆ W := by
    intro x hx
    simpa using Set.mem_iInter.mp hx (1 : MulAction.stabilizer (Component F ζ hζ U R P H i) p)
  have hp : p ∈ V := by
    apply Set.mem_iInter.mpr; intro g
    change g.val • p ∈ W
    rw [MulAction.mem_stabilizer_iff.mp g.property]
    exact hpW (Set.mem_singleton p)
  refine ⟨⟨i,p,O,V,hopen,hWc.of_isClosed_subset isClosed_closure (closure_mono hsub),
    (closure_mono hsub).trans hWsub,?_⟩,rfl,rfl,hp⟩
  intro g
  ext x; constructor
  · rintro ⟨y,hy,rfl⟩
    apply Set.mem_iInter.mpr; intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, ← mul_smul] using Set.mem_iInter.mp hy (h*g)
  · intro hx
    refine ⟨(g.val : KPCuspArithmetic.PGL2 F)⁻¹ • x,?_, smul_inv_smul _ _⟩
    apply Set.mem_iInter.mpr; intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, Subgroup.coe_inv, ← mul_smul]
      using Set.mem_iInter.mp hx (h*g⁻¹)

 def smoothGradient (s : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H)
    (hs : KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ U R P H s) :
    Family (U := U) (H := H) :=
  ⟨fun a => KPContActualSectorTestDifferentialDescent.chartDifferential a
      (fun x => (isotropyChart a).coefficient s x.val), smooth_section_differential s hs⟩

theorem smoothGradient_at_arch (s : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H)
    (hs : KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ U R P H s)
    (i : Fin (H.atlas U).componentCount) (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
    (normSquare (smoothGradient s hs) ((H.atlas U).components ⟨i, Quotient.mk _ y⟩) : ℝ) =
    (∑ j : Fin (d F), ∑ k : Fin 3,
      ‖HyperbolicChart.differential (d F)
        (fun x => (s i).val (labeledA (placeEquiv F ζ hζ) x))
        (labeledAInv (placeEquiv F ζ hζ) y) j k‖ ^ 2) := by
  obtain ⟨a, hi, hcenter, hy⟩ := shrink_at (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) i y
  let x := labeledAInv (placeEquiv F ζ hζ) y
  have hA : labeledA (placeEquiv F ζ hζ) x = y := by
    funext k
    simp [x, labeledA, labeledAInv]
  have hx : x ∈ omega a := by
    change labeledA (placeEquiv F ζ hζ) x ∈ a.domain
    rw [hA]; exact hy
  have hq : q a x = (H.atlas U).components ⟨i, Quotient.mk _ y⟩ := by
    rw [(H.atlas U).components_formula]
    change KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
      (Quotient.mk _ (labeledA (placeEquiv F ζ hζ) x)) = _
    rw [hA, hi]
  have hopen : IsOpen (omega a) := by
    apply a.domain_open.preimage
    apply continuous_pi
    intro k
    exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
  have hgerm : liftExtension a (fun z => (isotropyChart a).coefficient s z.val) =ᶠ[𝓝 x]
      (fun z => (s i).val (labeledA (placeEquiv F ζ hζ) z)) := by
    filter_upwards [hopen.mem_nhds hx] with z hz
    rw [liftExtension, dite_eq_left hz]
    simp only [sectionFields, LiftedChart.coefficient, isotropyChart, ChartKind.representative,
      map_one, Units.val_one, one_mul, one_smul]
    rw [hi]
  have hcoeff : ∀ j k, coefficient (smoothGradient s hs) a ⟨x, hx⟩ (j,k) =
      HyperbolicChart.differential (d F)
        (fun z => (s i).val (labeledA (placeEquiv F ζ hζ) z)) x j k := by
    intro j k
    change (CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (liftExtension a (fun z => (isotropyChart a).coefficient s z.val)) x)) (j,k) = _
    rw [CotangentLogCoframe.j_apply]
    fin_cases k <;> simp only [HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative, hgerm.fderiv_eq]
  rw [← hq, normSquare_chart (smoothGradient s hs) a ⟨x,hx⟩]
  change ‖coefficient (smoothGradient s hs) a ⟨x,hx⟩‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  simp_rw [hcoeff]
  rfl

theorem smoothGradient_norm_continuous
    (s : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H)
    (hs : KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ U R P H s) :
    Continuous (fun x => (normSquare (smoothGradient s hs) x : ℝ)) := by
  apply (H.atlas U).components.isQuotientMap.continuous_iff.mpr
  apply continuous_sigma_iff.mpr
  intro i
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  have hA : ContDiff ℝ (⊤ : ℕ∞) (labeledA (placeEquiv F ζ hζ)) := by
    apply contDiff_pi.mpr
    intro k
    exact (ContinuousLinearMap.proj ((placeEquiv F ζ hζ).symm k) : KPArch.Space (d F) →L[ℝ] KPArch.H3).contDiff.comp
      (CotangentLogCoframe.A (d F)).contDiff
  have hAi : Continuous (labeledAInv (placeEquiv F ζ hζ)) := by
    change Continuous (fun y : KPCuspGenuineMonodromy.SymmetricSpace F => (CotangentLogCoframe.A (d F)).symm
      (fun j => y ((placeEquiv F ζ hζ) j)))
    exact (CotangentLogCoframe.A (d F)).symm.continuous.comp
      (continuous_pi (fun j => continuous_apply _))
  have hg : ContDiff ℝ (⊤ : ℕ∞) ((s i).val ∘ labeledA (placeEquiv F ζ hζ)) := (hs i).comp hA
  have hd : ∀ j k, Continuous (fun x =>
      HyperbolicChart.differential (d F)
        (fun z => (s i).val (labeledA (placeEquiv F ζ hζ) z)) x j k) := by
    intro j k
    have hc : ∀ l, Continuous (HyperbolicChart.coordinateDerivative (d F) j l
        (fun z => (s i).val (labeledA (placeEquiv F ζ hζ) z))) := by
      intro l
      exact ((hg.fderiv_right (m := 0) (by simp)).clm_apply contDiff_const).continuous
    fin_cases k
    · exact hc 2
    · exact (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (EuclideanSpace.proj (j,2) : M F →L[ℝ] ℝ).continuous)).mul (hc 0)
    · exact (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (EuclideanSpace.proj (j,2) : M F →L[ℝ] ℝ).continuous)).mul (hc 1)
  have he : (fun y => (normSquare (smoothGradient s hs)
      ((H.atlas U).components ⟨i, Quotient.mk _ y⟩) : ℝ)) =
      (fun y => ∑ j : Fin (d F), ∑ k : Fin 3,
        ‖HyperbolicChart.differential (d F)
          (fun x => (s i).val (labeledA (placeEquiv F ζ hζ) x))
          (labeledAInv (placeEquiv F ζ hζ) y) j k‖ ^ 2) := by
    funext y
    exact smoothGradient_at_arch s hs i y
  change Continuous (fun y => (normSquare (smoothGradient s hs)
      ((H.atlas U).components ⟨i, Quotient.mk _ y⟩) : ℝ))
  rw [he]
  exact continuous_finset_sum _ (fun j _ => continuous_finset_sum _
    (fun k _ => ((hd j k).comp hAi).norm.pow 2))

theorem smoothGradient_cusp_coframe
    (s : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H)
    (hs : KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ U R P H s)
    (c : KPMsFixedHaarDisintegration.CuspIndex (H.atlas U))
    (p : KPCuspCharts.Cross F) (t : ℝ) :
    (∑ i : Fin (KPContCotangentActualOverlap.d F), ∑ k : Fin 3,
      ‖HyperbolicChart.differential (KPContCotangentActualOverlap.d F)
        (fun x => (s c.1).val
          (((H.atlas U).cuspAtlas c.1).representative c.2 •
            KPContCotangentActualOverlap.labeledA
              (KPContCotangentActualOverlap.placeEquiv F ζ hζ) x))
        (KPContCotangentActualOverlap.labeledAInv
          (KPContCotangentActualOverlap.placeEquiv F ζ hζ)
          (KPCuspCharts.toArch F (p, t))) i k‖ ^ 2) =
    (normSquare (smoothGradient s hs) ((H.atlas U).components ⟨c.1, Quotient.mk _
      (KPContSectorSmoothFramesSupport.cuspPoint F ζ hζ U R P H c.1 c.2 (p,t))⟩) : ℝ) := by
  let places := placeEquiv F ζ hζ
  let σ := ((H.atlas U).cuspAtlas c.1).representative c.2
  let z := KPCuspCharts.toArch F (p,t)
  let x := labeledAInv places z
  let ψ := rationalCoordinates F places σ
  let g : M F → ℂ := fun x => (s c.1).val (labeledA places x)
  have hA : ∀ y : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA places (labeledAInv places y) = y := by
    intro y
    funext k
    simp [labeledA, labeledAInv]
  have he : (fun x => (s c.1).val (σ • labeledA places x)) = g ∘ ψ := by
    funext y
    change (s c.1).val (σ • labeledA places y) =
      (s c.1).val (labeledA places (labeledAInv places (σ • labeledA places y)))
    rw [hA]
  have hsm := rational_smooth_metric F places σ
  have hg : DifferentiableAt ℝ g (ψ x) := by
    have hsg : ContDiff ℝ (⊤ : ℕ∞) (s c.1).val :=
      hs c.1
    have hla : ContDiff ℝ (⊤ : ℕ∞) (labeledA places) := by
      apply contDiff_pi.mpr
      intro k
      exact (ContinuousLinearMap.proj (places.symm k) : KPArch.Space (d F) →L[ℝ] KPArch.H3).contDiff.comp
        (CotangentLogCoframe.A (d F)).contDiff
    exact (hsg.comp hla).differentiable (by simp) |>.differentiableAt
  have hn := differential_norm_isometry (d F) ψ x
    (hsm.1.differentiable (by simp) |>.differentiableAt) (hsm.2 x) g hg
  change (∑ i, ∑ k, ‖HyperbolicChart.differential (d F)
    (fun x => (s c.1).val (σ • labeledA places x)) x i k‖ ^ 2) = _
  rw [he, hn]
  have hx : ψ x = labeledAInv places (σ • z) := by
    change labeledAInv places (σ • labeledA places (labeledAInv places z)) = _
    rw [hA]
  rw [hx]
  exact (smoothGradient_at_arch s hs c.1 (σ • z)).symm

 theorem arch_coframe_norm (n : ℕ) (g : KPArch.Space n → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : KPArch.Space n) :
    (∑ i, ∑ k, ‖HyperbolicChart.differential n (g ∘ KPMeanZeroWeightedEnergy.archCoordinates n)
      (KPMeanZeroWeightedEnergy.realCoordinates n z) i k‖ ^ 2) =
      KPContActualChamberOutgoingAdapter.covariantNorm n 1 g z ^ 2 := by
  let A := CotangentLogCoframe.A n
  have he : (g ∘ KPMeanZeroWeightedEnergy.archCoordinates n) = g ∘ A := by
    funext x
    apply congrArg g
    funext i
    apply Prod.ext
    · simp [A, CotangentLogCoframe.A_apply, KPMeanZeroWeightedEnergy.archCoordinates,
      Complex.mk_eq_add_mul_I, mul_comm]
    · rfl
  have hi : A (KPMeanZeroWeightedEnergy.realCoordinates n z) = z := by
    funext i
    apply Prod.ext
    · simpa [A, CotangentLogCoframe.A_apply, KPMeanZeroWeightedEnergy.realCoordinates, mul_comm] using
        Complex.re_add_im (z i).1
    · rfl
  have hdf := fderiv_comp (KPMeanZeroWeightedEnergy.realCoordinates n z)
    (hg.differentiable (by simp) _) A.differentiableAt
  rw [he]
  have ht : ∀ v : Fin n × Fin 3,
      (CotangentLogCoframe.j n (HyperbolicChart.differential n (g ∘ A)
        (KPMeanZeroWeightedEnergy.realCoordinates n z))) v =
        KPContActualChamberOutgoingAdapter.frameDerivative n v g z := by
    intro v
    rw [differential_frame_any, hdf, ContinuousLinearMap.comp_apply, hi]
    rw [A.fderiv]
    rcases v with ⟨i,k⟩
    have hv : A (CotangentLogCoframe.H n (KPMeanZeroWeightedEnergy.realCoordinates n z)
        (EuclideanSpace.basisFun _ ℝ (i,k))) =
        (if k = 0 then 1 else KPArch.height (z i)) •
          KPContActualSphericalFlatStage.coordinateDirection n i
            (if k = 0 then 2 else if k = 1 then 0 else 1) := by
      funext j
      apply Prod.ext
      · apply Complex.ext <;>
          fin_cases k <;> simp [A, CotangentLogCoframe.A_apply, CotangentLogCoframe.H, CotangentLogCoframe.C,
            EuclideanSpace.basisFun_apply, KPContActualSphericalFlatStage.coordinateDirection,
            KPMeanZeroWeightedEnergy.realCoordinates, KPArch.height, eq_comm, Complex.real_smul]
        all_goals
          simp only [Pi.single_apply, EuclideanSpace.single_apply, PiLp.single_apply]
          split_ifs <;> simp_all [KPArch.height, ← Complex.ofReal_exp]
      · fin_cases k <;> simp [A, CotangentLogCoframe.A_apply, CotangentLogCoframe.H, CotangentLogCoframe.C,
            EuclideanSpace.basisFun_apply, KPContActualSphericalFlatStage.coordinateDirection,
            KPMeanZeroWeightedEnergy.realCoordinates, KPArch.height, eq_comm, Complex.real_smul]
        all_goals
          simp only [Pi.single_apply, EuclideanSpace.single_apply, PiLp.single_apply]
          split_ifs <;> simp_all [KPArch.height, ← Complex.ofReal_exp]
    change fderiv ℝ g z (A _) = _
    rw [hv, map_smul]
    rfl
  have hj : (∑ i, ∑ k, ‖HyperbolicChart.differential n (g ∘ A)
      (KPMeanZeroWeightedEnergy.realCoordinates n z) i k‖ ^ 2) =
      ∑ v, ‖(CotangentLogCoframe.j n (HyperbolicChart.differential n (g ∘ A)
        (KPMeanZeroWeightedEnergy.realCoordinates n z))) v‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    simp [CotangentLogCoframe.j, Fin.sum_univ_three]
  rw [hj]
  simp_rw [ht]
  simp only [KPContActualChamberOutgoingAdapter.covariantNorm, Fin.reduceEq, ite_false, ite_true]
  exact (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm

private theorem arch_coframe_norm_at (n : ℕ) (g : KPArch.Space n → ℂ)
    (z : KPArch.Space n) (hg : DifferentiableAt ℝ g z) :
    (∑ i, ∑ k, ‖HyperbolicChart.differential n (g ∘ KPMeanZeroWeightedEnergy.archCoordinates n)
      (KPMeanZeroWeightedEnergy.realCoordinates n z) i k‖ ^ 2) =
      KPContActualChamberOutgoingAdapter.covariantNorm n 1 g z ^ 2 := by
  let A := CotangentLogCoframe.A n
  have he : (g ∘ KPMeanZeroWeightedEnergy.archCoordinates n) = g ∘ A := by
    funext x
    apply congrArg g
    funext i
    apply Prod.ext
    · simp [A, CotangentLogCoframe.A_apply, KPMeanZeroWeightedEnergy.archCoordinates,
      Complex.mk_eq_add_mul_I, mul_comm]
    · rfl
  have hi : A (KPMeanZeroWeightedEnergy.realCoordinates n z) = z := by
    funext i
    apply Prod.ext
    · simpa [A, CotangentLogCoframe.A_apply, KPMeanZeroWeightedEnergy.realCoordinates, mul_comm] using
        Complex.re_add_im (z i).1
    · rfl
  have hdf := fderiv_comp (KPMeanZeroWeightedEnergy.realCoordinates n z)
    (by simpa [hi] using hg) A.differentiableAt
  rw [he]
  have ht : ∀ v : Fin n × Fin 3,
      (CotangentLogCoframe.j n (HyperbolicChart.differential n (g ∘ A)
        (KPMeanZeroWeightedEnergy.realCoordinates n z))) v =
        KPContActualChamberOutgoingAdapter.frameDerivative n v g z := by
    intro v
    rw [differential_frame_any, hdf, ContinuousLinearMap.comp_apply, hi]
    rw [A.fderiv]
    rcases v with ⟨i,k⟩
    have hv : A (CotangentLogCoframe.H n (KPMeanZeroWeightedEnergy.realCoordinates n z)
        (EuclideanSpace.basisFun _ ℝ (i,k))) =
        (if k = 0 then 1 else KPArch.height (z i)) •
          KPContActualSphericalFlatStage.coordinateDirection n i
            (if k = 0 then 2 else if k = 1 then 0 else 1) := by
      funext j
      apply Prod.ext
      · apply Complex.ext <;>
          fin_cases k <;> simp [A, CotangentLogCoframe.A_apply, CotangentLogCoframe.H, CotangentLogCoframe.C,
            EuclideanSpace.basisFun_apply, KPContActualSphericalFlatStage.coordinateDirection,
            KPMeanZeroWeightedEnergy.realCoordinates, KPArch.height, eq_comm, Complex.real_smul]
        all_goals
          simp only [Pi.single_apply, EuclideanSpace.single_apply, PiLp.single_apply]
          split_ifs <;> simp_all [KPArch.height, ← Complex.ofReal_exp]
      · fin_cases k <;> simp [A, CotangentLogCoframe.A_apply, CotangentLogCoframe.H, CotangentLogCoframe.C,
            EuclideanSpace.basisFun_apply, KPContActualSphericalFlatStage.coordinateDirection,
            KPMeanZeroWeightedEnergy.realCoordinates, KPArch.height, eq_comm, Complex.real_smul]
        all_goals
          simp only [Pi.single_apply, EuclideanSpace.single_apply, PiLp.single_apply]
          split_ifs <;> simp_all [KPArch.height, ← Complex.ofReal_exp]
    change fderiv ℝ g z (A _) = _
    rw [hv, map_smul]
    rfl
  have hj : (∑ i, ∑ k, ‖HyperbolicChart.differential n (g ∘ A)
      (KPMeanZeroWeightedEnergy.realCoordinates n z) i k‖ ^ 2) =
      ∑ v, ‖(CotangentLogCoframe.j n (HyperbolicChart.differential n (g ∘ A)
        (KPMeanZeroWeightedEnergy.realCoordinates n z))) v‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    simp [CotangentLogCoframe.j, Fin.sum_univ_three]
  rw [hj]
  simp_rw [ht]
  simp only [KPContActualChamberOutgoingAdapter.covariantNorm, Fin.reduceEq, ite_false, ite_true]
  exact (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm

 theorem coframe_reindex (m n : ℕ) (h : m = n) (g : KPArch.Space n → ℂ)
    (y : KPArch.Space n) :
    (∑ j : Fin m, ∑ k : Fin 3, ‖HyperbolicChart.differential m
      (fun x => g (fun r => CotangentLogCoframe.A m x ((finCongr h).symm r)))
      ((CotangentLogCoframe.A m).symm (fun r => y (finCongr h r))) j k‖ ^ 2) =
    ∑ j : Fin n, ∑ k : Fin 3, ‖HyperbolicChart.differential n
      (g ∘ KPMeanZeroWeightedEnergy.archCoordinates n)
      (KPMeanZeroWeightedEnergy.realCoordinates n y) j k‖ ^ 2 := by
  subst n
  simp only [finCongr_refl, Equiv.refl_symm, Equiv.refl_apply]
  have he : (fun x : HyperbolicChart.Space m => g (fun r => CotangentLogCoframe.A m x r)) =
      (g ∘ KPMeanZeroWeightedEnergy.archCoordinates m) := by
    funext x
    apply congrArg g
    funext i
    apply Prod.ext
    · simp [CotangentLogCoframe.A_apply, KPMeanZeroWeightedEnergy.archCoordinates,
      Complex.mk_eq_add_mul_I, mul_comm]
    · rfl
  rw [he]
  rfl

end DedekindZetaZeroFree.KPContThreeL2CotangentHelpers

namespace DedekindZetaZeroFree.KPContThreeL2EndHelpers
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
 abbrev Base := KPFiniteCuspAtlas.rawXU F ζ hζ U
 abbrev CuspIndex := KPContActualCollarBuffer.CuspIndex F ζ hζ U R P H
private theorem endChart_continuous (τ : ℝ) (c : CuspIndex F ζ hζ U R P H) :
    Continuous (KPContActualCollarBuffer.endChart F ζ hζ U R P H τ c) := by
  apply Continuous.comp _ (show Continuous (KPFiniteCuspAtlas.endMap F
    (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative c.1))
    (((H.atlas U).cuspAtlas c.1).cusp c.2)
    (((H.atlas U).cuspAtlas c.1).representative c.2) τ) from ?_)
  · have hh := (H.atlas U).components.continuous.comp (continuous_sigmaMk (i := c.1))
    simpa only [Function.comp_def, (H.atlas U).components_formula] using hh
  · apply Continuous.quotient_lift
    have hact : Continuous (KPCuspSiegel.action F (((H.atlas U).cuspAtlas c.1).representative c.2)) :=
      (by unfold KPCuspSiegel.action KPCuspSiegel.glAction
          exact (KPArch.productAction_contDiff _ _).continuous)
    exact continuous_quotient_mk'.comp
      (hact.comp ((KPCuspCharts.toArch_contDiff F).continuous.comp continuous_subtype_val))
private theorem compact_slab (c : CuspIndex F ζ hζ U R P H) (L B : ℝ) :
    ∃ K : Set (Base F ζ hζ U), IsCompact K ∧
      ∀ z : KPCuspCharts.Coordinates F, z.2 ∈ Set.Icc L B →
        KPContActualCollarBuffer.chartLift F ζ hζ U R P H c z ∈ K := by
  let G := ((H.atlas U).cuspAtlas c.1).geometry c.2
  let S := KPContActualCollarBuffer.Stabilizer F ζ hζ U R P H c
  letI : CompactSpace (KPCuspCharts.CrossQuotient F S) := G.compact_cross
  letI : CompactSpace (Set.Icc L B) := isCompact_iff_compactSpace.mp isCompact_Icc
  let f : KPCuspCharts.CrossQuotient F S × Set.Icc L B → Base F ζ hζ U := fun p =>
    KPContActualCollarBuffer.endChart F ζ hζ U R P H (L-1) c
      (G.highPresentation (L-1) (p.1, ⟨p.2.val, by change L-1 < p.2.val; have := p.2.property.1; linarith⟩))
  have hf : Continuous f := (endChart_continuous F ζ hζ U R P H (L-1) c).comp
    ((G.highPresentation (L-1)).continuous.comp (by fun_prop))
  refine ⟨Set.range f, isCompact_range hf, ?_⟩
  intro z hz
  refine ⟨(Quotient.mk _ z.1, ⟨z.2,hz⟩), ?_⟩
  dsimp only [f]
  rw [G.highPresentation_formula]
  rfl
private theorem end_lift_range (τ : ℝ) (c : CuspIndex F ζ hζ U R P H) :
    KPContActualCollarBuffer.chartLift F ζ hζ U R P H c ''
      {z : KPCuspCharts.Coordinates F | τ < z.2} =
    KPContActualCollarBuffer.endSet F ζ hζ U R P H τ c := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨KPCuspSiegel.projection F _
      (((H.atlas U).cuspAtlas c.1).representative c.2 • KPCuspCharts.toArch F z), ?_, rfl⟩
    refine ⟨_, ⟨KPCuspCharts.toArch F z, ?_, rfl⟩, rfl⟩
    change τ < KPCuspLogShape.meanHeight _ (KPCuspCharts.toArch F z)
    rw [KPCuspCharts.toArch_meanHeight F (((H.atlas U).cuspAtlas c.1).geometry c.2).positive_dimension]
    exact hz
  · rintro ⟨u,⟨w,⟨v,hv,rfl⟩,rfl⟩,rfl⟩
    let z := (KPCuspCharts.toArchHomeomorph F
      (((H.atlas U).cuspAtlas c.1).geometry c.2).positive_dimension).symm v
    refine ⟨z, hv, ?_⟩
    change KPContActualCollarBuffer.chartLift F ζ hζ U R P H c z = _
    simp only [KPContActualCollarBuffer.chartLift]
    congr 2
    exact congrArg (fun w => (((H.atlas U).cuspAtlas c.1).representative c.2 • w))
      ((KPCuspCharts.toArchHomeomorph F _).apply_symm_apply v)
private theorem all_ends_open (t : ℝ) (c : CuspIndex F ζ hζ U R P H) :
    IsOpen (KPContActualCollarBuffer.endSet F ζ hζ U R P H t c) := by
  have hop : IsOpenMap (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative c.1)) := by
    have he := (H.atlas U).components.isOpenMap.comp (isOpenMap_sigmaMk (i := c.1))
    simpa only [Function.comp_def, (H.atlas U).components_formula] using he
  exact hop _ (KPFiniteAdelicCuspEnds.component_open_end F _ _ t)
private theorem compact_truncated_core (B : ℝ) :
    IsCompact ((⋃ c : CuspIndex F ζ hζ U R P H,
      KPContActualCollarBuffer.endSet F ζ hζ U R P H B c)ᶜ) := by
  classical
  choose K hK hslab using (fun c : CuspIndex F ζ hζ U R P H =>
    compact_slab F ζ hζ U R P H c (H.atlas U).threshold B)
  let core := (⋃ c : CuspIndex F ζ hζ U R P H,
      KPContActualCollarBuffer.endSet F ζ hζ U R P H (H.atlas U).threshold c)ᶜ
  have hc : IsCompact core := by
    convert (H.atlas U).compact_core using 1
    ext x
    simp only [core, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_diff, Set.mem_univ,
      true_and, KPContActualCollarBuffer.endSet]
    simp only [Sigma.exists]
  have hcompact : IsCompact (core ∪ ⋃ c, K c) := hc.union (isCompact_iUnion hK)
  apply hcompact.of_isClosed_subset
  · exact (isOpen_iUnion (all_ends_open F ζ hζ U R P H B)).isClosed_compl
  · intro x hx
    by_cases hcore : x ∈ core
    · exact Or.inl hcore
    · right
      have hh : x ∈ ⋃ c : CuspIndex F ζ hζ U R P H,
          KPContActualCollarBuffer.endSet F ζ hζ U R P H (H.atlas U).threshold c :=
        not_not.mp hcore
      obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hh
      rw [← end_lift_range F ζ hζ U R P H (H.atlas U).threshold c] at hc
      obtain ⟨z,hz,rfl⟩ := hc
      have hzB : z.2 ≤ B := by
        by_contra hn
        apply hx
        exact Set.mem_iUnion.mpr ⟨c, by rw [← end_lift_range F ζ hζ U R P H B c]; exact ⟨z,lt_of_not_ge hn,rfl⟩⟩
      exact Set.mem_iUnion.mpr ⟨c,hslab c z ⟨hz.le,hzB⟩⟩
end DedekindZetaZeroFree.KPContThreeL2EndHelpers

namespace DedekindZetaZeroFree.KPContThreeL2CompactBoundHelpers
private theorem clm_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (O : Set ℂ) (hO : IsOpen O) (j : ℂ → E) (hj : DifferentiableOn ℂ j O)
    (k : ℕ) (s : ℂ) (hs : s ∈ O) (L : E →L[ℂ] ℂ) :
    iteratedDerivWithin k (fun z => L (j z)) O s = L (iteratedDerivWithin k j O s) := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin]
  change ((iteratedFDerivWithin ℂ k (L ∘ j) O s) fun _ => 1) = _
  rw [L.iteratedFDerivWithin_comp_left ((hj.contDiffOn hO (n := (⊤ : ℕ∞ω))).contDiffWithinAt hs) hO.uniqueDiffOn hs (by simp)]
  rfl
open KPContLocalNorm

private theorem tuple_parameter_jet_joint {n m : ℕ} (A : LocalBall n)
    (O : Set ℂ) (hO : IsOpen O) (v : ℂ → Space n → ℂ)
    (hv : KPCutoffSource.ChartSmoothHolomorphicOn A v O)
    (K : Set (Space n)) (hK : IsCompact K) (hKA : K ⊆ A.carrier)
    (k : ℕ) (α : MultiIndex n m) :
    ContinuousOn (fun p : ℂ × Space n => iteratedDerivWithin k
      (fun z => coordinateDerivative α (v z) p.2) O p.1) (O ×ˢ K) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨j,hj,he⟩ := hv.2 K hK hKA m
  have hc := (hj.contDiffOn hO (n := (⊤ : ℕ∞ω))).continuousOn_iteratedDerivWithin
    (m := k) (by simp) hO.uniqueDiffOn
  have hp : ContinuousOn (fun z => (iteratedDerivWithin k j O z) α) O :=
    (continuous_apply α).comp_continuousOn hc
  have hcont : ContinuousOn (fun p : ℂ × K =>
      (iteratedDerivWithin k j O p.1) α p.2) (O ×ˢ Set.univ) :=
    continuous_eval.comp_continuousOn ((hp.comp continuous_fst.continuousOn
      (fun _ h => h.1)).prodMk continuous_snd.continuousOn)
  apply continuousOn_iff_continuous_restrict.mpr
  let a : (O ×ˢ K) → ℂ × K := fun p => (p.val.1, ⟨p.val.2,p.property.2⟩)
  have ha : Continuous a := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun p => p.property.2))
  apply (hcont.comp_continuous ha (fun p => ⟨p.property.1, Set.mem_univ _⟩)).congr
  intro p
  let ev : CompactJets K m →L[ℂ] ℂ :=
    (ContinuousMap.evalCLM ℂ (⟨p.val.2,p.property.2⟩ : K)).comp (ContinuousLinearMap.proj α)
  have heq : Set.EqOn (fun z => coordinateDerivative α (v z) p.val.2)
      (fun z => ev (j z)) O := fun z hz => (he z hz α ⟨p.val.2,p.property.2⟩).symm
  change _ = iteratedDerivWithin k (fun z => coordinateDerivative α (v z) p.val.2) O p.val.1
  rw [iteratedDerivWithin_congr heq p.property.1, clm_jet O hO j hj k p.val.1 p.property.1 ev]
  rfl

end DedekindZetaZeroFree.KPContThreeL2CompactBoundHelpers

namespace DedekindZetaZeroFree.KPContThreeL2GradientCompactHelpers
open KPContLocalNorm
private theorem list_index {n : ℕ} (l : List (Fin n)) :
    ∃ m, ∃ α : MultiIndex n m, l.Perm α.directions := by
  classical
  let m := ∑ i : Fin n, l.count i
  let α : MultiIndex n m := ⟨fun i => ⟨l.count i, by
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (l.count j)) (Finset.mem_univ i)
    dsimp [m]; omega⟩, by simp [m]⟩
  refine ⟨m, α, List.perm_iff_count.mpr ?_⟩
  intro i
  rw [MultiIndex.directions, List.count_flatMap,
    ← List.sum_toFinset _ (List.nodup_finRange n)]
  simp [α, Function.comp_def, List.count_replicate]

private theorem flat_word (n : ℕ) (w : List (Fin n)) (u : Space n → ℂ) :
    RightFrame.PullbackWords.directionalWord (fun i _ => EuclideanSpace.single i (1:ℝ)) w u =
      coordinateDerivativeList w u := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [RightFrame.PullbackWords.directionalWord, coordinateDerivativeList, ih]

private theorem compact_coordinate_jets_transport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : ℕ} (B : LocalBall d) (O : Set ℂ)
    (g : ℂ → Space d → ℂ) (hg : KPCutoffSource.ChartSmoothHolomorphicOn B g O)
    (D : Set E) (hD : IsOpen D) (ψ : E → Space d)
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ D) (hψB : Set.MapsTo ψ D B.carrier)
    (K : Set E) (hK : IsCompact K) (hKD : K ⊆ D) (n : ℕ) (v : Fin n → E) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j O ∧ ∀ z ∈ O, ∀ x : K,
      j z x = iteratedFDerivWithin ℝ n (g z ∘ ψ) D x.val v := by
  apply KPContActualChamberCasimirJets.normalSeries_transported_compact_jet
    B.carrier Metric.isOpen_ball D hD
    (fun i _ => EuclideanSpace.single i (1:ℝ)) (fun _ => contDiffOn_const)
    (fun x _ => ⟨(EuclideanSpace.basisFun (Fin d) ℝ).toBasis,
      fun i => EuclideanSpace.basisFun_apply (Fin d) ℝ i⟩)
    ψ hψ hψB O g hg.1 ?_ K hK hKD n v
  intro w C hC hCB
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  obtain ⟨m,α,hperm⟩ := list_index w
  obtain ⟨j,hj,hjval⟩ := hg.2 C hC hCB m
  let L : CompactJets C m →L[ℂ] C(C,ℂ) := ContinuousLinearMap.proj α
  refine ⟨fun z => L (j z), L.differentiable.comp_differentiableOn hj, ?_⟩
  intro z hz x
  rw [flat_word, WeakJets.Raw.coordinateDerivativeList_perm_on hperm (hg.1 z hz) (hCB x.property)]
  exact hjval z hz α x
end DedekindZetaZeroFree.KPContThreeL2GradientCompactHelpers

namespace DedekindZetaZeroFree.KPContActualChamberThreeL2Tails

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

abbrev V : Set ℂ := KPContActualChamberCasimirJets.V
abbrev level := KPContActualAllCuspSource.level F ζ hζ C R P H U
abbrev Base := KPContActualAllCuspSource.Base F ζ hζ C R P H U
abbrev Covered := KPContActualAllCuspSource.Covered F ζ hζ C R P H U
abbrev Sector := KPContActualAllCuspSource.Sector F ζ hζ C R P H U
abbrev Sections := KPContSectorSmoothFramesSupport.Sections F ζ hζ
  (level F ζ hζ C R P H U) R P H
abbrev SmoothSections := KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
abbrev BorelL2Sections := KPContSectorLineL2Isometry.BorelL2Sections F ζ hζ
  (level F ζ hζ C R P H U) R P H
abbrev measure := KPContActualAllCuspSource.measure F ζ hζ C R P H U
abbrev baseMeasure := KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P
  (level F ζ hζ C R P H U)
abbrev Frame (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount) :=
  KPContActualChamberCasimirJets.Frame F ζ hζ C R P H U i

abbrev GradientFamily := KPContActualCotangentMeasurableFamilies.MeasurableCotangentFamily
  F ζ hζ (level F ζ hζ C R P H U) R P H

def tail (A : ℝ) : Set (Base F ζ hζ C R P H U) :=
  KPCuspCutoffGraph.highEnds F ζ hζ H.totallyComplex (level F ζ hζ C R P H U)
    (H.atlas (level F ζ hζ C R P H U)) A

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (f : ℂ → S)
variable {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U →
  KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
  KPContinuation.spectralDomain f χ)

def g (k : ℕ) (s : ℂ) (x : Covered F ζ hζ C R P H U) : ℂ :=
  iteratedDerivWithin k (fun z =>
    KPContActualChamberNormalSeries.E F ζ hζ U ι f z
      (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U x) -
    KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff z) x) V s

def h (k : ℕ) (s : ℂ) (x : Covered F ζ hζ C R P H U) : ℂ :=
  iteratedDerivWithin k (fun z =>
    KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
      (source.descent.commutator z) x) V s

theorem genuine (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    g F ζ hζ C R P H U ι f buffer χ source k s ∈
      KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ (level F ζ hζ C R P H U) ∧
    h F ζ hζ C R P H U ι f buffer χ source k s ∈
      KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ (level F ζ hζ C R P H U) := by
  obtain ⟨eE, heE, -, -⟩ :=
    KPContActualChamberNormalSeries.descent_series F ζ hζ C R P H U ι f hι hf
  have hvalE : ∀ w ∈ V, ∀ x, (eE w).val x =
      KPContActualChamberNormalSeries.E F ζ hζ U ι f w
        (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U x) := by
    intro w hw x
    rw [← heE w hw (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U x),
      KPContActualChamberNormalSeries.coveredRepresentative_projection]
  let eC : ℂ → KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ
      (level F ζ hζ C R P H U) := fun w =>
    ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ (level F ζ hζ C R P H U) R P H).symm
      (source.descent.cutoff w)).val
  have hvalC : ∀ w x, (eC w).val x = KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
      (source.descent.cutoff w) x := fun w x => rfl
  let eK : ℂ → KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ
      (level F ζ hζ C R P H U) := fun w =>
    ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ (level F ζ hζ C R P H U) R P H).symm
      (source.descent.commutator w)).val
  have hvalK : ∀ w x, (eK w).val x = KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
      (source.descent.commutator w) x := fun w x => rfl
  have hg : g F ζ hζ C R P H U ι f buffer χ source k s =
      fun v => iteratedDerivWithin k (fun z =>
        KPContActualChamberNormalSeries.E F ζ hζ U ι f z
          (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U v) -
        KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff z) v) V s := by
    funext v; rfl
  have hh : h F ζ hζ C R P H U ι f buffer χ source k s =
      fun v => iteratedDerivWithin k (fun z =>
        KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
          (source.descent.commutator z) v) V s := by
    funext v; rfl
  constructor
  · rw [hg]
    intro ε v
    simp only []
    have hsum : iteratedDerivWithin k (fun z =>
          KPContActualChamberNormalSeries.E F ζ hζ U ι f z
            (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
              (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v)) -
          KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff z)
            (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v)) V s =
        iteratedDerivWithin k (fun z =>
          (eE z).val (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v) -
          (eC z).val (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v)) V s :=
      iteratedDerivWithin_congr (fun z hz => by
        rw [← hvalE z hz (KPContSectorCoveredQuotientVocabulary.z F ζ hζ
              (level F ζ hζ C R P H U) ε v),
          ← hvalC z (KPContSectorCoveredQuotientVocabulary.z F ζ hζ
              (level F ζ hζ C R P H U) ε v)]) hs
    have hA : iteratedDerivWithin k (fun z =>
          (eE z).val (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v) -
          (eC z).val (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v)) V s =
        iteratedDerivWithin k (fun z =>
          (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
            ((eE z).val v - (eC z).val v)) V s :=
      iteratedDerivWithin_congr (fun z _ => by
        rw [(eE z).property ε v, (eC z).property ε v]; ring) hs
    have hcm : iteratedDerivWithin k (fun z =>
          (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
            ((eE z).val v - (eC z).val v)) V s =
        (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
          iteratedDerivWithin k (fun z => (eE z).val v - (eC z).val v) V s :=
      iteratedDerivWithin_const_mul_field _ _
    have hZ : iteratedDerivWithin k (fun z => (eE z).val v - (eC z).val v) V s =
        iteratedDerivWithin k (fun z =>
          KPContActualChamberNormalSeries.E F ζ hζ U ι f z
            (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U v) -
          KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff z) v) V s :=
      iteratedDerivWithin_congr (fun z hz => by rw [hvalE z hz v, hvalC z v]) hs
    rw [hsum, hA, hcm, hZ]
  · rw [hh]
    intro ε v
    simp only []
    have hsum : iteratedDerivWithin k (fun z =>
          KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.commutator z)
            (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v)) V s =
        iteratedDerivWithin k (fun z =>
          (eK z).val (KPContSectorCoveredQuotientVocabulary.z F ζ hζ
            (level F ζ hζ C R P H U) ε v)) V s :=
      iteratedDerivWithin_congr (fun z _ => hvalK z
        (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v)) hs
    have hA : iteratedDerivWithin k (fun z =>
          (eK z).val (KPContSectorCoveredQuotientVocabulary.z F ζ hζ
            (level F ζ hζ C R P H U) ε v)) V s =
        iteratedDerivWithin k (fun z =>
          (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) * (eK z).val v) V s :=
      iteratedDerivWithin_congr (fun z _ => (eK z).property ε v) hs
    have hcm : iteratedDerivWithin k (fun z =>
          (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) * (eK z).val v) V s =
        (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
          iteratedDerivWithin k (fun z => (eK z).val v) V s :=
      iteratedDerivWithin_const_mul_field _ _
    have hZ : iteratedDerivWithin k (fun z => (eK z).val v) V s =
        iteratedDerivWithin k (fun z =>
          KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
            (source.descent.commutator z) v) V s :=
      (iteratedDerivWithin_congr (fun z _ => hvalK z v) hs).symm
    rw [hsum, hA, hcm, hZ]

variable (hι : Function.Injective ι)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)

def coveredG (k : ℕ) (s : ℂ) :
    KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ (level F ζ hζ C R P H U) :=
  if hs : s ∈ V then ⟨_, (genuine F ζ hζ C R P H U ι f buffer χ source hι hf k s hs).1⟩ else 0

def coveredH (k : ℕ) (s : ℂ) :
    KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ (level F ζ hζ C R P H U) :=
  if hs : s ∈ V then ⟨_, (genuine F ζ hζ C R P H U ι f buffer χ source hι hf k s hs).2⟩ else 0

def lineG (k : ℕ) (s : ℂ) : Sections F ζ hζ C R P H U :=
  KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H
    (coveredG F ζ hζ C R P H U ι f buffer χ source hι hf k s)

def lineH (k : ℕ) (s : ℂ) : Sections F ζ hζ C R P H U :=
  KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H
    (coveredH F ζ hζ C R P H U ι f buffer χ source hι hf k s)

open KPContLocalNorm

private theorem point_holomorphic {n : ℕ} (A : LocalBall n) (Ω : Set ℂ)
    (g : ℂ → Space n → ℂ) (hg : KPCutoffSource.ChartSmoothHolomorphicOn A g Ω)
    (x : Space n) (hx : x ∈ A.carrier) : DifferentiableOn ℂ (fun s => g s x) Ω := by
  let K : Set (Space n) := {x}
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_singleton : IsCompact K)
  obtain ⟨j,hj,he⟩ := hg.2 K isCompact_singleton (Set.singleton_subset_iff.mpr hx) 0
  let α : MultiIndex n 0 := ⟨fun _ => 0,by simp⟩
  let L : CompactJets K 0 →L[ℂ] ℂ :=
    (ContinuousMap.evalCLM ℂ (⟨x,rfl⟩ : K)).comp (ContinuousLinearMap.proj α)
  apply (L.differentiable.comp_differentiableOn hj).congr
  intro s hs
  have h := he s hs α ⟨x,rfl⟩
  have hd : α.directions = [] := by
    simp only [MultiIndex.directions,α,List.replicate_zero]
    induction List.finRange n with
    | nil => rfl
    | cons i l ih => simpa using ih
  simpa [L,coordinateDerivative,hd,coordinateDerivativeList] using h.symm

private theorem realCoordinates_inverse_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (KPContActualChartRestrictionDensity.coordinates F).symm := by
  rw [contDiff_piLp]
  intro k
  dsimp [KPContActualChartRestrictionDensity.coordinates, KPArchRealCoordinates.coordinates]
  split_ifs
  · exact Complex.reCLM.contDiff.comp ((contDiff_apply ℝ (ℂ × ℝ) _).fst)
  · exact Complex.imCLM.contDiff.comp ((contDiff_apply ℝ (ℂ × ℝ) _).fst)
  · exact (contDiff_apply ℝ (ℂ × ℝ) _).snd

private theorem E_holo (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (x : KPContActualChamberNormalSeries.G F ζ hζ) :
    DifferentiableOn ℂ (fun s => KPContActualChamberNormalSeries.E F ζ hζ U ι f s x) V := by
  let A : Set (KPContActualChamberNormalSeries.G F ζ hζ) := {x}
  letI : CompactSpace A := isCompact_iff_compactSpace.mp isCompact_singleton
  have hh := KPContActualChamberNormalSeries.compactMixedJet_holomorphic F ζ hζ U ι f hι hf 0 [] A isCompact_singleton
  have hd := (ContinuousMap.evalCLM ℂ (⟨x, Set.mem_singleton x⟩ : A)).differentiable.comp_differentiableOn hh
  apply hd.congr
  intro s hs
  simp [KPContActualChamberNormalSeries.compactMixedJet, hs,
    KPContActualChamberNormalSeries.mixedJet, KPContActualChamberNormalSeries.rightWord]

private theorem source_chart_neighborhood (b : Bool)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (y : KPFiniteCuspAtlas.SymmetricSpace F) :
    ∃ B : LocalBall (KPCuspLogShape.dimension F * 3),
      (KPContActualChartRestrictionDensity.coordinates F).symm y ∈ B.carrier ∧
      KPCutoffSource.ChartSmoothHolomorphicOn B
        (fun s => KPContActualAllCuspSource.chartCoefficient F ζ hζ C R P H U
          (if b then source.descent.commutator s else source.descent.cutoff s) i
          (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ (level F ζ hζ C R P H U) 1))
        KPContinuation.spectralDomain := by
  let O := (KPContSectorPhaseComponentCharts.orbifoldChart_exists F ζ hζ
    (level F ζ hζ C R P H U) R P H i y).some
  let x := (KPContActualChartRestrictionDensity.coordinates F).symm y
  have hx : x ∈ KPContActualChartRestrictionDensity.chartDomain F ζ hζ
      (level F ζ hζ C R P H U) R P H i y O := by
    change KPContActualChartRestrictionDensity.coordinates F x ∈ O.neighborhood
    rw [Homeomorph.apply_symm_apply]
    exact O.center_mem
  have hopen := O.isOpen.preimage (KPContActualChartRestrictionDensity.coordinates F).continuous
  obtain ⟨r, hr, hrD⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hx)
  have hn : 0 < KPCuspLogShape.dimension F * 3 := by
    have he := (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.1
    have hd := (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.2
    dsimp [KPCuspLogShape.dimension]
    positivity
  let B : LocalBall (KPCuspLogShape.dimension F * 3) := ⟨hn, x, r/2, by positivity⟩
  have hBD : KPContLocalCubeEmbedding.closedCarrier B ⊆
      KPContActualChartRestrictionDensity.chartDomain F ζ hζ
        (level F ζ hζ C R P H U) R P H i y O :=
    (Metric.closedBall_subset_ball (by change r/2 < r; linarith)).trans hrD
  refine ⟨B, Metric.mem_ball_self B.radius_pos, ?_⟩
  have hh := source.local_holomorphy i y O
    (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ (level F ζ hζ C R P H U) 1) B hBD
  cases b
  · exact hh.1
  · exact hh.2.1

private theorem source_coefficient_formula (b : Bool) (s : ℂ)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (x : Space (KPCuspLogShape.dimension F * 3)) :
    KPContActualAllCuspSource.chartCoefficient F ζ hζ C R P H U
      (if b then source.descent.commutator s else source.descent.cutoff s) i
      (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ (level F ζ hζ C R P H U) 1) x =
    KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
      (if b then source.descent.commutator s else source.descent.cutoff s)
      (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
        (level F ζ hζ C R P H U))
        (KPContActualChartRestrictionDensity.coordinates F x,
          (H.atlas (level F ζ hζ C R P H U)).representative i)) := by
  unfold KPContActualAllCuspSource.chartCoefficient
  rw [KPContActualChartRestrictionDensity.frameCoefficient_class,
    KPContSectorScalarLineAlgebra.S_apply]
  simp [KPContActualCutoffSmoothDescent.scalar]

private theorem source_component_holo (b : Bool)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (y : KPFiniteCuspAtlas.SymmetricSpace F) :
    DifferentiableOn ℂ (fun s => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
      (if b then source.descent.commutator s else source.descent.cutoff s)
      (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
        (level F ζ hζ C R P H U)) (y, (H.atlas (level F ζ hζ C R P H U)).representative i)))
      KPContinuation.spectralDomain := by
  obtain ⟨B, hx, hh⟩ := source_chart_neighborhood F ζ hζ C R P H U ι f buffer χ source b i y
  apply (point_holomorphic B _ _ hh _ hx).congr
  intro s hs
  rw [source_coefficient_formula, Homeomorph.apply_symm_apply]

private theorem source_component_jet_joint (b : Bool) (k : ℕ)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount) :
    ContinuousOn (fun p : ℂ × KPFiniteCuspAtlas.SymmetricSpace F =>
      iteratedDerivWithin k (fun z => KPContActualCutoffSmoothDescent.scalar
        F ζ hζ C R P H U
        (if b then source.descent.commutator z else source.descent.cutoff z)
        (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
          (level F ζ hζ C R P H U))
          (p.2, (H.atlas (level F ζ hζ C R P H U)).representative i))) V p.1)
      (V ×ˢ Set.univ) := by
  apply (KPChamberL2Defect.chamber_isOpen.prod isOpen_univ).continuousOn_iff.mpr
  intro p hp
  obtain ⟨B,hx,hh⟩ := source_chart_neighborhood F ζ hζ C R P H U ι f buffer χ source b i p.2
  obtain ⟨K,hK,hxK,hKB⟩ := exists_compact_subset Metric.isOpen_ball hx
  let α : MultiIndex (KPCuspLogShape.dimension F * 3) 0 := ⟨fun _ => 0,by simp⟩
  have hα : ∀ u x, coordinateDerivative α u x = u x := by
    intro u x
    have hd : α.directions = [] := by
      simp only [MultiIndex.directions,α,List.replicate_zero]
      induction List.finRange (KPCuspLogShape.dimension F * 3) with
      | nil => rfl
      | cons i l ih => simpa using ih
    simp [coordinateDerivative,hd,coordinateDerivativeList]
  have hj := KPContThreeL2CompactBoundHelpers.tuple_parameter_jet_joint B
    KPContinuation.spectralDomain KPContinuation.spectralDomain_isOpen _ hh K hK hKB k α
  have hpΩ : p.1 ∈ KPContinuation.spectralDomain := by
    change -(1 : ℝ)/6 < p.1.re
    have hr : (1 : ℝ)/3 < p.1.re := hp.1
    linarith
  have hnh : KPContinuation.spectralDomain ×ˢ K ∈
      𝓝 (p.1, (KPContActualChartRestrictionDensity.coordinates F).symm p.2) := by
    apply mem_nhds_prod_iff.mpr
    exact ⟨_, KPContinuation.spectralDomain_isOpen.mem_nhds hpΩ,
      _, Filter.mem_of_superset (isOpen_interior.mem_nhds hxK) interior_subset, Set.Subset.refl _⟩
  have ht := hj.continuousAt (x := (p.1, (KPContActualChartRestrictionDensity.coordinates F).symm p.2)) hnh
  let map : ℂ × KPFiniteCuspAtlas.SymmetricSpace F → ℂ × Space (KPCuspLogShape.dimension F * 3) :=
    fun q => (q.1, (KPContActualChartRestrictionDensity.coordinates F).symm q.2)
  have hm : ContinuousAt map p := continuousAt_fst.prodMk
    ((KPContActualChartRestrictionDensity.coordinates F).symm.continuous.continuousAt.comp continuousAt_snd)
  have hc := ht.comp_of_eq hm rfl
  apply hc.congr_of_eventuallyEq
  filter_upwards [((KPChamberL2Defect.chamber_isOpen.prod isOpen_univ).mem_nhds hp)] with q hq
  simp only [Function.comp_def, hα]
  rw [iteratedDerivWithin_of_isOpen KPContinuation.spectralDomain_isOpen (by
      change -(1 : ℝ)/6 < q.1.re
      have hr : (1 : ℝ)/3 < q.1.re := hq.1
      linarith),
    iteratedDerivWithin_of_isOpen KPChamberL2Defect.chamber_isOpen hq.1]
  congr 1
  funext z
  rw [source_coefficient_formula, Homeomorph.apply_symm_apply]

private theorem source_component_jet_smooth (b : Bool) (k : ℕ) (s : ℂ)
    (hs : s ∈ V) (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => iteratedDerivWithin k
      (fun z => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
        (if b then source.descent.commutator z else source.descent.cutoff z)
        (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
          (level F ζ hζ C R P H U)) (y, (H.atlas (level F ζ hζ C R P H U)).representative i))) V s) := by
  have hsΩ : s ∈ KPContinuation.spectralDomain := by
    change -(1 : ℝ)/6 < s.re
    change (1 : ℝ)/3 < s.re at hs
    linarith
  rw [contDiff_iff_contDiffAt]
  intro y
  obtain ⟨B, hx, hh⟩ := source_chart_neighborhood F ζ hζ C R P H U ι f buffer χ source b i y
  have hj := KPContActualCutoffSmoothDescent.smooth_parameter_jet_on_ball B _
    KPContinuation.spectralDomain_isOpen _ hh k s hsΩ
  have hd := (hj.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).comp y
    (realCoordinates_inverse_smooth F).contDiffAt
  apply hd.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro z
  dsimp only [Function.comp_def]
  rw [iteratedDerivWithin_of_isOpen (show IsOpen V from KPChamberL2Defect.chamber_isOpen) hs,
    iteratedDerivWithin_of_isOpen KPContinuation.spectralDomain_isOpen hsΩ]
  congr 1
  funext w
  rw [source_coefficient_formula, Homeomorph.apply_symm_apply]

theorem smooth (k : ℕ) (s : ℂ) :
    KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ (level F ζ hζ C R P H U) R P H
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) ∧
    KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ (level F ζ hζ C R P H U) R P H
      (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s) := by
  by_cases hs : s ∈ V
  · have hE := KPContActualChamberCasimirJets.lineJet_smooth F ζ hζ C R P H U ι f hι hf k s hs
    have hC := source_component_jet_smooth F ζ hζ C R P H U ι f buffer χ source false k s hs
    have hK := source_component_jet_smooth F ζ hζ C R P H U ι f buffer χ source true k s hs
    constructor
    · intro i
      have he : (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s i).val =
          fun y => (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf k s i).val y -
            iteratedDerivWithin k (fun z => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
              (source.descent.cutoff z)
              (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
                (level F ζ hζ C R P H U)) (y, (H.atlas (level F ζ hζ C R P H U)).representative i))) V s := by
        funext y
        unfold lineG KPContActualChamberCasimirJets.lineJet
        rw [KPContSectorScalarLineAlgebra.S_apply, KPContSectorScalarLineAlgebra.S_apply]
        simp only [coveredG, KPContActualChamberCasimirJets.coveredJet, dif_pos hs]
        unfold g KPContActualChamberCasimirJets.jet
        have hh := (source_component_holo F ζ hζ C R P H U ι f buffer χ source false i y)
        have hVΩ : V ⊆ KPContinuation.spectralDomain := by
          intro z hz
          change -(1 : ℝ)/6 < z.re
          change (1 : ℝ)/3 < z.re at hz
          linarith
        exact iteratedDerivWithin_sub hs KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
          ((E_holo F ζ hζ U ι f hι hf _).contDiffOn KPChamberL2Defect.chamber_isOpen s hs)
          ((hh.mono hVΩ).contDiffOn KPChamberL2Defect.chamber_isOpen s hs)
      rw [he]
      exact (hE i).sub (hC i)
    · intro i
      have he : (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s i).val =
          fun y => iteratedDerivWithin k (fun z => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
            (source.descent.commutator z)
            (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
              (level F ζ hζ C R P H U)) (y, (H.atlas (level F ζ hζ C R P H U)).representative i))) V s := by
        funext y
        unfold lineH
        rw [KPContSectorScalarLineAlgebra.S_apply]
        simp only [coveredH, dif_pos hs, h]
      rw [he]
      exact hK i
  · simp only [lineG, lineH, coveredG, coveredH, dif_neg hs, map_zero]
    exact ⟨(KPContSectorSmoothFramesSupport.smoothSections F ζ hζ (level F ζ hζ C R P H U) R P H).zero_mem,
      (KPContSectorSmoothFramesSupport.smoothSections F ζ hζ (level F ζ hζ C R P H U) R P H).zero_mem⟩

private theorem source_scalar_component (w : SmoothSections F ζ hζ C R P H U)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (y : KPFiniteCuspAtlas.SymmetricSpace F) :
    KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U w
      (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
        (level F ζ hζ C R P H U)) (y, (H.atlas (level F ζ hζ C R P H U)).representative i)) =
      (w.val i).val y := by
  have he := congrArg (fun v => (v i).val y)
    (congrArg Subtype.val ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
      (level F ζ hζ C R P H U) R P H).apply_symm_apply w))
  rw [KPContSectorSmoothFramesSupport.smoothS_apply,
    KPContSectorScalarLineAlgebra.S_apply] at he
  exact he

theorem lineG_eq_series_sub_source (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf k s -
      KPContActualCompactSectionL2Jets.pointwiseJets
        (fun z => (source.descent.cutoff z).val) V k s := by
  funext i
  apply Subtype.ext
  funext y
  simp only [Pi.sub_apply, Submodule.coe_sub, Pi.sub_apply]
  unfold lineG KPContActualChamberCasimirJets.lineJet
  rw [KPContSectorScalarLineAlgebra.S_apply, KPContSectorScalarLineAlgebra.S_apply]
  simp only [coveredG, KPContActualChamberCasimirJets.coveredJet, dif_pos hs,
    KPContActualCompactSectionL2Jets.pointwiseJets_apply]
  unfold g KPContActualChamberCasimirJets.jet
  have hVΩ : V ⊆ KPContinuation.spectralDomain := by
    intro z hz
    change -(1 : ℝ)/6 < z.re
    change (1 : ℝ)/3 < z.re at hz
    linarith
  have hC := ((source_component_holo F ζ hζ C R P H U ι f buffer χ source false i y).mono hVΩ).contDiffOn (n := k)
      KPChamberL2Defect.chamber_isOpen s hs
  simp only [Bool.false_eq_true, ↓reduceIte] at hC
  refine (iteratedDerivWithin_sub hs KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
    ((E_holo F ζ hζ U ι f hι hf
      (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
        (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
          (level F ζ hζ C R P H U)) (y, (H.atlas (level F ζ hζ C R P H U)).representative i)))).contDiffOn
        KPChamberL2Defect.chamber_isOpen s hs) hC).trans ?_
  congr 1
  congr 1
  funext z
  exact source_scalar_component F ζ hζ C R P H U (source.descent.cutoff z) i y

theorem lineH_eq_source_jet (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      KPContActualCompactSectionL2Jets.pointwiseJets
        (fun z => (source.descent.commutator z).val) V k s := by
  funext i
  apply Subtype.ext
  funext y
  unfold lineH
  rw [KPContSectorScalarLineAlgebra.S_apply]
  simp only [coveredH, dif_pos hs, h, KPContActualCompactSectionL2Jets.pointwiseJets_apply]
  congr 1
  funext z
  exact source_scalar_component F ζ hζ C R P H U (source.descent.commutator z) i y

def smoothG (k : ℕ) (s : ℂ) : SmoothSections F ζ hζ C R P H U :=
  ⟨_, (smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1⟩

private theorem actualE_component_jet_joint (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (k : ℕ)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount) :
    ContinuousOn (fun p : ℂ × KPFiniteCuspAtlas.SymmetricSpace F =>
      KPContActualChamberNormalSeries.mixedJet F ζ hζ
        (KPContActualChamberNormalSeries.E F ζ hζ U ι f) k [] p.1
        (KPContActualChamberNormalSeries.componentRepresentative F ζ hζ C R P H U i p.2))
      (V ×ˢ Set.univ) := by
  apply (KPChamberL2Defect.chamber_isOpen.prod isOpen_univ).continuousOn_iff.mpr
  intro p hp
  obtain ⟨K,hK,hxK⟩ := exists_compact_mem_nhds p.2
  let rep := KPContActualChamberNormalSeries.componentRepresentative F ζ hζ C R P H U i
  have hr : Continuous rep :=
    ((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
      (KPContSectorArchSphericalFibers.section_continuous F ζ hζ)).mul continuous_const
  let A := rep '' K
  have hA : IsCompact A := hK.image hr
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hc := (KPContActualChamberNormalSeries.compactMixedJet_holomorphic
    F ζ hζ U ι f hι hf k [] A hA).continuousOn
  let j := KPContActualChamberNormalSeries.compactMixedJet F ζ hζ U ι f hι hf k [] A
  have hj : ContinuousOn (fun q : ℂ × A => j q.1 q.2) (V ×ˢ Set.univ) :=
    continuous_eval.comp_continuousOn ((hc.comp continuous_fst.continuousOn
      (fun _ h => h.1)).prodMk continuous_snd.continuousOn)
  have hcont : ContinuousOn (fun q : ℂ × KPFiniteCuspAtlas.SymmetricSpace F =>
      KPContActualChamberNormalSeries.mixedJet F ζ hζ
        (KPContActualChamberNormalSeries.E F ζ hζ U ι f) k [] q.1 (rep q.2)) (V ×ˢ K) := by
    apply continuousOn_iff_continuous_restrict.mpr
    let a : (V ×ˢ K) → ℂ × A := fun q => (q.val.1, ⟨rep q.val.2, ⟨q.val.2,q.property.2,rfl⟩⟩)
    have ha : Continuous a := (continuous_fst.comp continuous_subtype_val).prodMk
      ((hr.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
    apply (hj.comp_continuous ha (fun q => ⟨q.property.1,Set.mem_univ _⟩)).congr
    intro q
    simp [j,a,KPContActualChamberNormalSeries.compactMixedJet,q.property.1]
  exact hcont.continuousAt (mem_nhds_prod_iff.mpr
    ⟨_,KPChamberL2Defect.chamber_isOpen.mem_nhds hp.1,_,hxK,Set.Subset.refl _⟩)

private theorem lineGH_component_jet_joint (k : ℕ)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount) :
    ContinuousOn (fun p : ℂ × KPFiniteCuspAtlas.SymmetricSpace F =>
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k p.1 i).val p.2) (V ×ˢ Set.univ) ∧
    ContinuousOn (fun p : ℂ × KPFiniteCuspAtlas.SymmetricSpace F =>
      (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k p.1 i).val p.2) (V ×ˢ Set.univ) := by
  constructor
  · apply ((actualE_component_jet_joint F ζ hζ C R P H U ι f hι hf k i).sub
      (source_component_jet_joint F ζ hζ C R P H U ι f buffer χ source false k i)).congr
    intro p hp
    have hg := congrArg (fun v => (v i).val p.2)
      (lineG_eq_series_sub_source F ζ hζ C R P H U ι f buffer χ source hι hf k p.1 hp.1)
    dsimp only
    rw [hg]
    simp only [Pi.sub_apply, Submodule.coe_sub, Pi.sub_apply,
      KPContActualCompactSectionL2Jets.pointwiseJets_apply]
    congr 1
    · unfold KPContActualChamberCasimirJets.lineJet
      rw [KPContSectorScalarLineAlgebra.S_apply]
      rw [← KPContActualChamberNormalSeries.mixedJet_commute F ζ hζ U ι f hι hf k [] p.1 hp.1]
      change _ = KPContActualChamberCasimirJets.jet F ζ hζ U ι f k p.1
        (KPContActualChamberNormalSeries.componentRepresentative F ζ hζ C R P H U i p.2)
      rw [← KPContActualChamberCasimirJets.coveredJet_projection F ζ hζ C R P H U ι f hι hf k p.1 hp.1]
      unfold KPContActualChamberNormalSeries.componentRepresentative
      rw [KPContSectorQuotientRelationsComparison.piTilde_quotientMap,
        KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection]
    · congr 1
      funext z
      unfold KPContActualCutoffSmoothDescent.scalar
      rw [← KPContSectorScalarLineAlgebra.S_apply]
      have he := LinearEquiv.apply_symm_apply
        (KPContSectorSmoothFramesSupport.smoothS F ζ hζ (level F ζ hζ C R P H U) R P H)
        (source.descent.cutoff z)
      simpa only [Bool.false_eq_true, ite_false, KPContSectorSmoothFramesSupport.smoothS_apply] using
        (congrArg (fun v => (v.val i).val p.2) he).symm
  · apply (source_component_jet_joint F ζ hζ C R P H U ι f buffer χ source true k i).congr
    intro p hp
    dsimp only
    rw [lineH_eq_source_jet F ζ hζ C R P H U ι f buffer χ source hι hf k p.1 hp.1]
    simp only [KPContActualCompactSectionL2Jets.pointwiseJets_apply]
    congr 1
    funext z
    unfold KPContActualCutoffSmoothDescent.scalar
    rw [← KPContSectorScalarLineAlgebra.S_apply]
    have he := LinearEquiv.apply_symm_apply
      (KPContSectorSmoothFramesSupport.smoothS F ζ hζ (level F ζ hζ C R P H U) R P H)
      (source.descent.commutator z)
    simpa only [ite_true, KPContSectorSmoothFramesSupport.smoothS_apply] using
      (congrArg (fun v => (v.val i).val p.2) he).symm

private theorem incoming_cutoff_chart_holomorphic
    (a : KPContActualSectorSmoothTestModules.ActualChart
      (U := level F ζ hζ C R P H U) (H := H)) :
    KPContActualCompactSectionL2Jets.ChartHolomorphicOn a
      (fun t => (source.descent.cutoff t).val) V := by
  let ψ : KPContCotangentActualOverlap.M F → KPContLocalNorm.Space (KPCuspLogShape.dimension F * 3) :=
    fun x => WithLp.toLp 2 (fun k =>
      x (finProdFinEquiv.symm k |>.1 |> (KPContCotangentActualOverlap.placeEquiv F ζ hζ).symm,
        (finProdFinEquiv.symm k).2))
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    apply PiLp.contDiff_toLp.comp
    apply contDiff_pi.mpr
    intro k
    exact (EuclideanSpace.proj (𝕜 := ℝ)
      ((KPContCotangentActualOverlap.placeEquiv F ζ hζ).symm (finProdFinEquiv.symm k).1,
        (finProdFinEquiv.symm k).2)).contDiff
  have hcoords : ∀ x, KPContActualChartRestrictionDensity.coordinates F (ψ x) =
      KPContCotangentActualOverlap.labeledA (KPContCotangentActualOverlap.placeEquiv F ζ hζ) x := by
    intro x
    have hp : ∀ i j, (finProdFinEquiv.symm (finProdFinEquiv (i,j)) :
        Fin (KPCuspLogShape.dimension F) × Fin 3) = (i,j) := fun _ _ => Equiv.symm_apply_apply _ _
    funext i
    apply Prod.ext
    · apply Complex.ext <;> change x ((KPContCotangentActualOverlap.placeEquiv F ζ hζ).symm
        (finProdFinEquiv.symm (finProdFinEquiv (i,_))).1,
        (finProdFinEquiv.symm (finProdFinEquiv (i,_))).2) = _
      all_goals rw [hp]; simp [KPContCotangentActualOverlap.labeledA, CotangentLogCoframe.A]
    · change x ((KPContCotangentActualOverlap.placeEquiv F ζ hζ).symm
        (finProdFinEquiv.symm (finProdFinEquiv (i,2))).1,
        (finProdFinEquiv.symm (finProdFinEquiv (i,2))).2) = _
      rw [hp]
      rfl
  let g := fun t => KPContActualAllCuspSource.chartCoefficient F ζ hζ C R P H U
    (source.descent.cutoff t) a.component
    (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ (level F ζ hζ C R P H U) 1)
  have hvalue : ∀ t x,
      g t (ψ x) = (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient
        (source.descent.cutoff t).val x := by
    intro t x
    unfold g KPContActualAllCuspSource.chartCoefficient
    rw [KPContActualChartRestrictionDensity.frameCoefficient_class]
    simp only [map_one, Circle.coe_one, one_mul]
    rw [show KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H
      (((KPContSectorSmoothFramesSupport.smoothS F ζ hζ (level F ζ hζ C R P H U) R P H).symm
        (source.descent.cutoff t)).val) = (source.descent.cutoff t).val from
        congrArg Subtype.val ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
          (level F ζ hζ C R P H U) R P H).apply_symm_apply _)]
    rw [hcoords]
    simp only [KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
      KPContCotangentActualOverlap.LiftedChart.coefficient,
      KPContCotangentActualOverlap.ChartKind.representative, map_one, Units.val_one, one_mul, one_smul]
  intro K hK hKω n v
  apply KPContActualChamberCasimirJets.normalSeries_compact_family_of_local V
    KPChamberL2Defect.chamber_isOpen (KPContCotangentOverlapRationalBranches.omega a)
    (fun t x => iteratedFDerivWithin ℝ n
      ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient
        (source.descent.cutoff t).val) (KPContCotangentOverlapRationalBranches.omega a) x v)
    ?_ K hK hKω
  intro x hx
  have hd : IsOpen (KPContActualChartRestrictionDensity.chartDomain F ζ hζ
      (level F ζ hζ C R P H U) R P H a.component a.center a.larger) :=
    a.larger.isOpen.preimage (KPContActualChartRestrictionDensity.coordinates F).continuous
  have hxD : ψ x ∈ KPContActualChartRestrictionDensity.chartDomain F ζ hζ
      (level F ζ hζ C R P H U) R P H a.component a.center a.larger := by
    change KPContActualChartRestrictionDensity.coordinates F (ψ x) ∈ a.larger.neighborhood
    rw [hcoords]
    exact a.closure_subset (subset_closure hx)
  obtain ⟨r,hr,hrD⟩ := Metric.mem_nhds_iff.mp (hd.mem_nhds hxD)
  let B : KPContLocalNorm.LocalBall (KPCuspLogShape.dimension F * 3) :=
    ⟨by simpa [KPCuspLogShape.dimension] using
      mul_pos (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.2 (by norm_num : (0:ℕ)<3),
      ψ x, r/2, by positivity⟩
  have hBD : KPContLocalCubeEmbedding.closedCarrier B ⊆
      KPContActualChartRestrictionDensity.chartDomain F ζ hζ
      (level F ζ hζ C R P H U) R P H a.component a.center a.larger :=
    (Metric.closedBall_subset_ball (by dsimp [B]; linarith)).trans hrD
  have hVs : V ⊆ KPContinuation.spectralDomain := by
    intro t ht
    change -(1:ℝ)/6 < t.re
    change (1:ℝ)/3 < t.re at ht
    linarith
  have hg : KPCutoffSource.ChartSmoothHolomorphicOn B g V := by
    have hh := (source.local_holomorphy a.component a.center a.larger
      (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ (level F ζ hζ C R P H U) 1) B hBD).1
    exact ⟨fun t hz => hh.1 t (hVs hz),
      fun C hC hCB m => by
        obtain ⟨j,hj,hjval⟩ := hh.2 C hC hCB m
        exact ⟨j,hj.mono hVs,
          fun t hz => hjval t (hVs hz)⟩⟩
  let D := ψ ⁻¹' B.carrier
  have hD : IsOpen D := Metric.isOpen_ball.preimage hψ.continuous
  have hxD' : x ∈ D := Metric.mem_ball_self B.radius_pos
  have hω : IsOpen (KPContCotangentOverlapRationalBranches.omega a) := by
    apply a.domain_open.preimage
    apply continuous_pi
    intro i
    exact (continuous_apply _).comp (CotangentLogCoframe.A (KPContCotangentActualOverlap.d F)).continuous
  obtain ⟨C,hC,hxC,hCD⟩ := exists_compact_subset (hD.inter hω) ⟨hxD',hx⟩
  refine ⟨C,hC,hxC,fun y hy => (hCD hy).2,?_⟩
  obtain ⟨j,hj,hjval⟩ := KPContThreeL2GradientCompactHelpers.compact_coordinate_jets_transport B V g hg D hD ψ hψ.contDiffOn
    (fun y hy => hy) C hC (fun y hy => (hCD hy).1) n v
  refine ⟨j,hj,?_⟩
  intro t hz y
  rw [hjval t hz y]
  have he : (g t ∘ ψ) = (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient
      (source.descent.cutoff t).val := funext (fun x => hvalue t x)
  rw [he, iteratedFDerivWithin_of_isOpen n hD ((hCD y.property).1),
    iteratedFDerivWithin_of_isOpen n hω ((hCD y.property).2)]

open _root_.DedekindZetaZeroFree.KPContActualChamberCasimirJets.ChartCalculus renaming parameter_word_commute → KPContActualChamberCasimirJets.ChartCalculus.parameter_word_commute
open _root_.DedekindZetaZeroFree.KPContActualChamberCasimirJets.ChartCalculus renaming joint_of_compact_family → KPContActualChamberCasimirJets.ChartCalculus.joint_of_compact_family
open _root_.DedekindZetaZeroFree.KPContActualChamberCasimirJets.ChartCalculus renaming point_of_compact_family → KPContActualChamberCasimirJets.ChartCalculus.point_of_compact_family
open _root_.DedekindZetaZeroFree.KPContActualChamberCasimirJets renaming jet_constant_word → KPContActualChamberCasimirJets.jet_constant_word

private theorem chart_holomorphic_parameter_jets
    (a : KPContActualSectorSmoothTestModules.ActualChart
      (U := level F ζ hζ C R P H U) (H := H))
    (w : ℂ → Sections F ζ hζ C R P H U)
    (hw : ∀ s ∈ V, KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ
      (level F ζ hζ C R P H U) R P H (w s))
    (hh : KPContActualCompactSectionL2Jets.ChartHolomorphicOn a w V) (k : ℕ) :
    KPContActualCompactSectionL2Jets.ChartHolomorphicOn a
      (KPContActualCompactSectionL2Jets.pointwiseJets w V k) V := by
  let D := KPContCotangentOverlapRationalBranches.omega a
  let h := fun s => (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient (w s)
  have hD : IsOpen D := KPContThreeL2CotangentHelpers.isOpen_omega a
  have hs : ∀ s ∈ V, ContDiffOn ℝ (⊤ : ℕ∞) (h s) D := by
    intro s hz
    obtain ⟨u,hu,he⟩ := KPContThreeL2CotangentHelpers.section_smooth (w s) (hw s hz) a
    apply hu.congr
    intro x hx
    exact (he ⟨x,hx⟩).symm
  let b := Module.finBasis ℝ (KPContCotangentActualOverlap.M F)
  let fields := fun i (_ : KPContCotangentActualOverlap.M F) => b i
  have hb : ∀ l K (hK : IsCompact K), K ⊆ D →
      letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
      ∃ j : ℂ → C(K,ℂ), DifferentiableOn ℂ j V ∧ ∀ s ∈ V, ∀ x : K,
      j s x = RightFrame.PullbackWords.directionalWord fields l (h s) x.val := by
    intro l K hK hKD
    obtain ⟨j,hj,he⟩ := hh K hK hKD (l.map b).length (l.map b).get
    refine ⟨j,hj,?_⟩
    intro s hz x
    rw [he s hz x, KPContActualChamberCasimirJets.jet_constant_word _ _ D hD (hs s hz) _ (hKD x.property)]
    simp only [List.ofFn_get]
    have eq : RightFrame.PullbackWords.directionalWord fields l (h s) =
        RightFrame.PullbackWords.constantDirectionWord (l.map b) (h s) := by
      clear he
      induction l with
      | nil => rfl
      | cons i l ih =>
          change (fun x => fderiv ℝ (RightFrame.PullbackWords.directionalWord fields l (h s)) x (b i)) =
            (fun x => fderiv ℝ (RightFrame.PullbackWords.constantDirectionWord (l.map b) (h s)) x (b i))
          exact congrArg (fun v => fun x => fderiv ℝ v x (b i)) ih
    rw [eq]
  have hj := fun l K hK hKD => KPContActualChamberCasimirJets.ChartCalculus.joint_of_compact_family
    V D (fun s x => RightFrame.PullbackWords.directionalWord fields l (h s) x)
    (hb l) K hK hKD
  have hholo := fun l x hx => KPContActualChamberCasimirJets.ChartCalculus.point_of_compact_family
    V D (fun s x => RightFrame.PullbackWords.directionalWord fields l (h s) x) (hb l) x hx
  have commute := KPContActualChamberCasimirJets.ChartCalculus.parameter_word_commute
    D hD fields (fun _ => contDiffOn_const) (fun _ _ => ⟨b,fun _ => rfl⟩)
    V KPChamberL2Defect.chamber_isOpen h hs hj hholo
  intro K hK hKD n v
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨j,hj,he⟩ := hh K hK hKD n v
  have hcd := hj.contDiffOn KPChamberL2Defect.chamber_isOpen (n := (⊤ : ℕ∞ω))
  have hd := hcd.differentiableOn_iteratedDerivWithin (m := k) (by simp)
    KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
  refine ⟨iteratedDerivWithin k j V, hd, ?_⟩
  intro s hz x
  let u := fun t y => (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient
    (KPContActualCompactSectionL2Jets.pointwiseJets w V k t) y
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (u s) D := by
    have ht := KPContActualCompactSectionL2Jets.scalar_parameter_jet_smooth D hD V
      KPChamberL2Defect.chamber_isOpen h hs hh k s hz
    apply ht.congr
    intro x hx
    exact KPContActualCompactSectionL2Jets.pointwiseJets_frame w V k s a x
  rw [KPContActualChamberCasimirJets.jet_constant_word n _ D hD hu _ (hKD x.property)]
  obtain ⟨N,c,r,hc,_,hr⟩ := RightFrame.PullbackWords.transport D D hD hD fields
    (fun _ => contDiffOn_const) (fun _ _ => ⟨b,fun _ => rfl⟩)
    id contDiffOn_id (fun _ hx => hx) (List.ofFn v)
  change _ = RightFrame.PullbackWords.constantDirectionWord (List.ofFn v) (u s ∘ id) x.val
  rw [hr _ hu _ (hKD x.property)]
  have ueq : u s = fun y => iteratedDerivWithin k (fun z => h z y) V s :=
    funext (fun y => KPContActualCompactSectionL2Jets.pointwiseJets_frame w V k s a y)
  rw [ueq]
  change _ = ∑ i, c i x.val • RightFrame.PullbackWords.directionalWord fields (r i)
    (fun y => iteratedDerivWithin k (fun z => h z y) V s) x.val
  simp_rw [commute k s hz _ x.val (hKD x.property)]
  let ev : C(K,ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ x
  have heq : Set.EqOn (fun z => ev (j z))
      (fun z => ∑ i : Fin N, c i x.val • RightFrame.PullbackWords.directionalWord fields (r i) (h z) x.val) V := by
    intro z hz
    change (j z) x = _
    rw [he z hz x,KPContActualChamberCasimirJets.jet_constant_word n _ D hD (hs z hz) _ (hKD x.property)]
    exact hr _ (hs z hz) _ (hKD x.property)
  change ev (iteratedDerivWithin k j V s) = _
  rw [← KPContThreeL2CompactBoundHelpers.clm_jet V KPChamberL2Defect.chamber_isOpen j hj k s hz ev,
    iteratedDerivWithin_congr heq hz]
  rw [iteratedDerivWithin_fun_sum hz KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
    (fun i _ => (((hholo (r i) x.val (hKD x.property)).contDiffOn
      KPChamberL2Defect.chamber_isOpen (n := (k : ℕ∞ω))).const_smul (c i x.val)).contDiffWithinAt hz)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.real_smul,iteratedDerivWithin_const_mul_field]

private theorem defect_chart_holomorphic (k : ℕ)
    (a : KPContActualSectorSmoothTestModules.ActualChart
      (U := level F ζ hζ C R P H U) (H := H)) :
    KPContActualCompactSectionL2Jets.ChartHolomorphicOn a
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k) V := by
  have hE := KPContActualChamberCasimirJets.actual_normal_series_chart_holomorphic
    F ζ hζ C R P H U ι f hι hf k a
  have hC := chart_holomorphic_parameter_jets F ζ hζ C R P H U a
    (fun z => (source.descent.cutoff z).val) (fun z _ => (source.descent.cutoff z).property)
    (incoming_cutoff_chart_holomorphic F ζ hζ C R P H U ι f buffer χ source a) k
  intro K hK hKD n v
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨j,hj,he⟩ := hE K hK hKD n v
  obtain ⟨q,hq,hqv⟩ := hC K hK hKD n v
  refine ⟨j-q,hj.sub hq,?_⟩
  intro s hs x
  change j s x - q s x = _
  rw [he s hs x,hqv s hs x]
  rw [lineG_eq_series_sub_source F ζ hζ C R P H U ι f buffer χ source hι hf k s hs]
  have hc : ∀ u w : Sections F ζ hζ C R P H U,
      (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient (u-w) =
      (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient u -
      (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient w := by
    intro u w
    funext y
    simp [KPContCotangentActualOverlap.LiftedChart.coefficient,mul_sub]
  rw [hc,iteratedFDerivWithin_sub_apply]
  · rfl
  · have ht := KPContThreeL2CotangentHelpers.section_smooth _
      (KPContActualChamberCasimirJets.lineJet_smooth F ζ hζ C R P H U ι f hι hf k s hs) a
    obtain ⟨u,hu,heq⟩ := ht
    exact ((hu.congr (fun y hy => (heq ⟨y,hy⟩).symm)).contDiffWithinAt (hKD x.property)).of_le (by simp)
  · have ht : KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ
        (level F ζ hζ C R P H U) R P H
        (KPContActualCompactSectionL2Jets.pointwiseJets (fun z => (source.descent.cutoff z).val) V k s) := by
      intro i
      have heq := congrArg (fun u => (u i).val)
        (lineG_eq_series_sub_source F ζ hζ C R P H U ι f buffer χ source hι hf k s hs)
      have hh := (KPContActualChamberCasimirJets.lineJet_smooth F ζ hζ C R P H U ι f hι hf k s hs i).sub
        ((smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1 i)
      convert hh using 1
      funext y
      have hh := congrFun heq y
      simp only [Pi.sub_apply,Submodule.coe_sub,Pi.sub_apply] at hh ⊢
      linear_combination hh
    obtain ⟨u,hu,heq⟩ := KPContThreeL2CotangentHelpers.section_smooth _ ht a
    exact ((hu.congr (fun y hy => (heq ⟨y,hy⟩).symm)).contDiffWithinAt (hKD x.property)).of_le (by simp)
  · exact (KPContThreeL2CotangentHelpers.isOpen_omega a).uniqueDiffOn
  · exact hKD x.property

open _root_.DedekindZetaZeroFree.KPContActualCompactSectionL2Jets renaming finite_compact_lifts → KPContActualCompactSectionL2Jets.finite_compact_lifts

private theorem component_compact_lifts (K : Set (Base F ζ hζ C R P H U)) (hK : IsCompact K) :
    ∃ Z : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount →
      Set (KPFiniteCuspAtlas.SymmetricSpace F), (∀ i, IsCompact (Z i)) ∧
      K ⊆ ⋃ i, (fun y => (H.atlas (level F ζ hζ C R P H U)).components ⟨i,Quotient.mk _ y⟩) '' Z i := by
  suffices h : ∃ Z : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount →
      Set (KPFiniteCuspAtlas.SymmetricSpace F), (∀ i, IsCompact (Z i)) ∧
      (∀ i, Z i ⊆ Set.univ) ∧
      K ⊆ ⋃ i, (fun y => (H.atlas (level F ζ hζ C R P H U)).components ⟨i,Quotient.mk _ y⟩) '' Z i by
    obtain ⟨Z,hZ,_,hcov⟩ := h
    exact ⟨Z,hZ,hcov⟩
  apply KPContActualCompactSectionL2Jets.finite_compact_lifts K hK _ (fun _ => Set.univ)
    (fun i y => (H.atlas (level F ζ hζ C R P H U)).components ⟨i,Quotient.mk _ y⟩)
    (fun _ => isOpen_univ)
  · intro i
    letI : ContinuousConstSMul (KPContSectorPhaseComponentCharts.Component F ζ hζ
        (level F ζ hζ C R P H U) R P H i) (KPFiniteCuspAtlas.SymmetricSpace F) :=
      ⟨fun γ => KPCuspSiegel.continuous_action F γ.val⟩
    exact (H.atlas (level F ζ hζ C R P H U)).components.isOpenMap.comp
      (isOpenMap_sigmaMk.comp isOpenMap_quotient_mk'_mul)
  · intro x hx
    obtain ⟨⟨i,y⟩,rfl⟩ := (H.atlas (level F ζ hζ C R P H U)).components.surjective x
    refine Quotient.inductionOn y ?_
    intro z
    exact Set.mem_iUnion.mpr ⟨i,z,Set.mem_univ _,rfl⟩

private theorem lineGH_compact_norm_bound (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V)
    (K : Set (Base F ζ hζ C R P H U)) (hK : IsCompact K) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L, ∀ x ∈ K,
      KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ
        (level F ζ hζ C R P H U) R P H
        (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x ≤ B ∧
      KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ
        (level F ζ hζ C R P H U) R P H
        (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s) x ≤ B := by
  obtain ⟨Z,hZ,hcov⟩ := component_compact_lifts F ζ hζ C R P H U K hK
  have hb : ∀ i, ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L, ∀ y ∈ Z i,
      ‖(lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s i).val y‖ ≤ B ∧
      ‖(lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s i).val y‖ ≤ B := by
    intro i
    have hj := lineGH_component_jet_joint F ζ hζ C R P H U ι f buffer χ source hι hf k i
    obtain ⟨b,hb⟩ := (hL.prod (hZ i)).exists_bound_of_continuousOn
      (hj.1.mono (Set.prod_mono hLV (Set.subset_univ _)))
    obtain ⟨c,hc⟩ := (hL.prod (hZ i)).exists_bound_of_continuousOn
      (hj.2.mono (Set.prod_mono hLV (Set.subset_univ _)))
    exact ⟨max 0 (max b c), le_max_left _ _,fun s hs y hy =>
      ⟨(hb (s,y) ⟨hs,hy⟩).trans ((le_max_left _ _).trans (le_max_right _ _)),
       (hc (s,y) ⟨hs,hy⟩).trans ((le_max_right _ _).trans (le_max_right _ _))⟩⟩
  choose b hb hbound using hb
  refine ⟨∑ i, b i, Finset.sum_nonneg (fun i _ => hb i), ?_⟩
  intro s hs x hx
  obtain ⟨i,y,hy,rfl⟩ := Set.mem_iUnion.mp (hcov hx)
  rw [KPContSectorSmoothFramesSupport.sectionNorm_component,
    KPContSectorSmoothFramesSupport.sectionNorm_component]
  have hi : b i ≤ ∑ j, b j := Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i)
  exact ⟨(hbound i s hs y hy).1.trans hi,(hbound i s hs y hy).2.trans hi⟩

private theorem lineGH_compact_square_bound (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V)
    (K : Set (Base F ζ hζ C R P H U)) (hK : IsCompact K) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L,
      (∫⁻ x in K, KPContSectorLineL2Isometry.squaredNorm F ζ hζ
        (level F ζ hζ C R P H U) R P H
        (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
        ∂baseMeasure F ζ hζ C R P H U) ≤ ENNReal.ofReal B ∧
      (∫⁻ x in K, KPContSectorLineL2Isometry.squaredNorm F ζ hζ
        (level F ζ hζ C R P H U) R P H
        (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
        ∂baseMeasure F ζ hζ C R P H U) ≤ ENNReal.ofReal B := by
  letI := KPContSectorFixedMeasureLocalFiniteness.sphericalMeasure_finiteOnCompacts
    F ζ hζ R P (level F ζ hζ C R P H U)
  obtain ⟨B,hB,hbound⟩ := lineGH_compact_norm_bound F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV K hK k
  let D := ENNReal.ofReal (B^2) * baseMeasure F ζ hζ C R P H U K
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK.measure_lt_top.ne
  refine ⟨D.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro s hs
  rw [ENNReal.ofReal_toReal hD]
  have hi : ∀ u : Sections F ζ hζ C R P H U,
      (∀ x ∈ K, KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ
        (level F ζ hζ C R P H U) R P H u x ≤ B) →
      (∫⁻ x in K, KPContSectorLineL2Isometry.squaredNorm F ζ hζ
        (level F ζ hζ C R P H U) R P H u x ∂baseMeasure F ζ hζ C R P H U) ≤ D := by
    intro u hu
    calc
      _ ≤ ∫⁻ _x in K, ENNReal.ofReal (B^2) ∂baseMeasure F ζ hζ C R P H U := by
        apply setLIntegral_mono' hK.measurableSet
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        apply pow_le_pow_left₀ _ (hu x hx)
        obtain ⟨⟨i,y⟩,rfl⟩ := (H.atlas (level F ζ hζ C R P H U)).components.surjective x
        refine Quotient.inductionOn y ?_
        intro y
        rw [KPContSectorSmoothFramesSupport.sectionNorm_component]
        exact norm_nonneg _
      _ = D := by simp [D]
  exact ⟨hi _ (fun x hx => (hbound s hs x hx).1), hi _ (fun x hx => (hbound s hs x hx).2)⟩

private theorem smooth_coefficient_at
    (w : Sections F ζ hζ C R P H U)
    (hw : KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ (level F ζ hζ C R P H U) R P H w)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (x : KPContActualChamberCasimirJets.M F) (hx : x ∈ a.omega) :
    ContDiffAt ℝ (⊤ : ℕ∞) (a.coefficient w) x := by
  let v : KPArch.Space (KPCuspLogShape.dimension F) → ℂ := fun y => (w i).val (a.kind.representative • y)
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := (hw i).comp
    (CoreChartLocalizers.CutoffConstruction.StabilizerLinearization.rational_action_contDiff F a.kind.representative)
  have ha : ContDiff ℝ (⊤ : ℕ∞) (KPContCotangentActualOverlap.labeledA a.places) := by
    exact contDiff_pi.2 (fun j => contDiff_pi.1
      (CotangentLogCoframe.A (KPContActualChamberCasimirJets.d F)).contDiff (a.places.symm j))
  let c : ℂ := KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x)
  have hp : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ)) =ᶠ[𝓝 x] (fun _ => c) := by
    have he := (a.splitting_locallyConstant.comp (fun ε => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ))).eventually_eq (⟨x,hx⟩ : a.omega)
    have hh : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ)) =ᶠ[𝓝[a.omega] x] (fun _ => c) := by
      rw [nhdsWithin_eq_map_subtype_coe hx]; exact he
    rwa [a.isOpen_omega.nhdsWithin_eq hx] at hh
  apply (((contDiff_const (c := c)).mul (hv.comp ha)).contDiffAt).congr_of_eventuallyEq
  filter_upwards [hp] with y hy
  simp only [KPContCotangentActualOverlap.LiftedChart.coefficient, hy]
  rfl

private theorem metric_laplacian_sub {n : ℕ} {u v : HyperbolicChart.Space n → ℂ}
    {x : HyperbolicChart.Space n}
    (hu : ContDiffAt ℝ (⊤ : ℕ∞) u x) (hv : ContDiffAt ℝ (⊤ : ℕ∞) v x) :
    HyperbolicChart.laplacian n (u - v) x =
      HyperbolicChart.laplacian n u x - HyperbolicChart.laplacian n v x := by
  have hfirst (j : Fin n) (l : Fin 3) :
      HyperbolicChart.coordinateDerivative n j l (u - v) =ᶠ[𝓝 x]
        HyperbolicChart.coordinateDerivative n j l u - HyperbolicChart.coordinateDerivative n j l v := by
    filter_upwards [(hu.of_le (m := 1) (by simp)).eventually (by simp), (hv.of_le (m := 1) (by simp)).eventually (by simp)] with y hy hz
    simp only [HyperbolicChart.coordinateDerivative]
    rw [fderiv_sub (hy.differentiableAt (by simp)) (hz.differentiableAt (by simp))]
    rfl
  have hdiff (f : HyperbolicChart.Space n → ℂ) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x)
      (j : Fin n) (l : Fin 3) : DifferentiableAt ℝ (HyperbolicChart.coordinateDerivative n j l f) x := by
    unfold HyperbolicChart.coordinateDerivative
    exact (hf.fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const |>.differentiableAt (by simp)
  have hsecond (j : Fin n) (l : Fin 3) :
      HyperbolicChart.coordinateDerivative n j l (HyperbolicChart.coordinateDerivative n j l (u - v)) x =
        HyperbolicChart.coordinateDerivative n j l (HyperbolicChart.coordinateDerivative n j l u) x -
        HyperbolicChart.coordinateDerivative n j l (HyperbolicChart.coordinateDerivative n j l v) x := by
    change fderiv ℝ (HyperbolicChart.coordinateDerivative n j l (u - v)) x
      (HyperbolicChart.coordinateVector n j l) = _
    rw [(hfirst j l).fderiv_eq, fderiv_sub (hdiff u hu j l) (hdiff v hv j l)]
    rfl
  unfold HyperbolicChart.laplacian
  simp only [hsecond, (hfirst _ _).eq_of_nhds, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem defect_frame_equation (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (a : Frame F ζ hζ C R P H U i) (x : KPContActualChamberCasimirJets.M F) (hx : x ∈ a.omega) :
    HyperbolicChart.laplacian (KPContActualChamberCasimirJets.d F)
      (a.coefficient (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)) x =
    KPContActualChamberCasimirJets.lambda F s *
      a.coefficient (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x -
      a.coefficient (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s) x +
      ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) *
        KPContActualChamberCasimirJets.lambdaJet F j s *
        a.coefficient (lineG F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s) x := by
  let cjet := KPContActualCompactSectionL2Jets.pointwiseJets
    (fun z => (source.descent.cutoff z).val) V
  have hc : KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ
      (level F ζ hζ C R P H U) R P H (cjet k s) := by
    intro j
    have he := congrArg (fun v => (v j).val)
      (lineG_eq_series_sub_source F ζ hζ C R P H U ι f buffer χ source hι hf k s hs)
    have hcj := (KPContActualChamberCasimirJets.lineJet_smooth F ζ hζ C R P H U ι f hι hf k s hs j).sub
      ((smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1 j)
    convert hcj using 1
    funext y
    have hh := congrFun he y
    simp only [Pi.sub_apply, Submodule.coe_sub, Pi.sub_apply] at hh ⊢
    change (cjet k s j).val y =
      (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf k s j).val y -
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s j).val y
    linear_combination hh
  have hVΩ : V ⊆ KPContinuation.spectralDomain := by
    intro z hz
    change -(1 : ℝ)/6 < z.re
    change (1 : ℝ)/3 < z.re at hz
    linarith
  have hsource := (KPContActualAllCuspSourceLaplacianJets.actual_source_laplacian_jets
    F ζ hζ C R P H U ι f buffer χ source V KPChamberL2Defect.chamber_isOpen hVΩ).2 k s hs i a x hx
  have hE := KPContActualChamberCasimirJets.casimir_jets F ζ hζ C R P H U ι f hι hf k s hs a x hx
  simp only [lineG_eq_series_sub_source F ζ hζ C R P H U ι f buffer χ source hι hf _ s hs,
    lineH_eq_source_jet F ζ hζ C R P H U ι f buffer χ source hι hf _ s hs]
  have hcoef : ∀ u v : Sections F ζ hζ C R P H U, a.coefficient (u - v) =
      a.coefficient u - a.coefficient v := by
    intro u v
    funext y
    simp [KPContCotangentActualOverlap.LiftedChart.coefficient, mul_sub]
  rw [hcoef, metric_laplacian_sub
    (smooth_coefficient_at F ζ hζ C R P H U _
      (KPContActualChamberCasimirJets.lineJet_smooth F ζ hζ C R P H U ι f hι hf k s hs) a x hx)
    (smooth_coefficient_at F ζ hζ C R P H U _ hc a x hx)]
  have hE' : HyperbolicChart.laplacian (KPContActualChamberCasimirJets.d F)
      (a.coefficient (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf k s)) x =
      KPContActualChamberCasimirJets.lambda F s *
        a.coefficient (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf k s) x +
      ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) *
        KPContActualChamberCasimirJets.lambdaJet F j s *
        a.coefficient (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf (k-j) s) x := hE
  rw [hE', hsource]
  simp only [hcoef, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  simp only [KPContActualChamberCasimirJets.lambdaJet, KPContActualChamberCasimirJets.V, V]
  simp only [KPContActualChamberCasimirJets.lambda, KPContActualChamberCasimirJets.d]
  ring_nf
  rfl

def lineDelta (k : ℕ) (s : ℂ) : Sections F ζ hζ C R P H U :=
  KPCuspCutoffGraph.localLaplacianSection F ζ hζ H.totallyComplex
    (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U))
    (smoothG F ζ hζ C R P H U ι f buffer χ source hι hf k s)

private theorem threeL2_rational_laplacian (γ : KPCuspArithmetic.PGL2 F)
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

theorem lineDelta_frame (k : ℕ) (s : ℂ)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (a : Frame F ζ hζ C R P H U i) (x : KPContActualChamberCasimirJets.M F) (hx : x ∈ a.omega) :
    a.coefficient (lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s) x =
      HyperbolicChart.laplacian (KPContActualChamberCasimirJets.d F)
        (a.coefficient (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)) x := by
  let w := lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s
  have hw := (smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1 i
  let v : KPArch.Space (KPCuspLogShape.dimension F) → ℂ := fun y => (w i).val (a.kind.representative • y)
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := hw.comp
    (CoreChartLocalizers.CutoffConstruction.StabilizerLinearization.rational_action_contDiff F a.kind.representative)
  let c : ℂ := KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x)
  have hp : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ)) =ᶠ[𝓝 x] (fun _ => c) := by
    have he := (a.splitting_locallyConstant.comp (fun ε => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ))).eventually_eq (⟨x,hx⟩ : a.omega)
    have hh : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ)) =ᶠ[𝓝[a.omega] x] (fun _ => c) := by
      rw [nhdsWithin_eq_map_subtype_coe hx]; exact he
    rwa [a.isOpen_omega.nhdsWithin_eq hx] at hh
  have hg : a.coefficient w =ᶠ[𝓝 x]
      (fun y => c * v (KPContCotangentActualOverlap.labeledA a.places y)) := by
    filter_upwards [hp] with y hy
    simp only [KPContCotangentActualOverlap.LiftedChart.coefficient, hy]
    rfl
  rw [KPCuspCutoffGraphApproximation.laplacian_congr_nhds _ hg]
  have hb := KPContArchLaplacianCoordinateBridge.bridge_equiv
    (KPContActualChamberCasimirJets.d F) (KPCuspLogShape.dimension F) a.places
    (fun y => c * v y) (contDiff_const.mul hv) x
  change KPContActualSphericalFlatStage.localLaplacian _ (fun y => c * v y)
    (KPContCotangentActualOverlap.labeledA a.places x) =
      HyperbolicChart.laplacian _ (fun y => c * v (KPContCotangentActualOverlap.labeledA a.places y)) x at hb
  rw [← hb, KPContArchLaplacianNaturality.localLaplacian_const_mul _ _ hv,
    threeL2_rational_laplacian F a.kind.representative (w i).val hw]
  change c * KPCuspCutoffGraph.localLaplacianComplex F ζ hζ H.totallyComplex
    (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U)) w i
    (a.kind.representative • KPContCotangentActualOverlap.labeledA a.places x) = _
  congr 1
  exact (KPContArchLaplacianCoordinateBridge.bridge F (w i).val hw
    (a.kind.representative • KPContCotangentActualOverlap.labeledA a.places x)).symm

def gradientFields (k : ℕ) (s : ℂ) :
    KPContActualCotangentMeasurableFamilies.ChartFields F ζ hζ
      (level F ζ hζ C R P H U) R P H :=
  fun a => KPContActualSectorTestDifferentialDescent.chartDifferential a
    (fun x => (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x.val)

theorem gradient_compatible (k : ℕ) (s : ℂ) :
    KPContActualCotangentMeasurableFamilies.IsMeasurableCotangentFamily
      (gradientFields F ζ hζ C R P H U ι f buffer χ source hι hf k s) := by
  exact KPContThreeL2CotangentHelpers.smooth_section_differential
    (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)
    (smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1

def gradient (k : ℕ) (s : ℂ) : GradientFamily F ζ hζ C R P H U :=
  ⟨_, gradient_compatible F ζ hζ C R P H U ι f buffer χ source hι hf k s⟩

theorem lineH_support (k : ℕ) (s : ℂ) :
    tsupport (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ
      (level F ζ hζ C R P H U) R P H
      (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)) ⊆
    KPContActualAllCuspSource.K F ζ hζ C R P H U buffer := by
  by_cases hs : s ∈ V
  · have hsΩ : s ∈ KPContinuation.spectralDomain := by
      change -(1 : ℝ)/6 < s.re
      change (1 : ℝ)/3 < s.re at hs
      linarith
    have he : lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s =
        KPContActualCompactSectionL2Jets.pointwiseJets
          (fun z => (source.descent.commutator z).val) KPContinuation.spectralDomain k s := by
      funext i
      apply Subtype.ext
      funext y
      unfold lineH
      rw [KPContSectorScalarLineAlgebra.S_apply]
      simp only [coveredH, dif_pos hs, h, KPContActualCompactSectionL2Jets.pointwiseJets_apply]
      rw [iteratedDerivWithin_of_isOpen (show IsOpen V from KPChamberL2Defect.chamber_isOpen) hs,
        iteratedDerivWithin_of_isOpen KPContinuation.spectralDomain_isOpen hsΩ]
      congr 1
      funext z
      unfold KPContActualCutoffSmoothDescent.scalar
      rw [← KPContSectorScalarLineAlgebra.S_apply]
      have hS : KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H
          ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ (level F ζ hζ C R P H U) R P H).symm
            (source.descent.commutator z)).val = (source.descent.commutator z).val := by
        rw [← KPContSectorSmoothFramesSupport.smoothS_apply, LinearEquiv.apply_symm_apply]
      rw [hS]
    rw [he]
    exact KPContActualCompactSectionL2Jets.pointwiseJets_support _ _ _
      source.compact_collars.isClosed source.support k s hsΩ
  · simp only [lineH, coveredH, dif_neg hs, map_zero]
    have hz : KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ
        (level F ζ hζ C R P H U) R P H (0 : Sections F ζ hζ C R P H U) = 0 := by
      funext x
      obtain ⟨v, rfl⟩ := KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ
        (level F ζ hζ C R P H U) x
      rw [← map_zero (KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H),
        KPContSectorSmoothFramesSupport.sectionNorm_pullback]
      simp
    rw [hz]
    simp

private theorem source_collars_disjoint_high_end
    (A : ℝ) (hA : T + 1 < A)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U) :
    Disjoint (KPContActualAllCuspSource.K F ζ hζ C R P H U buffer)
      (KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A a) := by
  apply Set.disjoint_left.mpr
  intro x hx hxA
  obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hx
  have hbe : x ∈ KPContActualCollarBuffer.endSet F ζ hζ
      (level F ζ hζ C R P H U) R P H buffer.τ b :=
    interior_subset (buffer.collar_in_chart_interior b hb)
  have hτA : buffer.τ < A := lt_trans buffer.below_cutoff (by linarith)
  rw [← KPContThreeL2EndHelpers.end_lift_range F ζ hζ
    (level F ζ hζ C R P H U) R P H A a] at hxA
  obtain ⟨z,hz,rfl⟩ := hxA
  have hae : KPContActualCollarBuffer.chartLift F ζ hζ
      (level F ζ hζ C R P H U) R P H a z ∈
      KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H buffer.τ a := by
    rw [← buffer.lift_range a]
    exact ⟨z, lt_trans hτA hz, rfl⟩
  have hab : a = b := by
    by_contra hn
    exact (buffer.disjoint_ends hn).notMem_of_mem_left hae hbe
  subst b
  have hc := (buffer.height_continuous a _ hae).mono
    (show {x | x ∈ KPContActualCollarBuffer.endSet F ζ hζ
        (level F ζ hζ C R P H U) R P H buffer.τ a ∧
        KPContActualCollarBuffer.height F ζ hζ
          (level F ζ hζ C R P H U) R P H buffer.τ a x ∈ Set.Icc T (T+1)} ⊆
        KPContActualCollarBuffer.endSet F ζ hζ
          (level F ζ hζ C R P H U) R P H buffer.τ a from fun _ h => h.1)
  have hh := hc.mem_closure hb (show Set.MapsTo
    (KPContActualCollarBuffer.height F ζ hζ
      (level F ζ hζ C R P H U) R P H buffer.τ a)
    {x | x ∈ KPContActualCollarBuffer.endSet F ζ hζ
      (level F ζ hζ C R P H U) R P H buffer.τ a ∧
      KPContActualCollarBuffer.height F ζ hζ
        (level F ζ hζ C R P H U) R P H buffer.τ a x ∈ Set.Icc T (T+1)}
    (Set.Icc T (T+1)) from fun _ h => h.2)
  rw [isClosed_Icc.closure_eq, buffer.height_coordinates a z (lt_trans hτA hz)] at hh
  exact (not_lt_of_ge hh.2) (lt_trans hA hz)

private theorem source_high_tail_zero : ∃ A : ℝ,
    (H.atlas (level F ζ hζ C R P H U)).threshold < A ∧
    ∀ A' : ℝ, A ≤ A' → ∀ k s,
    (∫⁻ x in tail F ζ hζ C R P H U A',
      KPContSectorLineL2Isometry.squaredNorm F ζ hζ
        (level F ζ hζ C R P H U) R P H
        (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
      ∂baseMeasure F ζ hζ C R P H U) = 0 := by
  let A := max ((H.atlas (level F ζ hζ C R P H U)).threshold + 1) (T + 2)
  refine ⟨A, lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro A' hA' k s
  have hTA' : T + 1 < A' := lt_of_lt_of_le
    (lt_of_lt_of_le (by linarith) (le_max_right _ _)) hA'
  have hz : ∀ x ∈ tail F ζ hζ C R P H U A',
      KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ
        (level F ζ hζ C R P H U) R P H
        (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s) x = 0 := by
    intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hi
    have he : x ∈ KPContActualCollarBuffer.endSet F ζ hζ
        (level F ζ hζ C R P H U) R P H A' ⟨i,c⟩ := hc
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have hd := source_collars_disjoint_high_end F ζ hζ C R P H U buffer A' hTA' ⟨i,c⟩
    exact hd.notMem_of_mem_left
      (lineH_support F ζ hζ C R P H U ι f buffer χ source hι hf k s hs) he
  calc
    _ = ∫⁻ _x in tail F ζ hζ C R P H U A', (0 : ℝ≥0∞)
        ∂baseMeasure F ζ hζ C R P H U := by
      apply setLIntegral_congr_fun
      · exact (isOpen_iUnion (fun i => isOpen_iUnion (fun c =>
          KPContThreeL2EndHelpers.all_ends_open F ζ hζ
            (level F ζ hζ C R P H U) R P H A' ⟨i,c⟩))).measurableSet
      · intro x hx
        simp only [KPContSectorLineL2Isometry.squaredNorm, hz x hx, sq, mul_zero,
          ENNReal.ofReal_zero]
    _ = 0 := by simp

private theorem gradient_chart_norm_joint (k : ℕ)
    (a : KPContActualSectorSmoothTestModules.ActualChart
      (U := level F ζ hζ C R P H U) (H := H))
    (K : Set (KPContCotangentActualOverlap.M F)) (hK : IsCompact K)
    (hKD : K ⊆ KPContCotangentOverlapRationalBranches.omega a) :
    ContinuousOn (fun p : ℂ × KPContCotangentActualOverlap.M F =>
      (KPContActualCotangentMeasurableFamilies.normSquare
        (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k p.1)
        (KPContCotangentOverlapRationalBranches.q a p.2) : ℝ)) (V ×ˢ K) := by
  let d := KPContCotangentActualOverlap.d F
  let h := fun s => (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient
    (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)
  have hc : ∀ i j, ContinuousOn (fun p : ℂ × KPContCotangentActualOverlap.M F =>
      HyperbolicChart.coordinateDerivative d i j (h p.1) p.2) (V ×ˢ K) := by
    intro i j
    have hh := defect_chart_holomorphic F ζ hζ C R P H U ι f buffer χ source hι hf k a
    have hj := KPContActualChamberCasimirJets.ChartCalculus.joint_of_compact_family V
      (KPContCotangentOverlapRationalBranches.omega a)
      (fun s x => iteratedFDerivWithin ℝ 1 (h s)
        (KPContCotangentOverlapRationalBranches.omega a) x (fun _ => HyperbolicChart.coordinateVector d i j))
      (fun C hC hCD => hh C hC hCD 1 (fun _ => HyperbolicChart.coordinateVector d i j)) K hK hKD
    apply hj.congr
    intro p hp
    dsimp only
    rw [iteratedFDerivWithin_of_isOpen 1 (KPContThreeL2CotangentHelpers.isOpen_omega a) (hKD hp.2)]
    simp [iteratedFDeriv_one_apply,HyperbolicChart.coordinateDerivative]
  have hd : ∀ i j, ContinuousOn (fun p : ℂ × KPContCotangentActualOverlap.M F =>
      HyperbolicChart.differential d (h p.1) p.2 i j) (V ×ˢ K) := by
    intro i j
    fin_cases j
    · exact hc i 2
    · exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        ((EuclideanSpace.proj (i,2)).continuous.comp continuous_snd))).continuousOn).mul (hc i 0)
    · exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        ((EuclideanSpace.proj (i,2)).continuous.comp continuous_snd))).continuousOn).mul (hc i 1)
  have hj : ContinuousOn (fun p : ℂ × KPContCotangentActualOverlap.M F =>
      ∑ i : Fin d, ∑ j : Fin 3, ‖HyperbolicChart.differential d (h p.1) p.2 i j‖ ^ 2) (V ×ˢ K) :=
    continuousOn_finset_sum _ (fun i _ => continuousOn_finset_sum _
      (fun j _ => (hd i j).norm.pow 2))
  apply hj.congr
  intro p hp
  dsimp only
  rw [KPContActualCotangentMeasurableFamilies.normSquare_chart _ a ⟨p.2,hKD hp.2⟩]
  symm
  change _ = ‖_‖ ^ 2
  rw [PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hgerm : KPContActualSectorTestDifferentialDescent.liftExtension a
      (fun x => h p.1 x.val) =ᶠ[𝓝 p.2] h p.1 := by
    filter_upwards [(KPContThreeL2CotangentHelpers.isOpen_omega a).mem_nhds (hKD hp.2)] with y hy
    simp [KPContActualSectorTestDifferentialDescent.liftExtension,hy]
  change ‖HyperbolicChart.differential d (h p.1) p.2 i j‖ ^ 2 =
    ‖(CotangentLogCoframe.j d (HyperbolicChart.differential d
      (KPContActualSectorTestDifferentialDescent.liftExtension a (fun x => h p.1 x.val)) p.2)) (i,j)‖ ^ 2
  rw [CotangentLogCoframe.j_apply]
  fin_cases j <;> simp [HyperbolicChart.differential,HyperbolicChart.coordinateDerivative,hgerm.fderiv_eq]

theorem lineH_borelL2 (k : ℕ) (s : ℂ) :
    lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈
      BorelL2Sections F ζ hζ C R P H U := by
  have hsm := (smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).2
  have hm : ∀ i, Measurable
      (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s i).val :=
    fun i => (hsm i).continuous.measurable
  refine ⟨hm, ?_⟩
  apply (KPContSectorLineL2Isometry.finite_integral_iff F ζ hζ
    (level F ζ hζ C R P H U) R P H _ hm).mpr
  letI := KPContSectorFixedMeasureLocalFiniteness.coveredMeasure_finiteOnCompacts
    F ζ hζ R (level F ζ hζ C R P H U)
  have hc := (KPContSectorLineL2Isometry.continuous_iff F ζ hζ
    (level F ζ hζ C R P H U) R P H _).mp (fun i => (hsm i).continuous)
  apply hc.memLp_of_hasCompactSupport
  apply (KPContSectorSmoothFramesSupport.hasCompactSupport_iff F ζ hζ
    (level F ζ hζ C R P H U) R P H _).mpr
  rw [show KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H
      (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ (level F ζ hζ C R P H U) R P H
        (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)) =
      lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s from
    (KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H).apply_symm_apply _]
  exact source.compact_collars.of_isClosed_subset isClosed_closure
    (lineH_support F ζ hζ C R P H U ι f buffer χ source hι hf k s)

private theorem scalar_cusp_frame_identity
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (e : KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ (level F ζ hζ C R P H U))
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    (KPContSectorScalarLineAlgebra.J F ζ hζ (level F ζ hζ C R P H U) e).val
      (z, KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U a 1) =
      (KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H e a.1).val
        (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a • z) := by
  let j := KPContSectorScalarLineAlgebra.J F ζ hζ (level F ζ hζ C R P H U) e
  have hr := j.property.1 z
    (KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U a 1)
    (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a)
  have hc : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ
      (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a) *
      KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U a 1 =
      (H.atlas (level F ζ hζ C R P H U)).representative a.1 := by
    simp [KPContFlatCuspIncomingEvaluation.finiteRepresentative,
      KPContFlatCuspIncomingEvaluation.atlas, map_inv]
  rw [hc] at hr
  rw [KPContSectorScalarLineAlgebra.S_apply]
  exact hr.symm

include hι hf in
private theorem E_cusp_scalar (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) :
    KPContActualChamberNormalSeries.E F ζ hζ U ι f s
      (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
        (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a 1 p)) =
    KPContActualChamberNormalSeries.E F ζ hζ U ι f s
      (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a p.2 p.1.1 p.1.2 1) := by
  obtain ⟨e, he, -, -⟩ := KPContActualChamberNormalSeries.descent_series F ζ hζ C R P H U ι f hι hf
  have hleft := he s hs (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
    (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a 1 p))
  rw [KPContActualChamberNormalSeries.coveredRepresentative_projection] at hleft
  rw [← hleft]
  have hv : (e s).val (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a 1 p) =
      (KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H (e s) a.1).val
        (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a • KPCuspCharts.toArch F p) := by
    rw [KPContSectorScalarLineAlgebra.S_apply]
    simp [KPContActualCutoffSmoothDescent.coveredPoint, KPContSectorSmoothFramesSupport.cuspPoint,
      KPContFlatCuspIncomingEvaluation.sigma, KPContFlatCuspIncomingEvaluation.atlas]
  rw [hv, KPContFlatCuspIncomingEvaluation.cuspGroup,
    (KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s hs).1,
    ← he s hs, KPContFlatCuspIncomingEvaluation.localGroup,
    KPContSectorScalarLineAlgebra.group_lift_formula,
    KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection,
    scalar_cusp_frame_identity F ζ hζ C R P H U a (e s)]

include hι hf in

theorem g_cusp_scalar (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) :
    g F ζ hζ C R P H U ι f buffer χ source k s
      (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a 1 p) =
    iteratedDerivWithin k (fun w => KPContActualChamberOutgoingAdapter.correctionSheet
      F ζ hζ C R P H U a ι buffer f χ source w p.2 p.1.1 p.1.2 1) V s := by
  unfold g KPContActualChamberOutgoingAdapter.correctionSheet
  exact iteratedDerivWithin_congr (fun w hw => by rw [E_cusp_scalar F ζ hζ C R P H U ι f hι hf w hw]) hs

theorem sectionNorm_cusp_scalar (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) :
    KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ (level F ζ hζ C R P H U) R P H
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)
      (KPContActualCollarBuffer.chartLift F ζ hζ (level F ζ hζ C R P H U) R P H a p) =
    ‖iteratedDerivWithin k (fun w => KPContActualChamberOutgoingAdapter.correctionSheet
      F ζ hζ C R P H U a ι buffer f χ source w p.2 p.1.1 p.1.2 1) V s‖ := by
  rw [← KPContActualCutoffSmoothDescent.coveredPoint_base F ζ hζ C R P H U a 1 p]
  unfold lineG
  rw [KPContSectorSmoothFramesSupport.sectionNorm_pullback]
  simp only [coveredG, dif_pos hs]
  rw [g_cusp_scalar F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a p]

open KPContActualChamberMeanZeroAdapter in
include hι hf in
private theorem scalar_correction_complement_eq (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (s : ℂ) (hs : s ∈ V) (t : ℝ)
    (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F)
    (ht : buffer.τ < t) :
    correctionMeanZeroSheet F ζ hζ C R P H U a ι f buffer χ source s t x b ε =
      meanZeroJetSheet F ζ hζ C R P H U a ι f 0 s t x b ε := by
  have hsΩ : s ∈ KPContinuation.spectralDomain := by
    change -(1 : ℝ)/6 < s.re
    change (1 : ℝ)/3 < s.re at hs
    linarith
  let W := ((χ a).toFun t : ℂ) •
    (KPContFlatCuspIncomingEvaluation.W F ζ hζ C R P H U a ι s (f s) t b)
  have hcut (y : KPCuspCharts.Horizontal F) (δ : rootsOfUnity 3 F) :
      KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff s)
        (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a δ ((y,b),t)) =
      (KPCuspGenuineMonodromy.chi F ζ hζ δ : ℂ) * W.val 0 := by
    rw [KPContActualCutoffSmoothDescent.scalar_coveredPoint,
      source.descent.cutoff_frame s hsΩ a ((y,b),t) ht]
    simp only [KPContActualCutoffSmoothDescent.incomingValue]
    change (KPCuspGenuineMonodromy.chi F ζ hζ δ : ℂ) * (((χ a).toFun t : ℂ) * _) = _
    rw [(KPContFlatCuspIncomingEvaluation.W F ζ hζ C R P H U a ι s (f s) t b).property.2 (QuotientAddGroup.mk y)]
    change _ = (KPCuspGenuineMonodromy.chi F ζ hζ δ : ℂ) * (((χ a).toFun t : ℂ) * _)
    ring
  have hmode : KPContActualChamberOutgoingAdapter.zeroMode F ζ hζ C R P H U a ι buffer f χ source s t b =
      KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a
        (fiberMeasure F ζ hζ C R P H U a) 0 s t b - W := by
    letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
    letI := KPContinuation.ChamberOutgoingSource.actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U a
    unfold KPContActualChamberOutgoingAdapter.zeroMode
    have he : (fun δ => ∫ q : KernelTorus F ζ hζ C R P H U a,
        KPContActualChamberOutgoingAdapter.correctionSheet F ζ hζ C R P H U a ι buffer f χ source
          s t (Quotient.out q) b δ ∂fiberMeasure F ζ hζ C R P H U a) =
      (fun δ => ∫ q : KernelTorus F ζ hζ C R P H U a,
        KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out q) b δ
          ∂fiberMeasure F ζ hζ C R P H U a) -
      (fun δ => (KPCuspGenuineMonodromy.chi F ζ hζ δ : ℂ) * W.val 0) := by
      funext δ
      unfold KPContActualChamberOutgoingAdapter.correctionSheet
      simp_rw [hcut]
      change (∫ q : KernelTorus F ζ hζ C R P H U a,
        KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out q) b δ -
        (KPCuspGenuineMonodromy.chi F ζ hζ δ : ℂ) * W.val 0 ∂fiberMeasure F ζ hζ C R P H U a) = _
      rw [integral_sub
        (KPContinuation.ChamberModerateGrowth.actualCuspSheet_kernel_integrable F ζ hζ C R P H U ι hι f hf a s hs t b δ)
        (integrable_const _), integral_const]
      simp only [Pi.sub_apply, probReal_univ, one_smul]
    rw [he, map_sub, KPContActualChamberOutgoingAdapter.zeroProjection_reconstruct]
    rfl
  unfold correctionMeanZeroSheet KPContActualChamberOutgoingAdapter.correctionSheet meanZeroJetSheet
  rw [hcut, hmode]
  simp only [Submodule.coe_sub, Pi.sub_apply]
  rw [W.property.2 (QuotientAddGroup.mk x)]
  change _ = _ - _
  simp only [KPContActualChamberCasimirJets.cuspSheet, KPContActualChamberCasimirJets.jet, iteratedDerivWithin_zero]
  ring

include hι hf in
private theorem scalar_correction_holomorphic
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) :
    DifferentiableOn ℂ (fun w => KPContActualChamberOutgoingAdapter.correctionSheet
      F ζ hζ C R P H U a ι buffer f χ source w p.2 p.1.1 p.1.2 1) V := by
  apply (E_holo F ζ hζ U ι f hι hf
    (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a p.2 p.1.1 p.1.2 1)).sub
  have hh := (source_component_holo F ζ hζ C R P H U ι f buffer χ source false a.1
    (KPContSectorSmoothFramesSupport.cuspPoint F ζ hζ (level F ζ hζ C R P H U) R P H
      a.1 a.2 p)).mono (show V ⊆ KPContinuation.spectralDomain from by
        intro s hs; change -(1 : ℝ)/6 < s.re; change (1 : ℝ)/3 < s.re at hs; linarith)
  simpa [KPContActualCutoffSmoothDescent.coveredPoint] using hh

include hι hf in
private theorem scalar_zero_holomorphic
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) (ht : T + 1 ≤ p.2) (hb : buffer.τ < p.2) :
    DifferentiableOn ℂ (fun w => KPContActualChamberOutgoingAdapter.zeroScalar
      F ζ hζ C R P H U a ι buffer f χ source w p) V := by
  have hexp : DifferentiableOn ℂ (fun w => KPChamberOutgoingL2.outgoingFactor
      (KPContActualChamberOutgoingAdapter.d F) w p.2) V := by
    unfold KPChamberOutgoingL2.outgoingFactor
    fun_prop
  apply (hexp.mul (KPContActualChamberOutgoingAdapter.coefficient_holomorphic
    F ζ hζ C R P H U a ι f hι hf p.1.2)).congr
  intro w hw
  unfold KPContActualChamberOutgoingAdapter.zeroScalar
  rw [KPContActualChamberOutgoingAdapter.outgoing_formula
    F ζ hζ C R P H U a ι buffer f χ source hι hf w hw p.2 p.1.2 ht hb]
  rfl

include hι hf in

theorem g_cusp_split (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) (ht : T + 1 ≤ p.2) (hb : buffer.τ < p.2) :
    g F ζ hζ C R P H U ι f buffer χ source k s
      (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a 1 p) =
    KPContActualChamberOutgoingAdapter.parameterScalar F ζ hζ C R P H U
      a ι buffer f χ source k s (KPCuspCharts.toArch F p) +
    KPContActualChamberMeanZeroAdapter.jetScalar F ζ hζ C R P H U
      a ι f k s p := by
  have he : (KPCuspCharts.toArchHomeomorph F
      (KPContActualChamberMeanZeroAdapter.geometry F ζ hζ C R P H U a).positive_dimension).symm
      (KPCuspCharts.toArch F p) = p := Homeomorph.symm_apply_apply _ p
  have he' : (KPCuspCharts.toArchHomeomorph F
      (KPContActualChamberOutgoingAdapter.geometry F ζ hζ C R P H U a).positive_dimension).symm
      (KPCuspCharts.toArch F p) = p := Homeomorph.symm_apply_apply _ p
  have hm : KPContActualChamberMeanZeroAdapter.jetScalar F ζ hζ C R P H U a ι f k s p =
      iteratedDerivWithin k ((fun w => KPContActualChamberOutgoingAdapter.correctionSheet
        F ζ hζ C R P H U a ι buffer f χ source w p.2 p.1.1 p.1.2 1) -
        (fun w => KPContActualChamberOutgoingAdapter.zeroScalar
          F ζ hζ C R P H U a ι buffer f χ source w p)) V s := by
    unfold KPContActualChamberMeanZeroAdapter.jetScalar
      KPContActualChamberMeanZeroAdapter.parameterScalar KPContActualChamberMeanZeroAdapter.meanZero
    rw [he]
    apply iteratedDerivWithin_congr _ hs
    intro w hw
    dsimp only [Pi.sub_apply]
    rw [← scalar_correction_complement_eq F ζ hζ C R P H U ι f buffer χ source hι hf a w hw
      p.2 p.1.1 p.1.2 1 hb]
    unfold KPContActualChamberMeanZeroAdapter.correctionMeanZeroSheet
      KPContActualChamberOutgoingAdapter.zeroScalar
    rw [(KPContActualChamberOutgoingAdapter.zeroMode F ζ hζ C R P H U a ι buffer f χ source
      w p.2 p.1.2).property.2 (QuotientAddGroup.mk p.1.1)]
    simp
  rw [hm, iteratedDerivWithin_sub hs KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
    (((scalar_correction_holomorphic F ζ hζ C R P H U ι f buffer χ source hι hf a p).contDiffOn
      KPChamberL2Defect.chamber_isOpen).contDiffWithinAt hs)
    (((scalar_zero_holomorphic F ζ hζ C R P H U ι f buffer χ source hι hf a p ht hb).contDiffOn
      KPChamberL2Defect.chamber_isOpen).contDiffWithinAt hs)]
  unfold KPContActualChamberOutgoingAdapter.parameterScalar
  rw [he', g_cusp_scalar F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a p]
  ring

theorem sectionNorm_cusp_split_sq (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) (ht : T + 1 ≤ p.2) (hb : buffer.τ < p.2) :
    (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ (level F ζ hζ C R P H U) R P H
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)
      (KPContActualCollarBuffer.chartLift F ζ hζ (level F ζ hζ C R P H U) R P H a p)) ^ 2 ≤
    2 * (KPContActualChamberOutgoingAdapter.jetNorm F ζ hζ C R P H U
      a ι buffer f χ source k 0 s p) ^ 2 +
    2 * ‖KPContActualChamberMeanZeroAdapter.jetScalar F ζ hζ C R P H U a ι f k s p‖ ^ 2 := by
  rw [sectionNorm_cusp_scalar F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a p,
    ← g_cusp_scalar F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a p,
    g_cusp_split F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a p ht hb]
  simp only [KPContActualChamberOutgoingAdapter.jetNorm,
    KPContActualChamberOutgoingAdapter.covariantNorm, ite_true]
  have hn := norm_add_le
    (KPContActualChamberOutgoingAdapter.parameterScalar F ζ hζ C R P H U
      a ι buffer f χ source k s (KPCuspCharts.toArch F p))
    (KPContActualChamberMeanZeroAdapter.jetScalar F ζ hζ C R P H U a ι f k s p)
  have hsq := sq_nonneg
    (‖KPContActualChamberOutgoingAdapter.parameterScalar F ζ hζ C R P H U
      a ι buffer f χ source k s (KPCuspCharts.toArch F p)‖ -
      ‖KPContActualChamberMeanZeroAdapter.jetScalar F ζ hζ C R P H U a ι f k s p‖)
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith

theorem lineG_norm_continuous (k : ℕ) (s : ℂ) :
    Continuous (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ
      (level F ζ hζ C R P H U) R P H
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)) := by
  have hq := (KPContSectorQuotientRelationsComparison.q_isOpenMap F ζ hζ
    (level F ζ hζ C R P H U)).isQuotientMap
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ (level F ζ hζ C R P H U))
    (KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ (level F ζ hζ C R P H U))
  apply hq.continuous_iff.mpr
  have hc := (KPContSectorLineL2Isometry.continuous_iff F ζ hζ
    (level F ζ hζ C R P H U) R P H _).mp
    (fun i => ((smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1 i).continuous)
  convert hc.norm using 1
  funext v
  rw [Function.comp_apply, KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
  unfold lineG
  rw [LinearEquiv.symm_apply_apply, KPContSectorSmoothFramesSupport.sectionNorm_pullback]

theorem lineG_compact_square_finite (k : ℕ) (s : ℂ)
    (K : Set (Base F ζ hζ C R P H U)) (hK : IsCompact K) :
    (∫⁻ x in K, KPContSectorLineL2Isometry.squaredNorm F ζ hζ
      (level F ζ hζ C R P H U) R P H
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
      ∂baseMeasure F ζ hζ C R P H U) < ⊤ := by
  letI := KPContSectorFixedMeasureLocalFiniteness.sphericalMeasure_finiteOnCompacts
    F ζ hζ R P (level F ζ hζ C R P H U)
  have hc := (lineG_norm_continuous F ζ hζ C R P H U ι f buffer χ source hι hf k s).pow 2
  have hi := hc.continuousOn.integrableOn_compact (μ := baseMeasure F ζ hζ C R P H U) hK
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun x => sq_nonneg _))).mp hi.hasFiniteIntegral

theorem lineG_end_square_transport (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (A : ℝ) (hA : (H.atlas (level F ζ hζ C R P H U)).threshold < A) :
    (∫⁻ x in KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A a,
      KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H
        (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
      ∂baseMeasure F ζ hζ C R P H U) =
    ∫⁻ p in {p : KPCuspCharts.Coordinates F | A < p.2}, ENNReal.ofReal
      (‖iteratedDerivWithin k (fun w => KPContActualChamberOutgoingAdapter.correctionSheet
        F ζ hζ C R P H U a ι buffer f χ source w p.2 p.1.1 p.1.2 1) V s‖ ^ 2)
      ∂KPContActualChamberOutgoingAdapter.endMeasure F ζ hζ C R P H U a := by
  rw [← KPContActualEndHaarTransport.actual_end_coordinates_pushforward
    F ζ hζ C R P H U a A hA]
  rw [lintegral_map (KPContSectorLineL2Isometry.squaredNorm_measurable
    F ζ hζ (level F ζ hζ C R P H U) R P H _
      (fun i => ((smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1 i).continuous.measurable))
    (show Measurable (KPContActualCollarBuffer.chartLift F ζ hζ
      (level F ζ hζ C R P H U) R P H a) from by
        unfold KPContActualCollarBuffer.chartLift
        exact (continuous_quotient_mk'.comp
          (((KPCuspCharts.projectiveHomeomorph F
            (((H.atlas (level F ζ hζ C R P H U)).cuspAtlas a.1).representative a.2)).continuous.comp
            (KPCuspCharts.toArch_contDiff F).continuous).prodMk continuous_const)).measurable)]
  apply lintegral_congr
  intro p
  unfold KPContSectorLineL2Isometry.squaredNorm
  rw [sectionNorm_cusp_scalar F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a p]

theorem gradient_norm_cusp (k : ℕ) (s : ℂ)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) :
    (KPContActualCotangentMeasurableFamilies.normSquare
      (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s)
      (KPContActualCollarBuffer.chartLift F ζ hζ (level F ζ hζ C R P H U) R P H a p) : ℝ) =
    KPContActualChamberOutgoingAdapter.covariantNorm (KPCuspLogShape.dimension F) 1
      (fun z => (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s a.1).val
        (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a • z))
      (KPCuspCharts.toArch F p) ^ 2 := by
  let w := lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s
  have hw := (smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1
  have hc := KPContThreeL2CotangentHelpers.smoothGradient_cusp_coframe w hw a p.1 p.2
  have hq : KPContActualCollarBuffer.chartLift F ζ hζ (level F ζ hζ C R P H U) R P H a p =
      (H.atlas (level F ζ hζ C R P H U)).components ⟨a.1, Quotient.mk _
        (KPContSectorSmoothFramesSupport.cuspPoint F ζ hζ (level F ζ hζ C R P H U) R P H a.1 a.2 p)⟩ := by
    rw [(H.atlas _).components_formula]
    rfl
  rw [hq]
  change (∑ i, ∑ j, ‖HyperbolicChart.differential (KPContCotangentActualOverlap.d F)
      (fun x => (w a.1).val (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a •
        KPContCotangentActualOverlap.labeledA (KPContCotangentActualOverlap.placeEquiv F ζ hζ) x))
      (KPContCotangentActualOverlap.labeledAInv (KPContCotangentActualOverlap.placeEquiv F ζ hζ)
        (KPCuspCharts.toArch F p)) i j‖ ^ 2) = _ at hc
  change (KPContActualCotangentMeasurableFamilies.normSquare
    (KPContThreeL2CotangentHelpers.smoothGradient w hw) _ : ℝ) = _
  rw [← hc]
  have hr := KPContThreeL2CotangentHelpers.coframe_reindex
    (KPContCotangentActualOverlap.d F) (KPCuspLogShape.dimension F)
    (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.1.symm
    (fun z => (w a.1).val (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a • z))
    (KPCuspCharts.toArch F p)
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z => (w a.1).val
      (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a • z)) :=
    (hw a.1).comp (CoreChartLocalizers.CutoffConstruction.StabilizerLinearization.rational_action_contDiff F
      (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a))
  exact hr.trans (KPContThreeL2CotangentHelpers.arch_coframe_norm _ _ hg _)

include hι hf in

theorem lineG_cusp_split_germ (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) (ht : T + 1 < p.2) (hb : buffer.τ < p.2) :
    (fun z => (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s a.1).val
      (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a • z)) =ᶠ[𝓝 (KPCuspCharts.toArch F p)]
    (KPContActualChamberOutgoingAdapter.parameterScalar F ζ hζ C R P H U a ι buffer f χ source k s +
      KPContActualChamberMeanZeroAdapter.parameterScalar F ζ hζ C R P H U a ι f k s) := by
  let n := KPCuspLogShape.dimension F
  have hm : Continuous (KPCuspLogShape.meanHeight n) :=
    by
      unfold KPCuspLogShape.meanHeight
      fun_prop
  have hmean : KPCuspLogShape.meanHeight n (KPCuspCharts.toArch F p) = p.2 :=
    KPCuspCharts.toArch_meanHeight F (KPContActualChamberOutgoingAdapter.geometry F ζ hζ C R P H U a).positive_dimension p
  have hopen : IsOpen {z : KPArch.Space n | T+1 < KPCuspLogShape.meanHeight n z ∧
      buffer.τ < KPCuspLogShape.meanHeight n z} :=
    (isOpen_lt continuous_const hm).inter (isOpen_lt continuous_const hm)
  have hnhds : {z : KPArch.Space n | T+1 < KPCuspLogShape.meanHeight n z ∧
      buffer.τ < KPCuspLogShape.meanHeight n z} ∈ 𝓝 (KPCuspCharts.toArch F p) :=
    hopen.mem_nhds (by simpa [hmean] using And.intro ht hb)
  filter_upwards [hnhds] with z hz
  let e := KPCuspCharts.toArchHomeomorph F (KPContActualChamberOutgoingAdapter.geometry F ζ hζ C R P H U a).positive_dimension
  let q := e.symm z
  have hq : KPCuspCharts.toArch F q = z := e.apply_symm_apply z
  have hqt : q.2 = KPCuspLogShape.meanHeight n z := by
    rw [← hq, KPCuspCharts.toArch_meanHeight F (KPContActualChamberOutgoingAdapter.geometry F ζ hζ C R P H U a).positive_dimension]
  have hv : (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s a.1).val
      (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a • KPCuspCharts.toArch F q) =
      g F ζ hζ C R P H U ι f buffer χ source k s
        (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a 1 q) := by
    have hv' : (coveredG F ζ hζ C R P H U ι f buffer χ source hι hf k s).val
        (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a 1 q) =
        (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s a.1).val
          (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a • KPCuspCharts.toArch F q) := by
      unfold lineG
      rw [KPContSectorScalarLineAlgebra.S_apply]
      simp [KPContActualCutoffSmoothDescent.coveredPoint, KPContSectorSmoothFramesSupport.cuspPoint,
        KPContFlatCuspIncomingEvaluation.sigma, KPContFlatCuspIncomingEvaluation.atlas]
    rw [← hv']
    simp [coveredG, hs]
  rw [← hq, hv, g_cusp_split F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a q
    (by rw [hqt]; exact hz.1.le) (by rw [hqt]; exact hz.2)]
  rfl

private theorem covariant_gradient_sum_le (n : ℕ) (g f h : KPArch.Space n → ℂ) (z : KPArch.Space n)
    (he : g =ᶠ[𝓝 z] f+h) (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) :
    KPContActualChamberOutgoingAdapter.covariantNorm n 1 g z ^ 2 ≤
      2 * (KPContActualChamberOutgoingAdapter.covariantNorm n 1 f z ^ 2 +
        KPContActualChamberOutgoingAdapter.covariantNorm n 1 h z ^ 2) := by
  have hd : ∀ v, KPContActualChamberOutgoingAdapter.frameDerivative n v g z =
      KPContActualChamberOutgoingAdapter.frameDerivative n v f z +
      KPContActualChamberOutgoingAdapter.frameDerivative n v h z := by
    intro v
    unfold KPContActualChamberOutgoingAdapter.frameDerivative
    rw [he.fderiv_eq, fderiv_add hf hh]
    dsimp only
    simp only [add_apply]
    ring
  simp only [KPContActualChamberOutgoingAdapter.covariantNorm, Fin.reduceEq, ite_false, ite_true]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp_rw [hd]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  exact (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (norm_add_le _ _) |>.trans (add_sq_le)

theorem gradient_cusp_split_sq (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) (ht : T + 1 < p.2) (hb : buffer.τ < p.2) :
    (KPContActualCotangentMeasurableFamilies.normSquare
      (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s)
      (KPContActualCollarBuffer.chartLift F ζ hζ (level F ζ hζ C R P H U) R P H a p) : ℝ) ≤
      2 * (KPContActualChamberOutgoingAdapter.jetNorm F ζ hζ C R P H U a ι buffer f χ source k 1 s p ^ 2 +
        KPContActualChamberMeanZeroAdapter.gradientSq F ζ hζ C R P H U a ι f k s p) := by
  let z := KPCuspCharts.toArch F p
  let n := KPCuspLogShape.dimension F
  let o := KPContActualChamberOutgoingAdapter.parameterScalar F ζ hζ C R P H U a ι buffer f χ source k s
  let m := KPContActualChamberMeanZeroAdapter.parameterScalar F ζ hζ C R P H U a ι f k s
  have ho : DifferentiableAt ℝ o z := by
    have hgerm := KPContActualChamberOutgoingAdapter.parameterScalar_radialModel_germ
      F ζ hζ C R P H U a ι buffer f χ source hι hf k s hs z
      (by rwa [KPCuspCharts.toArch_meanHeight F (KPContActualChamberOutgoingAdapter.geometry F ζ hζ C R P H U a).positive_dimension])
      (by rwa [KPCuspCharts.toArch_meanHeight F (KPContActualChamberOutgoingAdapter.geometry F ζ hζ C R P H U a).positive_dimension])
    have hrad := (KPContActualChamberOutgoingAdapter.radialModel_derivatives F ζ hζ C R P H U a ι f k s).1
    have hm : Differentiable ℝ (KPCuspLogShape.meanHeight n) := by
      unfold KPCuspLogShape.meanHeight
      fun_prop
    exact ((hrad (KPCuspLogShape.meanHeight n z)).comp z (hm z)).congr_of_eventuallyEq hgerm
  have hmn : KPCuspLogShape.meanHeight n z = p.2 :=
    KPCuspCharts.toArch_meanHeight F (KPContActualChamberMeanZeroAdapter.geometry F ζ hζ C R P H U a).positive_dimension p
  have hm : ContDiffAt ℝ (⊤ : ℕ∞) m z := by
    obtain ⟨v,hv,_,_⟩ := KPContActualChamberMeanZeroAdapter.actual_meanZero_jet_sections
      F ζ hζ C R P H U ι f hι hf a s hs (KPCuspLogShape.meanHeight n z - 1)
    change ContDiffAt ℝ (⊤ : ℕ∞) (KPContActualChamberMeanZeroAdapter.parameterScalar F ζ hζ C R P H U a ι f k s) z
    rw [← hv k]
    exact (v k).smooth.contDiffAt ((isOpen_lt continuous_const
      (by unfold KPCuspLogShape.meanHeight; fun_prop)).mem_nhds (by dsimp; linarith))
  rw [gradient_norm_cusp F ζ hζ C R P H U ι f buffer χ source hι hf k s a p]
  have hg := covariant_gradient_sum_le n _ o m z
    (lineG_cusp_split_germ F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a p ht hb)
    ho (hm.differentiableAt (by simp))
  have hmc := KPContThreeL2CotangentHelpers.arch_coframe_norm_at n m z (hm.differentiableAt (by simp))
  change KPContActualChamberMeanZeroAdapter.gradientSq F ζ hζ C R P H U a ι f k s p =
    KPContActualChamberOutgoingAdapter.covariantNorm n 1 m z ^ 2 at hmc
  rw [hmc]
  exact hg

theorem gradient_end_square_transport (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (A : ℝ) (hA : (H.atlas (level F ζ hζ C R P H U)).threshold < A) :
    (∫⁻ x in KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A a,
      (KPContActualCotangentMeasurableFamilies.normSquare
        (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) x : ℝ≥0∞)
      ∂baseMeasure F ζ hζ C R P H U) =
    ∫⁻ p in {p : KPCuspCharts.Coordinates F | A < p.2}, ENNReal.ofReal
      (KPContActualChamberOutgoingAdapter.covariantNorm (KPCuspLogShape.dimension F) 1
        (fun z => (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s a.1).val
          (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a • z))
        (KPCuspCharts.toArch F p) ^ 2)
      ∂KPContActualChamberOutgoingAdapter.endMeasure F ζ hζ C R P H U a := by
  rw [← KPContActualEndHaarTransport.actual_end_coordinates_pushforward
    F ζ hζ C R P H U a A hA]
  rw [lintegral_map ((KPContActualCotangentMeasurableFamilies.measurable_normSquare _).coe_nnreal_ennreal)
    (show Measurable (KPContActualCollarBuffer.chartLift F ζ hζ
      (level F ζ hζ C R P H U) R P H a) from by
        unfold KPContActualCollarBuffer.chartLift
        exact (continuous_quotient_mk'.comp
          (((KPCuspCharts.projectiveHomeomorph F
            (((H.atlas (level F ζ hζ C R P H U)).cuspAtlas a.1).representative a.2)).continuous.comp
            (KPCuspCharts.toArch_contDiff F).continuous).prodMk continuous_const)).measurable)]
  apply lintegral_congr
  intro p
  have hh := gradient_norm_cusp F ζ hζ C R P H U ι f buffer χ source hι hf k s a p
  have hp : (KPContActualCotangentMeasurableFamilies.normSquare
      (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s)
      (KPContActualCollarBuffer.chartLift F ζ hζ (level F ζ hζ C R P H U) R P H a p) : ℝ≥0∞) =
      ENNReal.ofReal (KPContActualChamberOutgoingAdapter.covariantNorm (KPCuspLogShape.dimension F) 1
        (fun z => (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s a.1).val
          (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a • z))
        (KPCuspCharts.toArch F p) ^ 2) := by
    rw [← hh, ENNReal.ofReal_coe_nnreal]
  exact hp

theorem gradient_end_square_le (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (A : ℝ) (hA : (H.atlas (level F ζ hζ C R P H U)).threshold < A)
    (hT : T + 1 ≤ A) (hb : buffer.τ < A)
    (hout : AEMeasurable (fun p => ENNReal.ofReal
      ((KPContActualChamberOutgoingAdapter.jetNorm F ζ hζ C R P H U a ι buffer f χ source k 1 s p) ^ 2))
      ((KPContActualChamberOutgoingAdapter.endMeasure F ζ hζ C R P H U a).restrict {p | A < p.2})) :
    (∫⁻ x in KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A a,
      (KPContActualCotangentMeasurableFamilies.normSquare
        (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) x : ℝ≥0∞)
      ∂baseMeasure F ζ hζ C R P H U) ≤
    (2 : ℝ≥0∞) * KPContActualChamberOutgoingAdapter.squareTail F ζ hζ C R P H U a ι buffer f χ source k 1 s A +
    (2 : ℝ≥0∞) * KPContActualChamberMeanZeroAdapter.energy F ζ hζ C R P H U a ι f k s 0 A := by
  rw [gradient_end_square_transport F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a A hA]
  have hsplit : ∀ p : KPCuspCharts.Coordinates F, A < p.2 →
      ENNReal.ofReal (KPContActualChamberOutgoingAdapter.covariantNorm (KPCuspLogShape.dimension F) 1
        (fun z => (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s a.1).val
          (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a • z))
        (KPCuspCharts.toArch F p) ^ 2) ≤
      (2 : ℝ≥0∞) * ENNReal.ofReal ((KPContActualChamberOutgoingAdapter.jetNorm
        F ζ hζ C R P H U a ι buffer f χ source k 1 s p) ^ 2) +
      (2 : ℝ≥0∞) * ENNReal.ofReal
        (KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p) := by
    intro p hp
    have hh := gradient_cusp_split_sq F ζ hζ C R P H U ι f buffer χ source hι hf
      k s hs a p (hT.trans_lt hp) (hb.trans hp)
    rw [gradient_norm_cusp F ζ hζ C R P H U ι f buffer χ source hι hf k s a p] at hh
    have he : KPContActualChamberMeanZeroAdapter.gradientSq F ζ hζ C R P H U a ι f k s p ≤
        KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p := by
      unfold KPContActualChamberMeanZeroAdapter.energyDensity KPContActualChamberMeanZeroAdapter.gradientSq
      simp only [mul_zero, zero_mul, Real.exp_zero, one_mul]
      exact le_add_of_nonneg_left (sq_nonneg _)
    have henergy : 0 ≤ KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p :=
      (Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => sq_nonneg _).trans he
    calc
      _ ≤ ENNReal.ofReal (2 * (KPContActualChamberOutgoingAdapter.jetNorm
          F ζ hζ C R P H U a ι buffer f χ source k 1 s p) ^ 2 +
          2 * KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p) :=
        ENNReal.ofReal_le_ofReal (hh.trans (by linarith))
      _ = _ := by rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]; norm_num
  calc
    _ ≤ ∫⁻ p in {p : KPCuspCharts.Coordinates F | A < p.2},
        (2 : ℝ≥0∞) * ENNReal.ofReal ((KPContActualChamberOutgoingAdapter.jetNorm
          F ζ hζ C R P H U a ι buffer f χ source k 1 s p) ^ 2) +
        (2 : ℝ≥0∞) * ENNReal.ofReal
          (KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p)
        ∂KPContActualChamberOutgoingAdapter.endMeasure F ζ hζ C R P H U a :=
      setLIntegral_mono' (measurableSet_lt measurable_const (by fun_prop)) (by intro p hp; exact hsplit p hp)
    _ ≤ (2 : ℝ≥0∞) * KPContActualChamberOutgoingAdapter.squareTail F ζ hζ C R P H U
        a ι buffer f χ source k 1 s A +
        (2 : ℝ≥0∞) * KPContActualChamberMeanZeroAdapter.energy F ζ hζ C R P H U a ι f k s 0 A := by
      unfold KPContActualChamberOutgoingAdapter.squareTail KPContActualChamberMeanZeroAdapter.energy
      rw [← lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num),
        ← lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num)]
      exact le_of_eq (lintegral_add_left' (hout.const_mul 2) _)

theorem gradient_high_end_square_bound (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V)
    (k : ℕ) : ∃ A B : ℝ,
    (H.atlas (level F ζ hζ C R P H U)).threshold < A ∧ 0 ≤ B ∧
    ∀ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U, ∀ s ∈ L,
    (∫⁻ x in KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A a,
      (KPContActualCotangentMeasurableFamilies.normSquare
        (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) x : ℝ≥0∞)
      ∂baseMeasure F ζ hζ C R P H U) ≤ ENNReal.ofReal B := by
  obtain ⟨t₀,c,h0,hT,hb,hc,hbound⟩ := KPContActualChamberOutgoingAdapter.jets_memLp_square_bound
    F ζ hζ C R P H U ι buffer f χ source hι hf L hL hLV k 1
  have hm := DedekindZetaZeroFree.kp_cont_actual_chamber_mean_zero_adapter F ζ hζ C R P H U
    (DedekindZetaZeroFree.actual_levelRealization_of_recipe
      F ζ hζ (level F ζ hζ C R P H U) R P H) ι hι f hf buffer χ source
  obtain ⟨t₁,b,h10,h1atlas,h1b,h1T,hb0,hmbound,hmtail⟩ := hm.weighted_tails L hL hLV k 0 le_rfl
  let A := max t₀ t₁
  have h0A : t₀ ≤ A := le_max_left _ _
  have h1A : t₁ ≤ A := le_max_right _ _
  have hA : (H.atlas (level F ζ hζ C R P H U)).threshold < A := h1atlas.trans_le h1A
  refine ⟨A,2*c+2*b,hA,by positivity,?_⟩
  intro a s hs
  have hout : KPContActualChamberOutgoingAdapter.squareTail F ζ hζ C R P H U
      a ι buffer f χ source k 1 s A ≤ ENNReal.ofReal c :=
    (lintegral_mono_set (fun p hp => lt_of_le_of_lt h0A hp)).trans (hbound a s hs).2
  have hmean : KPContActualChamberMeanZeroAdapter.energy F ζ hζ C R P H U
      a ι f k s 0 A ≤ ENNReal.ofReal b := by
    apply (hmtail A h1A a s hs).2.1.trans
    simp
  have hmeas := ((KPContActualChamberOutgoingAdapter.jetNorm_high_aestronglyMeasurable
    F ζ hζ C R P H U a ι buffer f χ source hι hf k 1 s (hLV hs) A
    (hT.trans_le h0A) (hb.trans_le h0A)).aemeasurable.pow_const 2).ennreal_ofReal
  apply (gradient_end_square_le F ζ hζ C R P H U ι f buffer χ source hι hf k s (hLV hs)
    a A hA (hT.trans_le h0A).le (hb.trans_le h0A) hmeas).trans
  calc
    _ ≤ 2 * ENNReal.ofReal c + 2 * ENNReal.ofReal b :=
      add_le_add (mul_le_mul_right hout _) (mul_le_mul_right hmean _)
    _ = ENNReal.ofReal (2*c+2*b) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
      norm_num

theorem lineG_end_square_le (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (A : ℝ) (hA : (H.atlas (level F ζ hζ C R P H U)).threshold < A)
    (hT : T + 1 ≤ A) (hb : buffer.τ < A)
    (hout : AEMeasurable (fun p => ENNReal.ofReal
      ((KPContActualChamberOutgoingAdapter.jetNorm F ζ hζ C R P H U a ι buffer f χ source k 0 s p) ^ 2))
      ((KPContActualChamberOutgoingAdapter.endMeasure F ζ hζ C R P H U a).restrict {p | A < p.2})) :
    (∫⁻ x in KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A a,
      KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H
        (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
      ∂baseMeasure F ζ hζ C R P H U) ≤
    (2 : ℝ≥0∞) * KPContActualChamberOutgoingAdapter.squareTail F ζ hζ C R P H U a ι buffer f χ source k 0 s A +
    (2 : ℝ≥0∞) * KPContActualChamberMeanZeroAdapter.energy F ζ hζ C R P H U a ι f k s 0 A := by
  rw [lineG_end_square_transport F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a A hA]
  have hsplit : ∀ p : KPCuspCharts.Coordinates F, A < p.2 →
      ENNReal.ofReal (‖iteratedDerivWithin k
        (fun w => KPContActualChamberOutgoingAdapter.correctionSheet
          F ζ hζ C R P H U a ι buffer f χ source w p.2 p.1.1 p.1.2 1) V s‖ ^ 2) ≤
      (2 : ℝ≥0∞) * ENNReal.ofReal ((KPContActualChamberOutgoingAdapter.jetNorm
        F ζ hζ C R P H U a ι buffer f χ source k 0 s p) ^ 2) +
      (2 : ℝ≥0∞) * ENNReal.ofReal
        (KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p) := by
    intro p hp
    have hh := sectionNorm_cusp_split_sq F ζ hζ C R P H U ι f buffer χ source hι hf
      k s hs a p (hT.trans hp.le) (hb.trans hp)
    rw [sectionNorm_cusp_scalar F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a p] at hh
    have he : ‖KPContActualChamberMeanZeroAdapter.jetScalar F ζ hζ C R P H U a ι f k s p‖ ^ 2 ≤
        KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p := by
      unfold KPContActualChamberMeanZeroAdapter.energyDensity KPContActualChamberMeanZeroAdapter.gradientSq
      simp only [mul_zero, zero_mul, Real.exp_zero, one_mul]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => sq_nonneg _)
    have henergy : 0 ≤ KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p :=
      (sq_nonneg _).trans he
    calc
      _ ≤ ENNReal.ofReal (2 * (KPContActualChamberOutgoingAdapter.jetNorm
          F ζ hζ C R P H U a ι buffer f χ source k 0 s p) ^ 2 +
          2 * KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p) :=
        ENNReal.ofReal_le_ofReal (hh.trans (by linarith))
      _ = _ := by rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]; norm_num
  calc
    _ ≤ ∫⁻ p in {p : KPCuspCharts.Coordinates F | A < p.2},
        (2 : ℝ≥0∞) * ENNReal.ofReal ((KPContActualChamberOutgoingAdapter.jetNorm
          F ζ hζ C R P H U a ι buffer f χ source k 0 s p) ^ 2) +
        (2 : ℝ≥0∞) * ENNReal.ofReal
          (KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p)
        ∂KPContActualChamberOutgoingAdapter.endMeasure F ζ hζ C R P H U a :=
      setLIntegral_mono' (measurableSet_lt measurable_const (by fun_prop)) (by intro p hp; exact hsplit p hp)
    _ ≤ (2 : ℝ≥0∞) * KPContActualChamberOutgoingAdapter.squareTail F ζ hζ C R P H U
        a ι buffer f χ source k 0 s A +
        (2 : ℝ≥0∞) * KPContActualChamberMeanZeroAdapter.energy F ζ hζ C R P H U a ι f k s 0 A := by
      unfold KPContActualChamberOutgoingAdapter.squareTail KPContActualChamberMeanZeroAdapter.energy
      rw [← lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num),
        ← lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num)]
      exact le_of_eq (lintegral_add_left' (hout.const_mul 2) _)

theorem lineG_high_end_square_bound (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V)
    (k : ℕ) : ∃ A B : ℝ,
    (H.atlas (level F ζ hζ C R P H U)).threshold < A ∧ 0 ≤ B ∧
    ∀ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U, ∀ s ∈ L,
    (∫⁻ x in KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A a,
      KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H
        (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
      ∂baseMeasure F ζ hζ C R P H U) ≤ ENNReal.ofReal B := by
  obtain ⟨t₀,c,h0,hT,hb,hc,hbound⟩ := KPContActualChamberOutgoingAdapter.jets_memLp_square_bound
    F ζ hζ C R P H U ι buffer f χ source hι hf L hL hLV k 0
  have hm := DedekindZetaZeroFree.kp_cont_actual_chamber_mean_zero_adapter F ζ hζ C R P H U
    (DedekindZetaZeroFree.actual_levelRealization_of_recipe
      F ζ hζ (level F ζ hζ C R P H U) R P H) ι hι f hf buffer χ source
  obtain ⟨t₁,b,h10,h1atlas,h1b,h1T,hb0,hmbound,hmtail⟩ := hm.weighted_tails L hL hLV k 0 le_rfl
  let A := max t₀ t₁
  have h0A : t₀ ≤ A := le_max_left _ _
  have h1A : t₁ ≤ A := le_max_right _ _
  have hA : (H.atlas (level F ζ hζ C R P H U)).threshold < A := h1atlas.trans_le h1A
  refine ⟨A,2*c+2*b,hA,by positivity,?_⟩
  intro a s hs
  rw [lineG_end_square_transport F ζ hζ C R P H U ι f buffer χ source hι hf k s (hLV hs) a A hA]
  have hout : KPContActualChamberOutgoingAdapter.squareTail F ζ hζ C R P H U
      a ι buffer f χ source k 0 s A ≤ ENNReal.ofReal c :=
    (lintegral_mono_set (fun p hp => lt_of_le_of_lt h0A hp)).trans (hbound a s hs).2
  have hmean : KPContActualChamberMeanZeroAdapter.energy F ζ hζ C R P H U
      a ι f k s 0 A ≤ ENNReal.ofReal b := by
    apply (hmtail A h1A a s hs).2.1.trans
    simp
  have hsplit : ∀ p : KPCuspCharts.Coordinates F, A < p.2 →
      ENNReal.ofReal (‖iteratedDerivWithin k
        (fun w => KPContActualChamberOutgoingAdapter.correctionSheet
          F ζ hζ C R P H U a ι buffer f χ source w p.2 p.1.1 p.1.2 1) V s‖ ^ 2) ≤
      (2 : ℝ≥0∞) * ENNReal.ofReal ((KPContActualChamberOutgoingAdapter.jetNorm
        F ζ hζ C R P H U a ι buffer f χ source k 0 s p) ^ 2) +
      (2 : ℝ≥0∞) * ENNReal.ofReal
        (KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p) := by
    intro p hp
    have hh := sectionNorm_cusp_split_sq F ζ hζ C R P H U ι f buffer χ source hι hf
      k s (hLV hs) a p (hT.le.trans (h0A.trans hp.le)) (hb.trans_le h0A |>.trans hp)
    rw [sectionNorm_cusp_scalar F ζ hζ C R P H U ι f buffer χ source hι hf k s (hLV hs) a p] at hh
    have he : ‖KPContActualChamberMeanZeroAdapter.jetScalar F ζ hζ C R P H U a ι f k s p‖ ^ 2 ≤
        KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p := by
      unfold KPContActualChamberMeanZeroAdapter.energyDensity KPContActualChamberMeanZeroAdapter.gradientSq
      simp only [mul_zero, zero_mul, Real.exp_zero, one_mul]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => sq_nonneg _)
    have henergy : 0 ≤ KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p :=
      (sq_nonneg _).trans he
    calc
      _ ≤ ENNReal.ofReal (2 * (KPContActualChamberOutgoingAdapter.jetNorm
          F ζ hζ C R P H U a ι buffer f χ source k 0 s p) ^ 2 +
          2 * KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p) :=
        ENNReal.ofReal_le_ofReal (hh.trans (by linarith))
      _ = _ := by rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]; norm_num
  calc
    _ ≤ ∫⁻ p in {p : KPCuspCharts.Coordinates F | A < p.2},
        (2 : ℝ≥0∞) * ENNReal.ofReal ((KPContActualChamberOutgoingAdapter.jetNorm
          F ζ hζ C R P H U a ι buffer f χ source k 0 s p) ^ 2) +
        (2 : ℝ≥0∞) * ENNReal.ofReal
          (KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p)
        ∂KPContActualChamberOutgoingAdapter.endMeasure F ζ hζ C R P H U a :=
      setLIntegral_mono' (measurableSet_lt measurable_const (by fun_prop)) (by intro p hp; exact hsplit p hp)
    _ ≤ (2 : ℝ≥0∞) * KPContActualChamberOutgoingAdapter.squareTail F ζ hζ C R P H U
        a ι buffer f χ source k 0 s A +
        (2 : ℝ≥0∞) * KPContActualChamberMeanZeroAdapter.energy F ζ hζ C R P H U a ι f k s 0 A := by
      have hmnorm : AEMeasurable (fun p => ENNReal.ofReal
          ((KPContActualChamberOutgoingAdapter.jetNorm F ζ hζ C R P H U a ι buffer f χ source k 0 s p) ^ 2))
          ((KPContActualChamberOutgoingAdapter.endMeasure F ζ hζ C R P H U a).restrict {p | A < p.2}) := by
        have hh := ((hbound a s hs).1.aestronglyMeasurable.mono_measure
          (Measure.restrict_mono (fun p hp => lt_of_le_of_lt h0A hp) le_rfl)).aemeasurable
        exact (hh.pow_const 2).ennreal_ofReal
      rw [lintegral_add_left' (hmnorm.const_mul 2), lintegral_const_mul' _ _ (by norm_num),
        lintegral_const_mul' _ _ (by norm_num)]
      exact le_rfl
    _ ≤ 2 * ENNReal.ofReal c + 2 * ENNReal.ofReal b := add_le_add (mul_le_mul_right hout _) (mul_le_mul_right hmean _)
    _ = ENNReal.ofReal (2*c+2*b) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num)]; norm_num

private theorem lineG_global_square_bound (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L,
    (∫⁻ x, KPContSectorLineL2Isometry.squaredNorm F ζ hζ
      (level F ζ hζ C R P H U) R P H
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
      ∂baseMeasure F ζ hζ C R P H U) ≤ ENNReal.ofReal B := by
  obtain ⟨A,E,hA,hE,hend⟩ := lineG_high_end_square_bound F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV k
  let K := (tail F ζ hζ C R P H U A)ᶜ
  have hK : IsCompact K := by
    convert KPContThreeL2EndHelpers.compact_truncated_core F ζ hζ
      (level F ζ hζ C R P H U) R P H A using 1
    ext x
    simp only [K,tail,KPCuspCutoffGraph.highEnds,KPContActualCollarBuffer.endSet,
      Set.mem_compl_iff,Set.mem_iUnion]
    exact not_congr ⟨fun ⟨i,c,h⟩ => ⟨⟨i,c⟩,h⟩,fun ⟨⟨i,c⟩,h⟩ => ⟨i,c,h⟩⟩
  obtain ⟨B,hB,hcore⟩ := lineGH_compact_square_bound F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV K hK k
  let N := Fintype.card (KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
  refine ⟨B + N*E, by positivity, ?_⟩
  intro s hs
  have ht : tail F ζ hζ C R P H U A =
      ⋃ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U,
        KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A a := by
    ext x
    simp only [tail,KPCuspCutoffGraph.highEnds,KPContActualCollarBuffer.endSet,Set.mem_iUnion]
    exact ⟨fun ⟨i,c,h⟩ => ⟨⟨i,c⟩,h⟩,fun ⟨⟨i,c⟩,h⟩ => ⟨i,c,h⟩⟩
  have htail : (∫⁻ x in tail F ζ hζ C R P H U A,
      KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H
        (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
      ∂baseMeasure F ζ hζ C R P H U) ≤ ENNReal.ofReal (N*E) := by
    rw [ht]
    apply (lintegral_iUnion_le _ _).trans
    rw [tsum_fintype]
    calc
      _ ≤ ∑ _a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U, ENNReal.ofReal E :=
        Finset.sum_le_sum (fun a _ => hend a s hs)
      _ = ENNReal.ofReal (N*E) := by
        rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity)]
        rw [ENNReal.ofReal_natCast]
  calc
    _ = (∫⁻ x in K, KPContSectorLineL2Isometry.squaredNorm F ζ hζ
        (level F ζ hζ C R P H U) R P H
        (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
        ∂baseMeasure F ζ hζ C R P H U) +
        (∫⁻ x in tail F ζ hζ C R P H U A, KPContSectorLineL2Isometry.squaredNorm F ζ hζ
        (level F ζ hζ C R P H U) R P H
        (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
        ∂baseMeasure F ζ hζ C R P H U) := by
      simpa [K] using (lintegral_add_compl _ hK.measurableSet).symm
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal (N*E) := add_le_add (hcore s hs).1 htail
    _ = ENNReal.ofReal (B+N*E) := (ENNReal.ofReal_add hB (by positivity)).symm

private theorem lineH_global_square_bound (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L,
    (∫⁻ x, KPContSectorLineL2Isometry.squaredNorm F ζ hζ
      (level F ζ hζ C R P H U) R P H
      (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
      ∂baseMeasure F ζ hζ C R P H U) ≤ ENNReal.ofReal B := by
  let K := KPContActualAllCuspSource.K F ζ hζ C R P H U buffer
  obtain ⟨B,hB,hbound⟩ := lineGH_compact_square_bound F ζ hζ C R P H U ι f buffer χ source hι hf
    L hL hLV K source.compact_collars k
  refine ⟨B,hB,?_⟩
  intro s hs
  have hz : ∀ x ∈ Kᶜ, KPContSectorLineL2Isometry.squaredNorm F ζ hζ
      (level F ζ hζ C R P H U) R P H
      (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s) x = 0 := by
    intro x hx
    have hn : x ∉ tsupport (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ
        (level F ζ hζ C R P H U) R P H
        (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)) :=
      fun h => hx (lineH_support F ζ hζ C R P H U ι f buffer χ source hι hf k s h)
    simp [KPContSectorLineL2Isometry.squaredNorm,image_eq_zero_of_notMem_tsupport hn]
  have hi : (∫⁻ x in Kᶜ, KPContSectorLineL2Isometry.squaredNorm F ζ hζ
      (level F ζ hζ C R P H U) R P H
      (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
      ∂baseMeasure F ζ hζ C R P H U) = 0 := by
    rw [← lintegral_zero (μ := (baseMeasure F ζ hζ C R P H U).restrict Kᶜ)]
    exact setLIntegral_congr_fun source.compact_collars.measurableSet.compl hz
  rw [← lintegral_add_compl _ source.compact_collars.measurableSet,hi,add_zero]
  exact (hbound s hs).2

theorem lineG_borelL2 (k : ℕ) (s : ℂ) :
    lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈
      BorelL2Sections F ζ hζ C R P H U := by
  by_cases hs : s ∈ V
  · obtain ⟨A,B,hA,hB,hbound⟩ := lineG_high_end_square_bound
      F ζ hζ C R P H U ι f buffer χ source hι hf {s} isCompact_singleton
      (Set.singleton_subset_iff.mpr hs) k
    let E : Set (Base F ζ hζ C R P H U) := ⋃ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U,
      KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A a
    have hE : MeasurableSet E := (isOpen_iUnion (fun a => KPContThreeL2EndHelpers.all_ends_open
      F ζ hζ (level F ζ hζ C R P H U) R P H A a)).measurableSet
    have hEc : IsCompact Eᶜ := KPContThreeL2EndHelpers.compact_truncated_core
      F ζ hζ (level F ζ hζ C R P H U) R P H A
    refine ⟨fun i => ((smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1 i).continuous.measurable, ?_⟩
    unfold KPContSectorLineL2Isometry.normIntegral
    rw [← lintegral_add_compl _ hE]
    apply ENNReal.add_lt_top.mpr
    refine ⟨?_, lineG_compact_square_finite F ζ hζ C R P H U ι f buffer χ source hι hf k s Eᶜ hEc⟩
    apply lt_of_le_of_lt (lintegral_iUnion_le _ _)
    rw [tsum_fintype]
    apply ENNReal.sum_lt_top.mpr
    intro a ha
    exact (hbound a s (Set.mem_singleton s)).trans_lt ENNReal.ofReal_lt_top
  · have he : lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s = 0 := by
      simp [lineG, coveredG, hs]
    rw [he]
    exact (BorelL2Sections F ζ hζ C R P H U).zero_mem

include hι hf in

theorem g_memLp (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    MemLp (g F ζ hζ C R P H U ι f buffer χ source k s) 2 (measure F ζ hζ C R P H U) := by
  have hm := lineG_borelL2 F ζ hζ C R P H U ι f buffer χ source hι hf k s
  have he : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ (level F ζ hζ C R P H U)
      R P H (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)).val =
      g F ζ hζ C R P H U ι f buffer χ source k s := by
    rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
    unfold lineG
    rw [LinearEquiv.symm_apply_apply]
    simp [coveredG, hs]
  rw [← he]
  exact (KPContSectorLineL2Isometry.finite_integral_iff F ζ hζ
    (level F ζ hζ C R P H U) R P H _ hm.1).mp hm.2

include hι hf in

theorem h_memLp (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    MemLp (h F ζ hζ C R P H U ι f buffer χ source k s) 2 (measure F ζ hζ C R P H U) := by
  have hm := lineH_borelL2 F ζ hζ C R P H U ι f buffer χ source hι hf k s
  have he : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ (level F ζ hζ C R P H U)
      R P H (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)).val =
      h F ζ hζ C R P H U ι f buffer χ source k s := by
    rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
    unfold lineH
    rw [LinearEquiv.symm_apply_apply]
    simp [coveredH, hs]
  rw [← he]
  exact (KPContSectorLineL2Isometry.finite_integral_iff F ζ hζ
    (level F ζ hζ C R P H U) R P H _ hm.1).mp hm.2

theorem lineG_end_uniform_tails (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) : ∃ A : ℝ,
    (H.atlas (level F ζ hζ C R P H U)).threshold < A ∧
    ∀ A' : ℝ, A ≤ A' →
    ∀ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U, ∀ s ∈ L,
    (∫⁻ x in KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A' a,
      KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H
        (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
      ∂baseMeasure F ζ hζ C R P H U) ≤ ENNReal.ofReal ε := by
  have hm := DedekindZetaZeroFree.kp_cont_actual_chamber_mean_zero_adapter F ζ hζ C R P H U
    (DedekindZetaZeroFree.actual_levelRealization_of_recipe
      F ζ hζ (level F ζ hζ C R P H U) R P H) ι hι f hf buffer χ source
  obtain ⟨t₁,b,h10,h1atlas,h1b,h1T,hb0,hmbound,hmtail⟩ := hm.weighted_tails L hL hLV k 1 (by norm_num)
  have hlim : Filter.Tendsto (fun t : ℝ => b * Real.exp (-2*t)) Filter.atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    simpa [mul_neg] using hh.const_mul b
  obtain ⟨t₂,ht₂⟩ := Filter.eventually_atTop.mp (hlim.eventually_le_const (by linarith : (0 : ℝ) < ε/4))
  obtain ⟨A,hA,hout⟩ := KPContActualChamberOutgoingAdapter.squareTail_uniform_vanishing
    F ζ hζ C R P H U ι buffer f χ source hι hf L hL hLV k 0 (max t₁ t₂) (ε/4) (by linarith)
  have h1A : t₁ ≤ A := (le_max_left _ _).trans hA
  have h2A : t₂ ≤ A := (le_max_right _ _).trans hA
  refine ⟨A,h1atlas.trans_le h1A,?_⟩
  intro A' hA' a s hs
  have hT' : T + 1 < A' := h1T.trans_le (h1A.trans hA')
  have hb' : buffer.τ < A' := h1b.trans_le (h1A.trans hA')
  have hmeas := ((KPContActualChamberOutgoingAdapter.jetNorm_high_aestronglyMeasurable
    F ζ hζ C R P H U a ι buffer f χ source hι hf k 0 s (hLV hs) A' hT' hb').aemeasurable.pow_const 2).ennreal_ofReal
  have he := (hmtail A' (h1A.trans hA') a s hs).2.1
  have he' : KPContActualChamberMeanZeroAdapter.energy F ζ hζ C R P H U a ι f k s 0 A' ≤ ENNReal.ofReal (ε/4) := by
    apply he.trans
    apply ENNReal.ofReal_le_ofReal
    simpa using ht₂ A' (h2A.trans hA')
  apply (lineG_end_square_le F ζ hζ C R P H U ι f buffer χ source hι hf k s (hLV hs)
    a A' (h1atlas.trans_le (h1A.trans hA')) hT'.le hb' hmeas).trans
  calc
    _ ≤ 2 * ENNReal.ofReal (ε/4) + 2 * ENNReal.ofReal (ε/4) :=
      add_le_add (mul_le_mul_right (hout A' hA' a s hs) _) (mul_le_mul_right he' _)
    _ = ENNReal.ofReal ε := by
      have h : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
      rw [h, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

theorem gradient_end_uniform_tails (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) : ∃ A : ℝ,
    (H.atlas (level F ζ hζ C R P H U)).threshold < A ∧
    ∀ A' : ℝ, A ≤ A' →
    ∀ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U, ∀ s ∈ L,
    (∫⁻ x in KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A' a,
      (KPContActualCotangentMeasurableFamilies.normSquare
        (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) x : ℝ≥0∞)
      ∂baseMeasure F ζ hζ C R P H U) ≤ ENNReal.ofReal ε := by
  have hm := DedekindZetaZeroFree.kp_cont_actual_chamber_mean_zero_adapter F ζ hζ C R P H U
    (DedekindZetaZeroFree.actual_levelRealization_of_recipe
      F ζ hζ (level F ζ hζ C R P H U) R P H) ι hι f hf buffer χ source
  obtain ⟨t₁,b,h10,h1atlas,h1b,h1T,hb0,hmbound,hmtail⟩ := hm.weighted_tails L hL hLV k 1 (by norm_num)
  have hlim : Filter.Tendsto (fun t : ℝ => b * Real.exp (-2*t)) Filter.atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    simpa [mul_neg] using hh.const_mul b
  obtain ⟨t₂,ht₂⟩ := Filter.eventually_atTop.mp (hlim.eventually_le_const (by linarith : (0 : ℝ) < ε/4))
  obtain ⟨A,hA,hout⟩ := KPContActualChamberOutgoingAdapter.squareTail_uniform_vanishing
    F ζ hζ C R P H U ι buffer f χ source hι hf L hL hLV k 1 (max t₁ t₂) (ε/4) (by linarith)
  have h1A : t₁ ≤ A := (le_max_left _ _).trans hA
  have h2A : t₂ ≤ A := (le_max_right _ _).trans hA
  refine ⟨A,h1atlas.trans_le h1A,?_⟩
  intro A' hA' a s hs
  have hT' : T + 1 < A' := h1T.trans_le (h1A.trans hA')
  have hb' : buffer.τ < A' := h1b.trans_le (h1A.trans hA')
  have hmeas := ((KPContActualChamberOutgoingAdapter.jetNorm_high_aestronglyMeasurable
    F ζ hζ C R P H U a ι buffer f χ source hι hf k 1 s (hLV hs) A' hT' hb').aemeasurable.pow_const 2).ennreal_ofReal
  have he := (hmtail A' (h1A.trans hA') a s hs).2.1
  have he' : KPContActualChamberMeanZeroAdapter.energy F ζ hζ C R P H U a ι f k s 0 A' ≤ ENNReal.ofReal (ε/4) := by
    apply he.trans
    apply ENNReal.ofReal_le_ofReal
    simpa using ht₂ A' (h2A.trans hA')
  apply (gradient_end_square_le F ζ hζ C R P H U ι f buffer χ source hι hf k s (hLV hs)
    a A' (h1atlas.trans_le (h1A.trans hA')) hT'.le hb' hmeas).trans
  calc
    _ ≤ 2 * ENNReal.ofReal (ε/4) + 2 * ENNReal.ofReal (ε/4) :=
      add_le_add (mul_le_mul_right (hout A' hA' a s hs) _) (mul_le_mul_right he' _)
    _ = ENNReal.ofReal ε := by
      have h : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
      rw [h, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

theorem gradient_norm_continuous (k : ℕ) (s : ℂ) :
    Continuous (fun x => (KPContActualCotangentMeasurableFamilies.normSquare
      (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) x : ℝ)) := by
  exact KPContThreeL2CotangentHelpers.smoothGradient_norm_continuous
    (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)
    (smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1

theorem gradient_compact_square_finite (k : ℕ) (s : ℂ)
    (K : Set (Base F ζ hζ C R P H U)) (hK : IsCompact K) :
    (∫⁻ x in K, (KPContActualCotangentMeasurableFamilies.normSquare
      (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) x : ℝ≥0∞)
      ∂baseMeasure F ζ hζ C R P H U) < ⊤ := by
  letI := KPContSectorFixedMeasureLocalFiniteness.sphericalMeasure_finiteOnCompacts
    F ζ hζ R P (level F ζ hζ C R P H U)
  have hi := (gradient_norm_continuous F ζ hζ C R P H U ι f buffer χ source hι hf k s).continuousOn.integrableOn_compact
    (μ := baseMeasure F ζ hζ C R P H U) hK
  simpa only [ENNReal.ofReal_coe_nnreal] using
    (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun x => NNReal.coe_nonneg _))).mp hi.hasFiniteIntegral

theorem gradient_norm_zero (k : ℕ) (s : ℂ) (hs : s ∉ V) :
    KPContActualCotangentMeasurableFamilies.normSquare
      (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) = 0 := by
  funext x
  obtain ⟨⟨i,y⟩,rfl⟩ := (H.atlas (level F ζ hζ C R P H U)).components.surjective x
  induction y using Quotient.inductionOn with | h y =>
    have he : lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s = 0 := by
      simp [lineG, coveredG, hs]
    have hh := KPContThreeL2CotangentHelpers.smoothGradient_at_arch
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)
      (smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1 i y
    change KPContActualCotangentMeasurableFamilies.normSquare
      (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s)
      ((H.atlas (level F ζ hζ C R P H U)).components ⟨i, Quotient.mk _ y⟩) = 0
    apply NNReal.coe_injective
    change (_ : ℝ) = 0
    change (KPContActualCotangentMeasurableFamilies.normSquare
      (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s)
      ((H.atlas (level F ζ hζ C R P H U)).components ⟨i, Quotient.mk _ y⟩) : ℝ) = _ at hh
    rw [hh, he]
    simp [HyperbolicChart.differential, HyperbolicChart.coordinateDerivative, Fin.sum_univ_succ]

theorem gradient_squareFinite (k : ℕ) (s : ℂ) :
    KPContActualCotangentMeasurableFamilies.squareFinite (R := R) (P := P)
      (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) := by
  by_cases hs : s ∈ V
  · obtain ⟨A,B,hA,hB,hbound⟩ := gradient_high_end_square_bound
      F ζ hζ C R P H U ι f buffer χ source hι hf {s} isCompact_singleton
      (Set.singleton_subset_iff.mpr hs) k
    let E : Set (Base F ζ hζ C R P H U) := ⋃ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U,
      KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A a
    have hE : MeasurableSet E := (isOpen_iUnion (fun a => KPContThreeL2EndHelpers.all_ends_open
      F ζ hζ (level F ζ hζ C R P H U) R P H A a)).measurableSet
    have hEc : IsCompact Eᶜ := KPContThreeL2EndHelpers.compact_truncated_core
      F ζ hζ (level F ζ hζ C R P H U) R P H A
    unfold KPContActualCotangentMeasurableFamilies.squareFinite
    simp only [ENNReal.ofReal_coe_nnreal]
    change (∫⁻ x, (KPContActualCotangentMeasurableFamilies.normSquare
      (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) x : ℝ≥0∞)
      ∂baseMeasure F ζ hζ C R P H U) < ⊤
    rw [← lintegral_add_compl _ hE]
    apply ENNReal.add_lt_top.mpr
    refine ⟨?_, gradient_compact_square_finite F ζ hζ C R P H U ι f buffer χ source hι hf k s Eᶜ hEc⟩
    apply lt_of_le_of_lt (lintegral_iUnion_le _ _)
    rw [tsum_fintype]
    apply ENNReal.sum_lt_top.mpr
    intro a ha
    exact (hbound a s (Set.mem_singleton s)).trans_lt ENNReal.ofReal_lt_top
  · unfold KPContActualCotangentMeasurableFamilies.squareFinite
    rw [gradient_norm_zero F ζ hζ C R P H U ι f buffer χ source hι hf k s hs]
    simp

theorem lineDelta_zero (k : ℕ) (s : ℂ) (hs : s ∉ V) :
    lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s = 0 := by
  have he : lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s = 0 := by
    simp [lineG, coveredG, hs]
  funext i
  apply Subtype.ext
  funext y
  change HyperbolicChart.laplacian (KPCuspLogShape.dimension F)
    ((lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s i).val ∘
      KPCuspCutoffGraph.toArch F) (KPCuspCutoffGraph.fromArch F y) = 0
  rw [he]
  have hd : ∀ j l, HyperbolicChart.coordinateDerivative
      (KPCuspLogShape.dimension F) j l (fun _ => (0 : ℂ)) = 0 := by
    intro j l
    funext x
    simp [HyperbolicChart.coordinateDerivative]
  simp [HyperbolicChart.laplacian, Function.comp_def, hd,
    HyperbolicChart.coordinateDerivative]

theorem lineDelta_borelL2_outside (k : ℕ) (s : ℂ) (hs : s ∉ V) :
    lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈
      BorelL2Sections F ζ hζ C R P H U := by
  rw [lineDelta_zero F ζ hζ C R P H U ι f buffer χ source hι hf k s hs]
  exact (BorelL2Sections F ζ hζ C R P H U).zero_mem

theorem lineDelta_eq_rhs (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      KPContActualChamberCasimirJets.lambda F s • lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s -
      lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s +
      ∑ j ∈ Finset.Icc 1 (min k 2),
        ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) •
          lineG F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s := by
  funext i
  apply Subtype.ext
  funext y
  let O := (KPContSectorPhaseComponentCharts.orbifoldChart_exists F ζ hζ
    (level F ζ hζ C R P H U) R P H i y).some
  let a : Frame F ζ hζ C R P H U i := {
    kind := .orbifold y O
    places := KPContCotangentActualOverlap.placeEquiv F ζ hζ
    splitting := fun _ => 1
    splitting_locallyConstant := IsLocallyConstant.const 1 }
  let x := KPContCotangentActualOverlap.labeledAInv a.places y
  have hxy : KPContCotangentActualOverlap.labeledA a.places x = y := by
    funext j
    simp [x, KPContCotangentActualOverlap.labeledAInv,
      KPContCotangentActualOverlap.labeledA]
  have hx : x ∈ a.omega := by
    change KPContCotangentActualOverlap.labeledA a.places x ∈ O.neighborhood
    rw [hxy]
    exact O.center_mem
  have hc (w : Sections F ζ hζ C R P H U) : a.coefficient w x = (w i).val y := by
    simp [KPContCotangentActualOverlap.LiftedChart.coefficient, a,
      KPContCotangentActualOverlap.ChartKind.representative, hxy]
  have he := defect_frame_equation F ζ hζ C R P H U ι f buffer χ source hι hf k s hs i a x hx
  rw [← lineDelta_frame F ζ hζ C R P H U ι f buffer χ source hι hf k s i a x hx] at he
  simp only [hc] at he
  simpa only [Pi.add_apply, Pi.sub_apply, Submodule.coe_add,
    Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_sum,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc] using he

private theorem laplacian_l2_from_rhs (k : ℕ) (s : ℂ)
    (he : lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      KPContActualChamberCasimirJets.lambda F s • lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s -
      lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s +
      ∑ j ∈ Finset.Icc 1 (min k 2),
        ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) •
          lineG F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s) :
    lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈ BorelL2Sections F ζ hζ C R P H U := by
  rw [he]
  apply Submodule.add_mem
  · exact Submodule.sub_mem _ (Submodule.smul_mem _ _
      (lineG_borelL2 F ζ hζ C R P H U ι f buffer χ source hι hf k s))
      (lineH_borelL2 F ζ hζ C R P H U ι f buffer χ source hι hf k s)
  · exact Submodule.sum_mem _ (fun j hj => Submodule.smul_mem _ _
      (lineG_borelL2 F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s))

theorem integrability (k : ℕ) (s : ℂ) :
    lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈ BorelL2Sections F ζ hζ C R P H U ∧
    lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈ BorelL2Sections F ζ hζ C R P H U ∧
    lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈ BorelL2Sections F ζ hζ C R P H U ∧
    KPContActualCotangentMeasurableFamilies.squareFinite (R := R) (P := P)
      (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) := by
  refine ⟨lineG_borelL2 F ζ hζ C R P H U ι f buffer χ source hι hf k s,
    lineH_borelL2 F ζ hζ C R P H U ι f buffer χ source hι hf k s, ?_,
    gradient_squareFinite F ζ hζ C R P H U ι f buffer χ source hι hf k s⟩
  by_cases hs : s ∈ V
  · exact laplacian_l2_from_rhs F ζ hζ C R P H U ι f buffer χ source hι hf k s
      (lineDelta_eq_rhs F ζ hζ C R P H U ι f buffer χ source hι hf k s hs)
  · exact lineDelta_borelL2_outside F ζ hζ C R P H U ι f buffer χ source hι hf k s hs

def borelG (k : ℕ) (s : ℂ) : BorelL2Sections F ζ hζ C R P H U :=
  ⟨_, (integrability F ζ hζ C R P H U ι f buffer χ source hι hf k s).1⟩

def borelH (k : ℕ) (s : ℂ) : BorelL2Sections F ζ hζ C R P H U :=
  ⟨_, (integrability F ζ hζ C R P H U ι f buffer χ source hι hf k s).2.1⟩

def borelDelta (k : ℕ) (s : ℂ) : BorelL2Sections F ζ hζ C R P H U :=
  ⟨_, (integrability F ζ hζ C R P H U ι f buffer χ source hι hf k s).2.2.1⟩

def UJet (k : ℕ) (s : ℂ) : Sector F ζ hζ C R P H U :=
  KPContSectorLineL2Isometry.toSector F ζ hζ (level F ζ hζ C R P H U) R P H
    (borelG F ζ hζ C R P H U ι f buffer χ source hι hf k s)

def HJet (k : ℕ) (s : ℂ) : Sector F ζ hζ C R P H U :=
  KPContSectorLineL2Isometry.toSector F ζ hζ (level F ζ hζ C R P H U) R P H
    (borelH F ζ hζ C R P H U ι f buffer χ source hι hf k s)

def DeltaJet (k : ℕ) (s : ℂ) : Sector F ζ hζ C R P H U :=
  KPContSectorLineL2Isometry.toSector F ζ hζ (level F ζ hζ C R P H U) R P H
    (borelDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s)

private theorem differential_class_from_rhs (k : ℕ) (s : ℂ)
    (he : lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      KPContActualChamberCasimirJets.lambda F s • lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s -
      lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s +
      ∑ j ∈ Finset.Icc 1 (min k 2),
        ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) •
          lineG F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s) :
    DeltaJet F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      KPContActualChamberCasimirJets.lambda F s • UJet F ζ hζ C R P H U ι f buffer χ source hι hf k s -
      HJet F ζ hζ C R P H U ι f buffer χ source hι hf k s +
      ∑ j ∈ Finset.Icc 1 (min k 2),
        ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) •
          UJet F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s := by
  unfold DeltaJet UJet HJet
  simp_rw [← map_smul]
  rw [← map_sub, ← map_sum, ← map_add]
  congr 1
  apply Subtype.ext
  simpa only [borelDelta, borelG, borelH, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_smul, Submodule.coe_sum] using he

theorem differential_rhs_class (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    DeltaJet F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      KPContActualChamberCasimirJets.lambda F s • UJet F ζ hζ C R P H U ι f buffer χ source hι hf k s -
      HJet F ζ hζ C R P H U ι f buffer χ source hι hf k s +
      ∑ j ∈ Finset.Icc 1 (min k 2),
        ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) •
          UJet F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s := by
  exact differential_class_from_rhs F ζ hζ C R P H U ι f buffer χ source hι hf k s
    (lineDelta_eq_rhs F ζ hζ C R P H U ι f buffer χ source hι hf k s hs)

theorem jets_actual_ae (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    ((UJet F ζ hζ C R P H U ι f buffer χ source hι hf k s).val : Covered F ζ hζ C R P H U → ℂ)
      =ᵐ[measure F ζ hζ C R P H U] g F ζ hζ C R P H U ι f buffer χ source k s ∧
    ((HJet F ζ hζ C R P H U ι f buffer χ source hι hf k s).val : Covered F ζ hζ C R P H U → ℂ)
      =ᵐ[measure F ζ hζ C R P H U] h F ζ hζ C R P H U ι f buffer χ source k s ∧
    ((DeltaJet F ζ hζ C R P H U ι f buffer χ source hι hf k s).val : Covered F ζ hζ C R P H U → ℂ)
      =ᵐ[measure F ζ hζ C R P H U]
        (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ
          (level F ζ hζ C R P H U) R P H
          (lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s)).val := by
  have hg := MemLp.coeFn_toLp (KPContSectorLineL2Isometry.representative_memLp F ζ hζ
    (level F ζ hζ C R P H U) R P H (borelG F ζ hζ C R P H U ι f buffer χ source hι hf k s))
  have hh := MemLp.coeFn_toLp (KPContSectorLineL2Isometry.representative_memLp F ζ hζ
    (level F ζ hζ C R P H U) R P H (borelH F ζ hζ C R P H U ι f buffer χ source hι hf k s))
  have hd := MemLp.coeFn_toLp (KPContSectorLineL2Isometry.representative_memLp F ζ hζ
    (level F ζ hζ C R P H U) R P H (borelDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s))
  refine ⟨?_,?_,hd⟩
  · exact hg.trans (Filter.Eventually.of_forall (fun x => by
      simp [borelG, lineG, coveredG, hs,
        KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]))
  · exact hh.trans (Filter.Eventually.of_forall (fun x => by
      simp [borelH, lineH, coveredH, hs,
        KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]))

def squaredDensity (j : Fin 3) (k : ℕ) (s : ℂ) : Base F ζ hζ C R P H U → ℝ≥0∞ :=
  if j = 0 then KPContSectorLineL2Isometry.squaredNorm F ζ hζ
    (level F ζ hζ C R P H U) R P H (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)
  else if j = 1 then fun x => (KPContActualCotangentMeasurableFamilies.normSquare
    (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) x : ℝ≥0∞)
  else KPContSectorLineL2Isometry.squaredNorm F ζ hζ
    (level F ζ hζ C R P H U) R P H (lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s)

def squareIntegral (j : Fin 3) (k : ℕ) (s : ℂ) : ℝ≥0∞ :=
  ∫⁻ x, squaredDensity F ζ hζ C R P H U ι f buffer χ source hι hf j k s x
    ∂baseMeasure F ζ hζ C R P H U

def squareTail (j : Fin 3) (k : ℕ) (s : ℂ) (A : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in tail F ζ hζ C R P H U A,
    squaredDensity F ζ hζ C R P H U ι f buffer χ source hι hf j k s x
    ∂baseMeasure F ζ hζ C R P H U

theorem value_uniform_tails (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V) (k : ℕ)
    (ε : ℝ) (hε : 0 < ε) : ∃ A : ℝ,
    (H.atlas (level F ζ hζ C R P H U)).threshold < A ∧
    ∀ A' : ℝ, A ≤ A' → ∀ s ∈ L,
    squareTail F ζ hζ C R P H U ι f buffer χ source hι hf 0 k s A' ≤ ENNReal.ofReal ε := by
  let N : ℕ := Fintype.card (KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
  have hN : (0 : ℝ) < (N : ℝ)+1 := by positivity
  obtain ⟨A,hA,hbound⟩ := lineG_end_uniform_tails F ζ hζ C R P H U ι f buffer χ source hι hf
    L hL hLV k (ε/((N:ℝ)+1)) (div_pos hε hN)
  refine ⟨A,hA,?_⟩
  intro A' hA' s hs
  have htail : tail F ζ hζ C R P H U A' =
      ⋃ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U,
        KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A' a := by
    ext x
    simp only [tail, KPCuspCutoffGraph.highEnds, KPContActualCollarBuffer.endSet, Set.mem_iUnion]
    exact ⟨fun ⟨i,c,h⟩ => ⟨⟨i,c⟩,h⟩, fun ⟨⟨i,c⟩,h⟩ => ⟨i,c,h⟩⟩
  unfold squareTail
  simp only [squaredDensity, ite_true]
  rw [htail]
  apply (lintegral_iUnion_le _ _).trans
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U,
        ENNReal.ofReal (ε/((N:ℝ)+1)) := Finset.sum_le_sum (fun a ha => hbound A' hA' a s hs)
    _ = ENNReal.ofReal ((N:ℝ) * (ε/((N:ℝ)+1))) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change (N : ℝ≥0∞) * ENNReal.ofReal (ε/((N:ℝ)+1)) = _
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by
      have hh : (N:ℝ) / ((N:ℝ)+1) ≤ 1 := (div_le_one hN).mpr (by linarith)
      have hh' := mul_le_mul_of_nonneg_right hh hε.le
      convert hh' using 1 <;> ring)

theorem gradient_uniform_tails (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V) (k : ℕ)
    (ε : ℝ) (hε : 0 < ε) : ∃ A : ℝ,
    (H.atlas (level F ζ hζ C R P H U)).threshold < A ∧
    ∀ A' : ℝ, A ≤ A' → ∀ s ∈ L,
    squareTail F ζ hζ C R P H U ι f buffer χ source hι hf 1 k s A' ≤ ENNReal.ofReal ε := by
  let N : ℕ := Fintype.card (KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
  have hN : (0 : ℝ) < (N : ℝ)+1 := by positivity
  obtain ⟨A,hA,hbound⟩ := gradient_end_uniform_tails F ζ hζ C R P H U ι f buffer χ source hι hf
    L hL hLV k (ε/((N:ℝ)+1)) (div_pos hε hN)
  refine ⟨A,hA,?_⟩
  intro A' hA' s hs
  have htail : tail F ζ hζ C R P H U A' =
      ⋃ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U,
        KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A' a := by
    ext x
    simp only [tail, KPCuspCutoffGraph.highEnds, KPContActualCollarBuffer.endSet, Set.mem_iUnion]
    exact ⟨fun ⟨i,c,h⟩ => ⟨⟨i,c⟩,h⟩, fun ⟨⟨i,c⟩,h⟩ => ⟨i,c,h⟩⟩
  unfold squareTail
  simp only [squaredDensity, show (1 : Fin 3) ≠ 0 by decide, ite_false, ite_true]
  rw [htail]
  apply (lintegral_iUnion_le _ _).trans
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U,
        ENNReal.ofReal (ε/((N:ℝ)+1)) := Finset.sum_le_sum (fun a ha => hbound A' hA' a s hs)
    _ = ENNReal.ofReal ((N:ℝ) * (ε/((N:ℝ)+1))) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change (N : ℝ≥0∞) * ENNReal.ofReal (ε/((N:ℝ)+1)) = _
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by
      have hh : (N:ℝ) / ((N:ℝ)+1) ≤ 1 := (div_le_one hN).mpr (by linarith)
      have hh' := mul_le_mul_of_nonneg_right hh hε.le
      convert hh' using 1 <;> ring)

private theorem tailworker_squared_add (u v : Sections F ζ hζ C R P H U)
    (x : Base F ζ hζ C R P H U) :
    KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H (u+v) x ≤
      2 * KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H u x +
      2 * KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H v x := by
  obtain ⟨⟨i,y⟩,rfl⟩ := (H.atlas (level F ζ hζ C R P H U)).components.surjective x
  refine Quotient.inductionOn y ?_
  intro y
  simp only [KPContSectorLineL2Isometry.squaredNorm,
    KPContSectorSmoothFramesSupport.sectionNorm_component, Submodule.coe_add, Pi.add_apply]
  calc
    ENNReal.ofReal (‖(u i).val y + (v i).val y‖ ^ 2) ≤
      ENNReal.ofReal (2 * ‖(u i).val y‖ ^ 2 + 2 * ‖(v i).val y‖ ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans (by nlinarith [sq_nonneg (‖(u i).val y‖ - ‖(v i).val y‖)])
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num

private theorem tailworker_squared_smul (c : ℂ) (u : Sections F ζ hζ C R P H U)
    (x : Base F ζ hζ C R P H U) :
    KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H (c • u) x =
      ENNReal.ofReal (‖c‖^2) * KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H u x := by
  obtain ⟨⟨i,y⟩,rfl⟩ := (H.atlas (level F ζ hζ C R P H U)).components.surjective x
  refine Quotient.inductionOn y ?_
  intro y
  simp only [KPContSectorLineL2Isometry.squaredNorm,
    KPContSectorSmoothFramesSupport.sectionNorm_component, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]

 def tailworker_energy (u : Sections F ζ hζ C R P H U) (A : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in tail F ζ hζ C R P H U A,
    KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H u x
    ∂baseMeasure F ζ hζ C R P H U

 def tailworker_decay (L : Set ℂ) (u : ℂ → Sections F ζ hζ C R P H U) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, (H.atlas (level F ζ hζ C R P H U)).threshold < A ∧
    ∀ A', A ≤ A' → ∀ s ∈ L, tailworker_energy F ζ hζ C R P H U (u s) A' ≤ ENNReal.ofReal ε

private theorem tailworker_energy_add (u v : Sections F ζ hζ C R P H U)
    (hu : ∀ i, Measurable (u i).val) (A : ℝ) :
    tailworker_energy F ζ hζ C R P H U (u+v) A ≤
      2 * tailworker_energy F ζ hζ C R P H U u A + 2 * tailworker_energy F ζ hζ C R P H U v A := by
  unfold tailworker_energy
  apply (lintegral_mono (tailworker_squared_add F ζ hζ C R P H U u v)).trans
  rw [lintegral_add_left ((KPContSectorLineL2Isometry.squaredNorm_measurable F ζ hζ
      (level F ζ hζ C R P H U) R P H u hu).const_mul 2),
    lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]

private theorem tailworker_decay_add (L : Set ℂ) (u v : ℂ → Sections F ζ hζ C R P H U)
    (hu : ∀ s ∈ L, ∀ i, Measurable (u s i).val)
    (hdu : tailworker_decay F ζ hζ C R P H U L u)
    (hdv : tailworker_decay F ζ hζ C R P H U L v) :
    tailworker_decay F ζ hζ C R P H U L (fun s => u s + v s) := by
  intro ε hε
  obtain ⟨A,hA,hbound⟩ := hdu (ε/4) (by positivity)
  obtain ⟨B,hB,hbound'⟩ := hdv (ε/4) (by positivity)
  refine ⟨max A B, lt_of_lt_of_le hA (le_max_left _ _), ?_⟩
  intro A' hA' s hs
  calc
    _ ≤ 2 * tailworker_energy F ζ hζ C R P H U (u s) A' +
        2 * tailworker_energy F ζ hζ C R P H U (v s) A' := tailworker_energy_add F ζ hζ C R P H U _ _ (hu s hs) A'
    _ ≤ 2 * ENNReal.ofReal (ε/4) + 2 * ENNReal.ofReal (ε/4) :=
      add_le_add (mul_le_mul_right (hbound A' ((le_max_left _ _).trans hA') s hs) _)
        (mul_le_mul_right (hbound' A' ((le_max_right _ _).trans hA') s hs) _)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

private theorem tailworker_decay_smul (L : Set ℂ) (u : ℂ → Sections F ζ hζ C R P H U)
    (c : ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hc : ∀ s ∈ L, ‖c s‖ ≤ B)
    (hdu : tailworker_decay F ζ hζ C R P H U L u) :
    tailworker_decay F ζ hζ C R P H U L (fun s => c s • u s) := by
  intro ε hε
  obtain ⟨A,hA,hbound⟩ := hdu (ε/(B^2+1)) (by positivity)
  refine ⟨A,hA,?_⟩
  intro A' hA' s hs
  unfold tailworker_energy
  simp_rw [tailworker_squared_smul F ζ hζ C R P H U]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ENNReal.ofReal (B^2) * ENNReal.ofReal (ε/(B^2+1)) :=
      mul_le_mul (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hc s hs) 2))
        (hbound A' hA' s hs) (by positivity) (by positivity)
    _ ≤ ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have hh : B^2 / (B^2+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      have := mul_le_mul_of_nonneg_right hh hε.le
      convert this using 1 <;> ring

private theorem tailworker_decay_zero (L : Set ℂ) :
    tailworker_decay F ζ hζ C R P H U L (fun _ => 0) := by
  intro ε hε
  refine ⟨(H.atlas (level F ζ hζ C R P H U)).threshold+1, by linarith, ?_⟩
  intro A' hA' s hs
  unfold tailworker_energy
  have hz : KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H
      (0 : Sections F ζ hζ C R P H U) = 0 := by
    funext x
    obtain ⟨⟨i,y⟩,rfl⟩ := (H.atlas (level F ζ hζ C R P H U)).components.surjective x
    refine Quotient.inductionOn y ?_
    intro y
    simp [KPContSectorLineL2Isometry.squaredNorm, KPContSectorSmoothFramesSupport.sectionNorm_component]
  rw [hz]
  simp

private theorem tailworker_decay_sum {ι' : Type*} (t : Finset ι')
    (L : Set ℂ) (u : ι' → ℂ → Sections F ζ hζ C R P H U)
    (hu : ∀ i ∈ t, ∀ s ∈ L, ∀ a, Measurable (u i s a).val)
    (hd : ∀ i ∈ t, tailworker_decay F ζ hζ C R P H U L (u i)) :
    tailworker_decay F ζ hζ C R P H U L (fun s => ∑ i ∈ t, u i s) := by
  induction t using Finset.induction_on with
  | empty => simpa using tailworker_decay_zero F ζ hζ C R P H U L
  | @insert i t hit ih =>
    have hsum : ∀ s ∈ L, ∀ a, Measurable ((∑ j ∈ t, u j s) a).val := by
      intro s hs a
      simpa only [Finset.sum_apply, Submodule.coe_sum, Finset.sum_fn] using
        Finset.measurable_sum t (fun j hj => hu j (Finset.mem_insert_of_mem hj) s hs a)
    simpa only [Finset.sum_insert hit] using tailworker_decay_add F ζ hζ C R P H U L
      (u i) (fun s => ∑ j ∈ t, u j s)
      (hu i (Finset.mem_insert_self _ _)) (hd i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)) (fun j hj => hd j (Finset.mem_insert_of_mem hj)))

private theorem tailworker_spectral_bound (L : Set ℂ) (hL : IsCompact L)
    (hLV : L ⊆ V) (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L, ‖KPContActualChamberCasimirJets.lambdaJet F j s‖ ≤ B := by
  have hh : ContDiff ℂ (⊤ : ℕ∞ω) (KPContActualChamberCasimirJets.lambda F) := by
    unfold KPContActualChamberCasimirJets.lambda KPContinuation.spectralCoordinate
    fun_prop
  have hc := (hh.contDiffOn (s := V)).continuousOn_iteratedDerivWithin
    (m := j) (by simp) (show IsOpen V from KPChamberL2Defect.chamber_isOpen).uniqueDiffOn
  obtain ⟨B,hB⟩ := hL.exists_bound_of_continuousOn (hc.mono hLV)
  exact ⟨max B 0, le_max_right _ _, fun s hs => (hB s hs).trans (le_max_left _ _)⟩

private theorem tailworker_laplacian_decay (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V)
    (k : ℕ)
    (he : ∀ s ∈ L,
      lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s =
        KPContActualChamberCasimirJets.lambda F s • lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s -
        lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s +
        ∑ j ∈ Finset.Icc 1 (min k 2),
          ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) •
          lineG F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s)
    (hsource : tailworker_decay F ζ hζ C R P H U L
      (fun s => lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)) :
    tailworker_decay F ζ hζ C R P H U L
      (fun s => lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s) := by
  let u := fun n s => lineG F ζ hζ C R P H U ι f buffer χ source hι hf n s
  have hu : ∀ n s, ∀ a, Measurable (u n s a).val := by
    intro n s a
    exact ((smooth F ζ hζ C R P H U ι f buffer χ source hι hf n s).1 a).continuous.measurable
  have hdu : ∀ n, tailworker_decay F ζ hζ C R P H U L (u n) := by
    intro n ε hε
    simpa only [squareTail, squaredDensity, ite_true, tailworker_energy, u] using
      value_uniform_tails F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV n ε hε
  obtain ⟨B,hB,hbound⟩ := tailworker_spectral_bound F L hL hLV 0
  have hbound' : ∀ s ∈ L, ‖KPContActualChamberCasimirJets.lambda F s‖ ≤ B := by
    simpa [KPContActualChamberCasimirJets.lambdaJet] using hbound
  have hfirst := tailworker_decay_smul F ζ hζ C R P H U L (u k)
    (KPContActualChamberCasimirJets.lambda F) B hB hbound' (hdu k)
  have hneg := tailworker_decay_smul F ζ hζ C R P H U L
    (fun s => lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)
    (fun _ => (-1 : ℂ)) 1 (by norm_num) (by intro s hs; simp) hsource
  have hsub := tailworker_decay_add F ζ hζ C R P H U L
    (fun s => KPContActualChamberCasimirJets.lambda F s • u k s)
    (fun s => (-1 : ℂ) • lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)
    (by
      intro s hs a
      change Measurable (fun y => KPContActualChamberCasimirJets.lambda F s * (u k s a).val y)
      exact (hu k s a).const_mul _) hfirst hneg
  let v := fun j s => ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) • u (k-j) s
  have hv : ∀ j s, ∀ a, Measurable (v j s a).val := by
    intro j s a
    change Measurable (fun y => ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) * (u (k-j) s a).val y)
    exact (hu (k-j) s a).const_mul _
  have hdv : ∀ j, tailworker_decay F ζ hζ C R P H U L (v j) := by
    intro j
    obtain ⟨B,hB,hbound⟩ := tailworker_spectral_bound F L hL hLV j
    apply tailworker_decay_smul F ζ hζ C R P H U L (u (k-j))
      (fun s => (Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s)
      (‖(Nat.choose k j : ℂ)‖ * B) (by positivity) _ (hdu (k-j))
    intro s hs
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound s hs) (norm_nonneg _)
  have hsum := tailworker_decay_sum F ζ hζ C R P H U (Finset.Icc 1 (min k 2)) L v
    (fun j hj s hs => hv j s) (fun j hj => hdv j)
  have hall := tailworker_decay_add F ζ hζ C R P H U L
    (fun s => KPContActualChamberCasimirJets.lambda F s • u k s +
      (-1 : ℂ) • lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)
    (fun s => ∑ j ∈ Finset.Icc 1 (min k 2), v j s)
    (by
      intro s hs a
      change Measurable (fun y => KPContActualChamberCasimirJets.lambda F s * (u k s a).val y +
        (-1 : ℂ) * (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s a).val y)
      exact ((hu k s a).const_mul _).add
        (((smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).2 a).continuous.measurable.const_mul _))
    hsub hsum
  intro ε hε
  obtain ⟨A,hA,hbound⟩ := hall ε hε
  refine ⟨A,hA,?_⟩
  intro A' hA' s hs
  dsimp only
  rw [he s hs]
  have hn : (-1 : ℂ) • lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      -lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s := by
    exact _root_.neg_one_smul (R := ℂ) (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)
  simpa only [v, u, hn, sub_eq_add_neg] using hbound A' hA' s hs

private theorem laplacian_uniform_tails_from_rhs (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V)
    (k : ℕ)
    (he : ∀ s ∈ L,
      lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s =
        KPContActualChamberCasimirJets.lambda F s • lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s -
        lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s +
        ∑ j ∈ Finset.Icc 1 (min k 2),
          ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) •
          lineG F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s)
    (hsource : ∃ A : ℝ, ∀ A', A ≤ A' → ∀ s ∈ L,
      (∫⁻ x in tail F ζ hζ C R P H U A',
        KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H
          (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
          ∂baseMeasure F ζ hζ C R P H U) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ,
      (H.atlas (level F ζ hζ C R P H U)).threshold < A ∧
      ∀ A' : ℝ, A ≤ A' → ∀ s ∈ L,
        squareTail F ζ hζ C R P H U ι f buffer χ source hι hf 2 k s A' ≤ ENNReal.ofReal ε := by
  have hdsource : tailworker_decay F ζ hζ C R P H U L
      (fun s => lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s) := by
    obtain ⟨A,hA⟩ := hsource
    intro ε hε
    refine ⟨max A ((H.atlas (level F ζ hζ C R P H U)).threshold+1),
      lt_of_lt_of_le (by linarith) (le_max_right _ _), ?_⟩
    intro A' hA' s hs
    unfold tailworker_energy
    rw [hA A' ((le_max_left _ _).trans hA') s hs]
    exact bot_le
  simpa only [squareTail, squaredDensity, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, ite_false, tailworker_decay, tailworker_energy] using
      tailworker_laplacian_decay F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV k he hdsource

private theorem three_uniform_tails_from_laplacian (L : Set ℂ) (hL : IsCompact L)
    (hLV : L ⊆ V) (k : ℕ)
    (hdelta : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ,
      (H.atlas (level F ζ hζ C R P H U)).threshold < A ∧
      ∀ A', A ≤ A' → ∀ s ∈ L,
        squareTail F ζ hζ C R P H U ι f buffer χ source hι hf 2 k s A' ≤ ENNReal.ofReal ε) :
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ,
      (H.atlas (level F ζ hζ C R P H U)).threshold < A ∧
      ∀ A', A ≤ A' → ∀ j : Fin 3, ∀ s ∈ L,
        squareTail F ζ hζ C R P H U ι f buffer χ source hι hf j k s A' ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨A,hA,hbound⟩ := value_uniform_tails F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV k ε hε
  obtain ⟨B,hB,hbound'⟩ := gradient_uniform_tails F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV k ε hε
  obtain ⟨D,hD,hbound''⟩ := hdelta ε hε
  refine ⟨max A (max B D), lt_of_lt_of_le hA (le_max_left _ _), ?_⟩
  intro A' hA' j s hs
  fin_cases j
  · exact hbound A' ((le_max_left _ _).trans hA') s hs
  · exact hbound' A' ((le_max_left _ _).trans ((le_max_right _ _).trans hA')) s hs
  · exact hbound'' A' ((le_max_right _ _).trans ((le_max_right _ _).trans hA')) s hs

 def tailworker_total (u : Sections F ζ hζ C R P H U) : ℝ≥0∞ :=
  ∫⁻ x, KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H u x
    ∂baseMeasure F ζ hζ C R P H U

 def tailworker_bounded (L : Set ℂ) (u : ℂ → Sections F ζ hζ C R P H U) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L, tailworker_total F ζ hζ C R P H U (u s) ≤ ENNReal.ofReal B

private theorem tailworker_bounded_add (L : Set ℂ) (u v : ℂ → Sections F ζ hζ C R P H U)
    (hu : ∀ s ∈ L, ∀ i, Measurable (u s i).val)
    (hdu : tailworker_bounded F ζ hζ C R P H U L u)
    (hdv : tailworker_bounded F ζ hζ C R P H U L v) :
    tailworker_bounded F ζ hζ C R P H U L (fun s => u s + v s) := by
  obtain ⟨A,hA,hbound⟩ := hdu
  obtain ⟨B,hB,hbound'⟩ := hdv
  refine ⟨2*A+2*B, by positivity, ?_⟩
  intro s hs
  have hsum : tailworker_total F ζ hζ C R P H U (u s + v s) ≤
      2 * tailworker_total F ζ hζ C R P H U (u s) + 2 * tailworker_total F ζ hζ C R P H U (v s) := by
    unfold tailworker_total
    apply (lintegral_mono (tailworker_squared_add F ζ hζ C R P H U _ _)).trans
    rw [lintegral_add_left ((KPContSectorLineL2Isometry.squaredNorm_measurable F ζ hζ
      (level F ζ hζ C R P H U) R P H _ (hu s hs)).const_mul 2),
      lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
  apply hsum.trans
  calc
    _ ≤ 2 * ENNReal.ofReal A + 2 * ENNReal.ofReal B :=
      add_le_add (mul_le_mul_right (hbound s hs) _) (mul_le_mul_right (hbound' s hs) _)
    _ = ENNReal.ofReal (2*A+2*B) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num

private theorem tailworker_bounded_smul (L : Set ℂ) (u : ℂ → Sections F ζ hζ C R P H U)
    (c : ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hc : ∀ s ∈ L, ‖c s‖ ≤ B)
    (hdu : tailworker_bounded F ζ hζ C R P H U L u) :
    tailworker_bounded F ζ hζ C R P H U L (fun s => c s • u s) := by
  obtain ⟨A,hA,hbound⟩ := hdu
  refine ⟨B^2*A, by positivity, ?_⟩
  intro s hs
  unfold tailworker_total
  simp_rw [tailworker_squared_smul F ζ hζ C R P H U]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ENNReal.ofReal (B^2) * ENNReal.ofReal A :=
      mul_le_mul (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hc s hs) 2))
        (hbound s hs) (by positivity) (by positivity)
    _ = ENNReal.ofReal (B^2*A) := (ENNReal.ofReal_mul (sq_nonneg _)).symm

private theorem tailworker_bounded_sum {ι' : Type*} (t : Finset ι')
    (L : Set ℂ) (u : ι' → ℂ → Sections F ζ hζ C R P H U)
    (hu : ∀ i ∈ t, ∀ s ∈ L, ∀ a, Measurable (u i s a).val)
    (hd : ∀ i ∈ t, tailworker_bounded F ζ hζ C R P H U L (u i)) :
    tailworker_bounded F ζ hζ C R P H U L (fun s => ∑ i ∈ t, u i s) := by
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨0, le_rfl, ?_⟩
    intro s hs
    simp only [Finset.sum_empty, tailworker_total, KPContSectorLineL2Isometry.squaredNorm]
    have hz : KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ (level F ζ hζ C R P H U) R P H
        (0 : Sections F ζ hζ C R P H U) = 0 := by
      funext x
      obtain ⟨⟨i,y⟩,rfl⟩ := (H.atlas (level F ζ hζ C R P H U)).components.surjective x
      refine Quotient.inductionOn y ?_
      intro y
      simp [KPContSectorSmoothFramesSupport.sectionNorm_component]
    rw [hz]
    simp
  | @insert i t hit ih =>
    simpa only [Finset.sum_insert hit] using tailworker_bounded_add F ζ hζ C R P H U L
      (u i) (fun s => ∑ j ∈ t, u j s)
      (hu i (Finset.mem_insert_self _ _)) (hd i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)) (fun j hj => hd j (Finset.mem_insert_of_mem hj)))

private theorem tailworker_laplacian_bounded (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V)
    (k : ℕ)
    (he : ∀ s ∈ L,
      lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s =
        KPContActualChamberCasimirJets.lambda F s • lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s -
        lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s +
        ∑ j ∈ Finset.Icc 1 (min k 2),
          ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) •
          lineG F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s)
    (hvalues : ∀ n, tailworker_bounded F ζ hζ C R P H U L
      (fun s => lineG F ζ hζ C R P H U ι f buffer χ source hι hf n s))
    (hsource : tailworker_bounded F ζ hζ C R P H U L
      (fun s => lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)) :
    tailworker_bounded F ζ hζ C R P H U L
      (fun s => lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s) := by
  let u := fun n s => lineG F ζ hζ C R P H U ι f buffer χ source hι hf n s
  have hu : ∀ n s, ∀ a, Measurable (u n s a).val := by
    intro n s a
    exact ((smooth F ζ hζ C R P H U ι f buffer χ source hι hf n s).1 a).continuous.measurable
  have hdu : ∀ n, tailworker_bounded F ζ hζ C R P H U L (u n) := hvalues
  obtain ⟨B,hB,hbound⟩ := tailworker_spectral_bound F L hL hLV 0
  have hbound' : ∀ s ∈ L, ‖KPContActualChamberCasimirJets.lambda F s‖ ≤ B := by
    simpa [KPContActualChamberCasimirJets.lambdaJet] using hbound
  have hfirst := tailworker_bounded_smul F ζ hζ C R P H U L (u k)
    (KPContActualChamberCasimirJets.lambda F) B hB hbound' (hdu k)
  have hneg := tailworker_bounded_smul F ζ hζ C R P H U L
    (fun s => lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)
    (fun _ => (-1 : ℂ)) 1 (by norm_num) (by intro s hs; simp) hsource
  have hsub := tailworker_bounded_add F ζ hζ C R P H U L
    (fun s => KPContActualChamberCasimirJets.lambda F s • u k s)
    (fun s => (-1 : ℂ) • lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)
    (by
      intro s hs a
      change Measurable (fun y => KPContActualChamberCasimirJets.lambda F s * (u k s a).val y)
      exact (hu k s a).const_mul _) hfirst hneg
  let v := fun j s => ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) • u (k-j) s
  have hv : ∀ j s, ∀ a, Measurable (v j s a).val := by
    intro j s a
    change Measurable (fun y => ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) * (u (k-j) s a).val y)
    exact (hu (k-j) s a).const_mul _
  have hdv : ∀ j, tailworker_bounded F ζ hζ C R P H U L (v j) := by
    intro j
    obtain ⟨B,hB,hbound⟩ := tailworker_spectral_bound F L hL hLV j
    apply tailworker_bounded_smul F ζ hζ C R P H U L (u (k-j))
      (fun s => (Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s)
      (‖(Nat.choose k j : ℂ)‖ * B) (by positivity) _ (hdu (k-j))
    intro s hs
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound s hs) (norm_nonneg _)
  have hsum := tailworker_bounded_sum F ζ hζ C R P H U (Finset.Icc 1 (min k 2)) L v
    (fun j hj s hs => hv j s) (fun j hj => hdv j)
  have hall := tailworker_bounded_add F ζ hζ C R P H U L
    (fun s => KPContActualChamberCasimirJets.lambda F s • u k s +
      (-1 : ℂ) • lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)
    (fun s => ∑ j ∈ Finset.Icc 1 (min k 2), v j s)
    (by
      intro s hs a
      change Measurable (fun y => KPContActualChamberCasimirJets.lambda F s * (u k s a).val y +
        (-1 : ℂ) * (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s a).val y)
      exact ((hu k s a).const_mul _).add
        (((smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).2 a).continuous.measurable.const_mul _))
    hsub hsum
  obtain ⟨B,hB,hbound⟩ := hall
  refine ⟨B,hB,?_⟩
  intro s hs
  dsimp only
  rw [he s hs]
  have hn : (-1 : ℂ) • lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      -lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s := by
    exact _root_.neg_one_smul (R := ℂ) (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)
  simpa only [v, u, hn, sub_eq_add_neg] using hbound s hs

private theorem lineDelta_global_square_bound (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L,
    (∫⁻ x, KPContSectorLineL2Isometry.squaredNorm F ζ hζ
      (level F ζ hζ C R P H U) R P H
      (lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
      ∂baseMeasure F ζ hζ C R P H U) ≤ ENNReal.ofReal B := by
  apply tailworker_laplacian_bounded F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV k
  · intro s hs
    exact lineDelta_eq_rhs F ζ hζ C R P H U ι f buffer χ source hι hf k s (hLV hs)
  · intro n
    exact lineG_global_square_bound F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV n
  · exact lineH_global_square_bound F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV k

private theorem gradient_compact_square_bound (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V)
    (K : Set (Base F ζ hζ C R P H U)) (hK : IsCompact K) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L,
      (∫⁻ x in K, (KPContActualCotangentMeasurableFamilies.normSquare
        (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) x : ℝ≥0∞)
        ∂baseMeasure F ζ hζ C R P H U) ≤ ENNReal.ofReal B := by
  let cover := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ
    (level F ζ hζ C R P H U) R P H).2.some
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun n => (cover.chart n).baseDomain)
    (fun n => (cover.properties n).base_open) (by
      intro x hx
      rw [cover.covers]
      exact Set.mem_univ x)
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let charts := fun i => cover.chart (e i).val
  have hcover : K ⊆ ⋃ i, (charts i).baseDomain := by
    intro x hx
    obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp (ht hx)
    obtain ⟨i, hi⟩ := e.surjective ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨i, by simpa [charts, hi] using hxn⟩
  obtain ⟨Z, hZ, hZD, hcov⟩ := KPContActualCompactSectionL2Jets.finite_actual_compact_lifts
    K hK (Fintype.card t) charts hcover
  have hb : ∀ i, ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L, ∀ y ∈ Z i,
      (KPContActualCotangentMeasurableFamilies.normSquare
        (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s)
        (KPContCotangentOverlapRationalBranches.q (charts i) y) : ℝ) ≤ B := by
    intro i
    have hj := gradient_chart_norm_joint F ζ hζ C R P H U ι f buffer χ source hι hf
      k (charts i) (Z i) (hZ i) (hZD i)
    obtain ⟨b, hb⟩ := (hL.prod (hZ i)).exists_bound_of_continuousOn
      (hj.mono (Set.prod_mono hLV (Set.Subset.refl _)))
    refine ⟨max 0 b, le_max_left _ _, ?_⟩
    intro s hs y hy
    have hb' := hb (s,y) ⟨hs,hy⟩
    rw [Real.norm_eq_abs] at hb'
    exact (le_abs_self _).trans (hb'.trans (le_max_right _ _))
  choose b hb hbound using hb
  let B := ∑ i, b i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hb i)
  have hpoint : ∀ s ∈ L, ∀ x ∈ K,
      (KPContActualCotangentMeasurableFamilies.normSquare
        (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) x : ℝ) ≤ B := by
    intro s hs x hx
    obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp (hcov hx)
    exact (hbound i s hs y hy).trans
      (Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i))
  letI := KPContSectorFixedMeasureLocalFiniteness.sphericalMeasure_finiteOnCompacts
    F ζ hζ R P (level F ζ hζ C R P H U)
  let D := ENNReal.ofReal B * baseMeasure F ζ hζ C R P H U K
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK.measure_lt_top.ne
  refine ⟨D.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro s hs
  rw [ENNReal.ofReal_toReal hD]
  calc
    _ ≤ ∫⁻ _x in K, ENNReal.ofReal B ∂baseMeasure F ζ hζ C R P H U := by
      apply setLIntegral_mono' hK.measurableSet
      intro x hx
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (hpoint s hs x hx)
    _ = D := by simp [D]

private theorem gradient_global_square_bound (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V)
    (k : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L,
      (∫⁻ x, (KPContActualCotangentMeasurableFamilies.normSquare
        (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) x : ℝ≥0∞)
        ∂baseMeasure F ζ hζ C R P H U) ≤ ENNReal.ofReal B := by
  obtain ⟨A, E, hA, hE, hend⟩ := gradient_high_end_square_bound
    F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV k
  let K := (tail F ζ hζ C R P H U A)ᶜ
  have hK : IsCompact K := by
    convert KPContThreeL2EndHelpers.compact_truncated_core F ζ hζ
      (level F ζ hζ C R P H U) R P H A using 1
    ext x
    simp only [K,tail,KPCuspCutoffGraph.highEnds,KPContActualCollarBuffer.endSet,
      Set.mem_compl_iff,Set.mem_iUnion]
    exact not_congr ⟨fun ⟨i,c,h⟩ => ⟨⟨i,c⟩,h⟩,fun ⟨⟨i,c⟩,h⟩ => ⟨i,c,h⟩⟩
  obtain ⟨B, hB, hcore⟩ := gradient_compact_square_bound
    F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV K hK k
  let N := Fintype.card (KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
  refine ⟨B + N * E, by positivity, ?_⟩
  intro s hs
  have ht : tail F ζ hζ C R P H U A =
      ⋃ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U,
        KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A a := by
    ext x
    simp only [tail,KPCuspCutoffGraph.highEnds,KPContActualCollarBuffer.endSet,Set.mem_iUnion]
    exact ⟨fun ⟨i,c,h⟩ => ⟨⟨i,c⟩,h⟩,fun ⟨⟨i,c⟩,h⟩ => ⟨i,c,h⟩⟩
  have htail : (∫⁻ x in tail F ζ hζ C R P H U A,
      (KPContActualCotangentMeasurableFamilies.normSquare
        (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) x : ℝ≥0∞)
      ∂baseMeasure F ζ hζ C R P H U) ≤ ENNReal.ofReal (N * E) := by
    rw [ht]
    apply (lintegral_iUnion_le _ _).trans
    rw [tsum_fintype]
    calc
      _ ≤ ∑ _a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U, ENNReal.ofReal E :=
        Finset.sum_le_sum (fun a _ => hend a s hs)
      _ = ENNReal.ofReal (N * E) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  calc
    _ = (∫⁻ x in K, (KPContActualCotangentMeasurableFamilies.normSquare
        (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) x : ℝ≥0∞)
        ∂baseMeasure F ζ hζ C R P H U) +
        (∫⁻ x in tail F ζ hζ C R P H U A, (KPContActualCotangentMeasurableFamilies.normSquare
        (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s) x : ℝ≥0∞)
        ∂baseMeasure F ζ hζ C R P H U) := by
      simpa [K] using (lintegral_add_compl _ hK.measurableSet).symm
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal (N * E) := add_le_add (hcore s hs) htail
    _ = ENNReal.ofReal (B + N * E) := (ENNReal.ofReal_add hB (by positivity)).symm

private theorem three_uniform_bounds_from_components (L : Set ℂ) (k : ℕ)
    (hv : ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L,
      squareIntegral F ζ hζ C R P H U ι f buffer χ source hι hf 0 k s ≤ ENNReal.ofReal B)
    (hg : ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L,
      squareIntegral F ζ hζ C R P H U ι f buffer χ source hι hf 1 k s ≤ ENNReal.ofReal B)
    (hd : ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ L,
      squareIntegral F ζ hζ C R P H U ι f buffer χ source hι hf 2 k s ≤ ENNReal.ofReal B) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : Fin 3, ∀ s ∈ L,
      squareIntegral F ζ hζ C R P H U ι f buffer χ source hι hf j k s ≤ ENNReal.ofReal B := by
  obtain ⟨A,hA,hbound⟩ := hv
  obtain ⟨B,hB,hbound'⟩ := hg
  obtain ⟨D,hD,hbound''⟩ := hd
  refine ⟨max A (max B D), hA.trans (le_max_left _ _), ?_⟩
  intro j s hs
  fin_cases j
  · exact (hbound s hs).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · exact (hbound' s hs).trans (ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_right _ _)))
  · exact (hbound'' s hs).trans (ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_right _ _)))

structure Properties : Prop where
  smooth_jets : ∀ k s, s ∈ V →
    KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ (level F ζ hζ C R P H U) R P H
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) ∧
    KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ (level F ζ hζ C R P H U) R P H
      (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)
  three_l2 : ∀ k s, s ∈ V →
    lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈ BorelL2Sections F ζ hζ C R P H U ∧
    lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈ BorelL2Sections F ζ hζ C R P H U ∧
    KPContActualCotangentMeasurableFamilies.squareFinite (R := R) (P := P)
      (gradient F ζ hζ C R P H U ι f buffer χ source hι hf k s)
  covered_values : ∀ k s, s ∈ V →
    (coveredG F ζ hζ C R P H U ι f buffer χ source hι hf k s).val =
      g F ζ hζ C R P H U ι f buffer χ source k s ∧
    (coveredH F ζ hζ C R P H U ι f buffer χ source hι hf k s).val =
      h F ζ hζ C R P H U ι f buffer χ source k s

  frame_equation : ∀ k s, s ∈ V →
    ∀ (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
      (a : Frame F ζ hζ C R P H U i) (x : KPContActualChamberCasimirJets.M F), x ∈ a.omega →
    HyperbolicChart.laplacian (KPContActualChamberCasimirJets.d F)
      (a.coefficient (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)) x =
    KPContActualChamberCasimirJets.lambda F s *
      a.coefficient (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x -
      a.coefficient (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s) x +
      ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) *
        KPContActualChamberCasimirJets.lambdaJet F j s *
        a.coefficient (lineG F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s) x
  laplacian_frames : ∀ k s, s ∈ V → ∀ i (a : Frame F ζ hζ C R P H U i) x, x ∈ a.omega →
    a.coefficient (lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s) x =
      HyperbolicChart.laplacian (KPContActualChamberCasimirJets.d F)
        (a.coefficient (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)) x
  covered_memLp : ∀ k s, s ∈ V →
    MemLp (g F ζ hζ C R P H U ι f buffer χ source k s) 2 (measure F ζ hζ C R P H U) ∧
    MemLp (h F ζ hζ C R P H U ι f buffer χ source k s) 2 (measure F ζ hζ C R P H U)

  uniform_bounds : ∀ L : Set ℂ, IsCompact L → L ⊆ V → ∀ k,
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : Fin 3, ∀ s ∈ L,
      squareIntegral F ζ hζ C R P H U ι f buffer χ source hι hf j k s ≤ ENNReal.ofReal B

  uniform_tails : ∀ L : Set ℂ, IsCompact L → L ⊆ V → ∀ k,
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ,
      (H.atlas (level F ζ hζ C R P H U)).threshold < A ∧
      ∀ A' : ℝ, A ≤ A' → ∀ j : Fin 3, ∀ s ∈ L,
        squareTail F ζ hζ C R P H U ι f buffer χ source hι hf j k s A' ≤ ENNReal.ofReal ε

  source_support : ∀ k s, s ∈ V → tsupport
    (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ (level F ζ hζ C R P H U) R P H
      (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)) ⊆
      KPContActualAllCuspSource.K F ζ hζ C R P H U buffer
  actual_ae : ∀ k s, s ∈ V →
    ((UJet F ζ hζ C R P H U ι f buffer χ source hι hf k s).val : Covered F ζ hζ C R P H U → ℂ)
      =ᵐ[measure F ζ hζ C R P H U] g F ζ hζ C R P H U ι f buffer χ source k s ∧
    ((HJet F ζ hζ C R P H U ι f buffer χ source hι hf k s).val : Covered F ζ hζ C R P H U → ℂ)
      =ᵐ[measure F ζ hζ C R P H U] h F ζ hζ C R P H U ι f buffer χ source k s ∧
    ((DeltaJet F ζ hζ C R P H U ι f buffer χ source hι hf k s).val : Covered F ζ hζ C R P H U → ℂ)
      =ᵐ[measure F ζ hζ C R P H U]
        (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ
          (level F ζ hζ C R P H U) R P H
          (lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s)).val

  differential_rhs_class : ∀ k s, s ∈ V →
    DeltaJet F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      KPContActualChamberCasimirJets.lambda F s •
        UJet F ζ hζ C R P H U ι f buffer χ source hι hf k s -
      HJet F ζ hζ C R P H U ι f buffer χ source hι hf k s +
      ∑ j ∈ Finset.Icc 1 (min k 2),
        ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) •
          UJet F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s

end DedekindZetaZeroFree.KPContActualChamberThreeL2Tails

namespace DedekindZetaZeroFree

theorem kp_cont_actual_chamber_three_l2_tails
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (_realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (hι : Function.Injective ι) (f : ℂ → S)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
      KPContinuation.spectralDomain f χ) :
    KPContActualChamberThreeL2Tails.Properties F ζ hζ C R P H U ι f buffer χ source hι hf := by
  letI _ := Classical.propDecidable
  refine {
    smooth_jets := ?_
    three_l2 := ?_
    covered_values := ?_
    frame_equation := ?_
    laplacian_frames := ?_
    covered_memLp := ?_
    uniform_bounds := ?_
    uniform_tails := ?_
    source_support := ?_
    actual_ae := ?_
    differential_rhs_class := ?_ }
  · intro k s hs
    exact KPContActualChamberThreeL2Tails.smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s
  · intro k s hs
    have hi := KPContActualChamberThreeL2Tails.integrability F ζ hζ C R P H U ι f buffer χ source hι hf k s
    exact ⟨hi.1, hi.2.2⟩
  · intro k s hs
    simp [KPContActualChamberThreeL2Tails.coveredG,
      KPContActualChamberThreeL2Tails.coveredH, hs]
  · exact KPContActualChamberThreeL2Tails.defect_frame_equation F ζ hζ C R P H U ι f buffer χ source hι hf
  · intro k s hs
    exact KPContActualChamberThreeL2Tails.lineDelta_frame F ζ hζ C R P H U ι f buffer χ source hι hf k s
  · intro k s hs
    exact ⟨KPContActualChamberThreeL2Tails.g_memLp F ζ hζ C R P H U ι f buffer χ source hι hf k s hs,
      KPContActualChamberThreeL2Tails.h_memLp F ζ hζ C R P H U ι f buffer χ source hι hf k s hs⟩
  · intro L hL hLV k
    apply KPContActualChamberThreeL2Tails.three_uniform_bounds_from_components
      F ζ hζ C R P H U ι f buffer χ source hι hf L k
    · exact KPContActualChamberThreeL2Tails.lineG_global_square_bound
        F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV k
    · simpa [KPContActualChamberThreeL2Tails.squareIntegral,
        KPContActualChamberThreeL2Tails.squaredDensity] using
        KPContActualChamberThreeL2Tails.gradient_global_square_bound
          F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV k
    · exact KPContActualChamberThreeL2Tails.lineDelta_global_square_bound
        F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV k
  · intro L hL hLV k
    apply KPContActualChamberThreeL2Tails.three_uniform_tails_from_laplacian F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV k
    apply KPContActualChamberThreeL2Tails.laplacian_uniform_tails_from_rhs F ζ hζ C R P H U ι f buffer χ source hι hf L hL hLV k
    · intro s hs
      exact KPContActualChamberThreeL2Tails.lineDelta_eq_rhs F ζ hζ C R P H U ι f buffer χ source hι hf k s (hLV hs)
    · obtain ⟨A,hA,hzero⟩ := KPContActualChamberThreeL2Tails.source_high_tail_zero F ζ hζ C R P H U ι f buffer χ source hι hf
      exact ⟨A, fun A' hA' s hs => hzero A' hA' k s⟩
  · intro k s hs
    exact KPContActualChamberThreeL2Tails.lineH_support F ζ hζ C R P H U ι f buffer χ source hι hf k s
  · exact KPContActualChamberThreeL2Tails.jets_actual_ae F ζ hζ C R P H U ι f buffer χ source hι hf
  · intro k s hs
    exact KPContActualChamberThreeL2Tails.differential_class_from_rhs F ζ hζ C R P H U ι f buffer χ source hι hf k s
      (KPContActualChamberThreeL2Tails.lineDelta_eq_rhs F ζ hζ C R P H U ι f buffer χ source hι hf k s hs)

end DedekindZetaZeroFree

end

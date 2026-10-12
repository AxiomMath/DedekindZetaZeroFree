module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestFriedrichsRealization
public import DedekindZetaZeroFree.Geometry.Hyperbolic.Laplacian.LogarithmicCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorCutoffGraphLimit

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings
open KPContActualSectorTestDifferentialDescent
open KPContActualCotangentMeasurableFamilies KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

abbrev SmoothSection := ↥(KPContSectorSmoothFramesSupport.smoothSections F ζ hζ U R P H)

abbrev Cutoffs := KPCuspCutoffGraph.Cutoffs F ζ hζ H.totallyComplex U (H.atlas U)

def realCutoff (r : Cutoffs (U := U) (H := H)) (n : ℕ) : RealSmoothCutoff F ζ hζ U R P H where
  val := r.rho n
  smooth := by
    intro a

    refine ⟨fun y : M F => r.rho n (KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex U
        (H.atlas U) a.component (labeledA (placeEquiv F ζ hζ) y)), ?_, ?_⟩
    · have hA : ContDiff ℝ (⊤ : ℕ∞) (labeledA (placeEquiv F ζ hζ) :
          M F → KPCuspGenuineMonodromy.SymmetricSpace F) := by
        apply contDiff_pi.mpr
        intro k
        exact ((ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin (d F) => KPArch.H3)
          (placeEquiv F ζ hζ |>.symm k)).contDiff.comp
          (CotangentLogCoframe.A (d F)).contDiff)
      exact ((r.smooth n a.component).comp hA).contDiffOn
    · intro x
      congr 1

def localLaplacian (w : SmoothSection (U := U) (H := H)) : Sections F ζ hζ U R P H :=
  KPCuspCutoffGraph.localLaplacianSection F ζ hζ H.totallyComplex U (H.atlas U)
    ⟨w.val, w.property⟩

private theorem contDiff_coordinateDerivative {n : ℕ} (h : HyperbolicChart.Space n → ℂ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (i : Fin n) (k : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => HyperbolicChart.coordinateDerivative n i k h p) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun q : HyperbolicChart.Space n × HyperbolicChart.Space n =>
      (fderiv ℝ h q.1 : HyperbolicChart.Space n →L[ℝ] ℂ) q.2) :=
    hh.contDiff_fderiv_apply (m := (⊤ : ℕ∞)) (by simp)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : HyperbolicChart.Space n =>
      (p, HyperbolicChart.coordinateVector n i k)) := contDiff_id.prodMk contDiff_const
  have h3 := h1.comp h2
  change ContDiff ℝ (⊤ : ℕ∞) (fun p : HyperbolicChart.Space n =>
    (fderiv ℝ h p) (HyperbolicChart.coordinateVector n i k)) at h3
  simpa only [HyperbolicChart.coordinateDerivative] using h3

private theorem contDiff_laplacian {n : ℕ} (h : HyperbolicChart.Space n → ℂ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (HyperbolicChart.laplacian n h) := by
  unfold HyperbolicChart.laplacian
  apply ContDiff.sum
  intro i _
  have h2 := contDiff_coordinateDerivative h hh i 2
  have h0 := contDiff_coordinateDerivative h hh i 0
  have h1 := contDiff_coordinateDerivative h hh i 1
  have h22 := contDiff_coordinateDerivative _ h2 i 2
  have h00 := contDiff_coordinateDerivative _ h0 i 0
  have h11 := contDiff_coordinateDerivative _ h1 i 1
  have hr : ContDiff ℝ (⊤ : ℕ∞) (fun p : HyperbolicChart.Space n => 2 * p (i, 2)) := by
    fun_prop
  have hexp : ContDiff ℝ (⊤ : ℕ∞) (fun p : HyperbolicChart.Space n =>
      (Real.exp (2 * p (i, 2)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr.exp
  exact ((h22.neg.add (contDiff_const.mul h2)).sub (hexp.mul (h00.add h11)))

private lemma fromArch_eq_symm :
    KPCuspCutoffGraph.fromArch F =
      ⇑(CotangentLogCoframe.A (KPCuspLogShape.dimension F)).symm := by
  funext z
  rfl

 theorem measurable_localLaplacianComplex (s : Sections F ζ hζ U R P H)
    (hs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (s i).val) (i : Fin (H.atlas U).componentCount) :
    Measurable (KPCuspCutoffGraph.localLaplacianComplex F ζ hζ H.totallyComplex U
      (H.atlas U) s i) := by
  have hsm : ContDiff ℝ (⊤ : ℕ∞) ((s i).val ∘ KPCuspCutoffGraph.toArch F) :=
    (hs i).comp (KPCuspCutoffGraphApproximation.cutoff_toArch_contDiff F)
  have hcont_from : Continuous (KPCuspCutoffGraph.fromArch F) := by
    rw [fromArch_eq_symm]
    exact (CotangentLogCoframe.A (KPCuspLogShape.dimension F)).symm.continuous
  have hcont : Continuous (fun x : KPCuspCutoffGraph.Arch F =>
      HyperbolicChart.laplacian (KPCuspLogShape.dimension F)
        ((s i).val ∘ KPCuspCutoffGraph.toArch F) (KPCuspCutoffGraph.fromArch F x)) :=
    (contDiff_laplacian _ hsm).continuous.comp hcont_from
  exact hcont.measurable

private theorem continuous_labeledA_self :
    Continuous (labeledA (placeEquiv F ζ hζ) : M F → KPCuspGenuineMonodromy.SymmetricSpace F) := by
  apply continuous_pi
  intro k
  exact (continuous_apply (placeEquiv F ζ hζ |>.symm k)).comp
    (CotangentLogCoframe.A (d F)).continuous

private theorem isOpen_omega (a : ActualChart (U := U) (H := H)) : IsOpen (omega a) :=
  a.domain_open.preimage continuous_labeledA_self

private theorem smooth_liftExtension {a : ActualChart (U := U) (H := H)} {f : omega a → ℂ}
    (hf : SmoothOnLift a f) : ContDiffOn ℝ (⊤ : ℕ∞) (liftExtension a f) (omega a) := by
  obtain ⟨g, hg, he⟩ := hf
  refine hg.congr (f₁ := liftExtension a f) ?_
  intro x hx
  simpa [liftExtension, hx] using (he ⟨x, hx⟩).symm

private theorem smooth_differential {a : ActualChart (U := U) (H := H)} {f : omega a → ℂ}
    (hf : SmoothOnLift a f) : SmoothOnLift a (fun x => CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (liftExtension a f) x.val)) := by
  refine ⟨fun x => CotangentLogCoframe.j (d F)
    (HyperbolicChart.differential (d F) (liftExtension a f) x), ?_, fun _ => rfl⟩
  rw [contDiffOn_piLp]
  rintro ⟨i, k⟩
  have hd := (smooth_liftExtension hf).fderiv_of_isOpen (isOpen_omega a) (m := (⊤ : ℕ∞)) (by simp)
  have hcd (k : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞)
      (HyperbolicChart.coordinateDerivative (d F) i k (liftExtension a f)) (omega a) :=
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
  exact hg.continuousOn.restrict.measurable

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

private theorem differential_frame_sum (f : M F → ℂ) (x : M F) (v : KPContCotangentActualGenuineTwistIsotropy.V F) :
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
      c • KPContCotangentRealOrthogonalComplexification.operatorComplexification _ (KPContCotangentActualGenuineTwistIsotropy.Q e x)
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
    change KPContCotangentActualGenuineTwistIsotropy.Q e x v = _
    change KPContCotangentActualGenuineTwistIsotropy.q e x hx v = _
    simp [v, CotangentLogCoframe.H]
  rw [← hh]
  have hdv := congrArg (fun A : M F →L[ℝ] ℂ => A (CotangentLogCoframe.H (d F) x v)) hd
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    differential_frame_sum] at hdv
  rw [hdv]
  change _ = c *
    (KPContCotangentRealOrthogonalComplexification.operatorComplexification _ (KPContCotangentActualGenuineTwistIsotropy.Q e x)
      (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x))) k
  rw [KPContCotangentRealOrthogonalComplexification.operatorComplexification_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  have hv : v l = KPContCotangentActualGenuineTwistIsotropy.Q e x (EuclideanSpace.basisFun _ ℝ l) k := by
    have hi := (KPContCotangentActualGenuineTwistIsotropy.q e x hx).inner_map_map
      v (EuclideanSpace.basisFun _ ℝ l)
    have hvq : KPContCotangentActualGenuineTwistIsotropy.q e x hx v =
        EuclideanSpace.basisFun _ ℝ k := by simp [v]
    rw [hvq] at hi
    change inner ℝ (EuclideanSpace.basisFun _ ℝ k)
      (KPContCotangentActualGenuineTwistIsotropy.Q e x (EuclideanSpace.basisFun _ ℝ l)) =
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
      KPContCotangentActualGenuineTwistIsotropy.T e x hx (CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) f x)) := by
  have hp : e.phase =ᶠ[𝓝 x] fun _ => e.phase x := by
    have hopen := e.isOpen_domain.isOpenMap_subtype_val _
      ((unitary_phase e).1.isOpen_fiber (e.phase x))
    have hmem : x ∈ (Subtype.val : e.domain → M F) '' {y | e.phase y.val = e.phase x} :=
      ⟨⟨x, hx⟩, rfl, rfl⟩
    filter_upwards [hopen.mem_nhds hmem] with y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact hz
  change _ = e.phase x •
    KPContCotangentRealOrthogonalComplexification.operatorComplexification _ (KPContCotangentActualGenuineTwistIsotropy.Q e x) _
  apply differential_arrow_const e (e.phase x) f g x hx hf hg
  filter_upwards [he, hp] with y hy hpy
  simpa [hpy] using hy

private theorem differentiable_liftExtension {a : ActualChart (U := U) (H := H)}
    {f : omega a → ℂ} (hf : SmoothOnLift a f) (x : omega a) :
    DifferentiableAt ℝ (liftExtension a f) x.val :=
  ((smooth_liftExtension hf).differentiableOn (by simp) x.val x.property).differentiableAt
    ((isOpen_omega a).mem_nhds x.property)

 theorem differential_measurable_local (f : ScalarFields F ζ hζ U R P H)
    (hf : ∀ a, SmoothOnLift a (f a)) (hc : ScalarCompatible f) :
    IsMeasurableCotangentFamily (fun a x => CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (liftExtension a (f a)) x.val)) := by
  refine ⟨fun a => measurable_smooth (smooth_differential (hf a)), ?_, ?_⟩
  · intro a γ x hx
    apply differential_arrow (KPContCotangentActualGenuineTwistIsotropy.isotropyArrow a γ) (liftExtension a (f a)) (liftExtension a (f a)) x
      (omega_subset_larger a hx) (differentiable_liftExtension (hf a) ⟨x, hx⟩)
      (differentiable_liftExtension (hf a) ⟨_, isotropy_mem a γ x hx⟩)
    filter_upwards [(isOpen_omega a).mem_nhds hx] with y hy
    simpa [liftExtension, hy, isotropy_mem a γ y hy] using hc.1 a γ y hy
  · intro a b e x hx
    apply differential_arrow e.arrow (liftExtension a (f a)) (liftExtension b (f b)) x hx
      (differentiable_liftExtension (hf a) ⟨x, e.source_shrinking hx⟩)
      (differentiable_liftExtension (hf b) ⟨_, e.target_shrinking hx⟩)
    filter_upwards [e.arrow.isOpen_domain.mem_nhds hx] with y hy
    simpa [liftExtension, e.source_shrinking hy, e.target_shrinking hy] using hc.2 a b e y hy

 theorem smoothOnLift_mul {a : ActualChart (U := U) (H := H)} {f g : omega a → ℂ}
    (hf : SmoothOnLift a f) (hg : SmoothOnLift a g) : SmoothOnLift a (fun x => f x * g x) := by
  obtain ⟨f', hf', he⟩ := hf
  obtain ⟨g', hg', he'⟩ := hg
  exact ⟨fun x => f' x * g' x, hf'.mul hg', fun x => by dsimp; rw [he x, he' x]⟩

 theorem smoothOnLift_ofReal {a : ActualChart (U := U) (H := H)} {f : omega a → ℝ}
    (hf : SmoothOnLift a f) : SmoothOnLift a (fun x => (f x : ℂ)) := by
  obtain ⟨g, hg, he⟩ := hf
  exact ⟨fun x => (g x : ℂ), Complex.ofRealCLM.contDiff.comp_contDiffOn hg,
    fun x => by dsimp; rw [he x]⟩

private theorem contDiff_labeledA :
    ContDiff ℝ (⊤ : ℕ∞) (labeledA (placeEquiv F ζ hζ) :
      M F → KPCuspGenuineMonodromy.SymmetricSpace F) := by
  apply contDiff_pi.mpr
  intro k
  exact ((ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin (d F) => KPArch.H3)
    (placeEquiv F ζ hζ |>.symm k)).contDiff.comp
    (CotangentLogCoframe.A (d F)).contDiff)

 theorem smoothOnLift_sectionFields_local (a : ActualChart (U := U) (H := H))
    (s : Sections F ζ hζ U R P H) (hs : IsSmoothSections F ζ hζ U R P H s) :
    SmoothOnLift a (sectionFields s a) := by
  refine ⟨fun y : M F => (s a.component).val (labeledA (placeEquiv F ζ hζ) y), ?_, ?_⟩
  · exact ((hs a.component).comp contDiff_labeledA).contDiffOn
  · intro x
    have hcoe : (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient s x.val =
        (KPCuspGenuineMonodromy.chi F ζ hζ ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).splitting x.val) : ℂ) *
          (s a.component).val ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).kind.representative •
            labeledA (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).places x.val) := rfl
    rw [sectionFields, hcoe]
    simp [KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative]

 theorem q_isotropyArrow (a : ActualChart (U := U) (H := H)) (γ : KPContCotangentActualGenuineTwistIsotropy.Gamma a) (x : M F)
    (hx : x ∈ omega a) :
    q a ((KPContCotangentActualGenuineTwistIsotropy.isotropyArrow a γ).psi x) = q a x := by
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U
    ((H.atlas U).representative a.component))
  have hA (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y) = y := by
    funext k
    simp [labeledA, labeledAInv]
  change KPCuspSiegel.projection F _
    (labeledA (placeEquiv F ζ hζ)
      (coordinateMap (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a) (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a) γ.val.1.val x)) = _
  simp only [coordinateMap, KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative, inv_one,
    one_mul, mul_one, hA]
  apply Quotient.sound
  exact ⟨γ.val.1.val, rfl⟩

 theorem q_actualBranch {a b : ActualChart (U := U) (H := H)} (e : ActualBranch a b)
    (x : M F) : q b (e.arrow.psi x) = q a x := by
  rcases e with ⟨h, e, hs, ht, hl⟩
  rcases a with ⟨i, ca, oa, da, dao, dac, das, dai⟩
  rcases b with ⟨j, cb, ob, db, dbo, dbc, dbs, dbi⟩
  dsimp at h
  subst j
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i))
  have hA (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y) = y := by
    funext k
    simp [labeledA, labeledAInv]
  change KPCuspSiegel.projection F _
    (labeledA (placeEquiv F ζ hζ) (coordinateMap _ _ e.gamma x)) = _
  simp only [coordinateMap, targetChart, KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative,
    inv_one, one_mul, mul_one, hA]
  apply Quotient.sound
  exact ⟨e.gamma, rfl⟩

private lemma targetChart_coefficient {a b : ActualChart (U := U) (H := H)}
    (h : a.component = b.component) (s : Sections F ζ hζ U R P H) (x : M F) :
    (targetChart a b h).coefficient s x = (KPContCotangentActualGenuineTwistIsotropy.isotropyChart b).coefficient s x := by
  rcases a with ⟨i, ca, oa, da, dao, dac, das, dai⟩
  rcases b with ⟨j, cb, ob, db, dbo, dbc, dbs, dbi⟩
  dsimp at h
  subst j
  rfl

 theorem scalarCompatible_sectionFields (s : Sections F ζ hζ U R P H) :
    ScalarCompatible (sectionFields s) := by
  refine ⟨?_, ?_⟩
  · intro a γ x hx
    have hx' : x ∈ (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).omega := omega_subset_larger a hx
    have h := (KPContCotangentActualOverlap.unitary_phase (KPContCotangentActualGenuineTwistIsotropy.isotropyArrow a γ)).2.2.2 s x hx'
    simpa only [sectionFields] using h
  · intro a b e x hx
    have h := (KPContCotangentActualOverlap.unitary_phase e.arrow).2.2.2 s x hx
    rw [targetChart_coefficient e.component_eq s (e.arrow.psi x)] at h
    simpa only [sectionFields] using h

def gradient (w : SmoothSection (U := U) (H := H)) : Family (U := U) (H := H) :=
  ⟨fun a => chartDifferential a (sectionFields w.val a),
    differential_measurable_local (sectionFields w.val)
      (fun a => smoothOnLift_sectionFields_local a w.val w.property)
      (scalarCompatible_sectionFields w.val)⟩

def ThreeL2 (w : SmoothSection (U := U) (H := H)) : Prop :=
  normIntegral F ζ hζ U R P H w.val < ⊤ ∧
  squareFinite (gradient w) ∧
  normIntegral F ζ hζ U R P H (localLaplacian w) < ⊤

abbrev GraphSection := {w : SmoothSection (U := U) (H := H) // ThreeL2 w}

def sectionClass (w : GraphSection (U := U) (H := H)) : KPContSectorClosedLpSubspace.H F ζ hζ R U :=
  toSector F ζ hζ U R P H
    ⟨w.val.val, ⟨fun i => (w.val.property i).continuous.measurable, w.property.1⟩⟩

def laplacianClass (w : GraphSection (U := U) (H := H)) : KPContSectorClosedLpSubspace.H F ζ hζ R U :=
  toSector F ζ hζ U R P H
    ⟨localLaplacian w.val,
      ⟨fun i => measurable_localLaplacianComplex (s := w.val.val)
        (hs := w.val.property) i, w.property.2.2⟩⟩

def cutoffTest (r : Cutoffs (U := U) (H := H)) (n : ℕ) (w : SmoothSection (U := U) (H := H)) :
    S_U F ζ hζ U R P H :=
  ⟨fun a x => cutoffLift (realCutoff r n) a x * sectionFields w.val a x, by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact smoothOnLift_mul (smoothOnLift_ofReal ((realCutoff r n).smooth a))
        (smoothOnLift_sectionFields_local a w.val w.property)
    · refine ⟨?_, ?_⟩
      · intro a γ x hx
        have hsec := (scalarCompatible_sectionFields w.val).1 a γ x hx
        have hcut : cutoffLift (realCutoff r n) a ⟨(KPContCotangentActualGenuineTwistIsotropy.isotropyArrow a γ).psi x,
            isotropy_mem a γ x hx⟩ = cutoffLift (realCutoff r n) a ⟨x, hx⟩ := by
          change (((realCutoff r n).val) (q a ((KPContCotangentActualGenuineTwistIsotropy.isotropyArrow a γ).psi x)) : ℂ) =
            (((realCutoff r n).val) (q a x) : ℂ)
          rw [q_isotropyArrow a γ x hx]
        show cutoffLift (realCutoff r n) a ⟨(KPContCotangentActualGenuineTwistIsotropy.isotropyArrow a γ).psi x,
            isotropy_mem a γ x hx⟩ * sectionFields w.val a ⟨(KPContCotangentActualGenuineTwistIsotropy.isotropyArrow a γ).psi x,
            isotropy_mem a γ x hx⟩ = (KPContCotangentActualGenuineTwistIsotropy.isotropyArrow a γ).phase x *
              (cutoffLift (realCutoff r n) a ⟨x, hx⟩ * sectionFields w.val a ⟨x, hx⟩)
        rw [hcut, hsec]; ring
      · intro a b e x hx
        have hsec := (scalarCompatible_sectionFields w.val).2 a b e x hx
        have hcut : cutoffLift (realCutoff r n) b ⟨e.arrow.psi x, e.target_shrinking hx⟩ =
            cutoffLift (realCutoff r n) a ⟨x, e.source_shrinking hx⟩ := by
          change (((realCutoff r n).val) (q b (e.arrow.psi x)) : ℂ) =
            (((realCutoff r n).val) (q a x) : ℂ)
          rw [q_actualBranch e x]
        show cutoffLift (realCutoff r n) b ⟨e.arrow.psi x, e.target_shrinking hx⟩ *
            sectionFields w.val b ⟨e.arrow.psi x, e.target_shrinking hx⟩ =
            e.arrow.phase x * (cutoffLift (realCutoff r n) a ⟨x, e.source_shrinking hx⟩ *
              sectionFields w.val a ⟨x, e.source_shrinking hx⟩)
        rw [hcut, hsec]; ring
    · have hsub : scalarSupport (fun a x =>
          cutoffLift (realCutoff r n) a x * sectionFields w.val a x) ⊆
          tsupport (r.rho n) := by
        apply closure_minimal _ (isClosed_tsupport _)
        rintro x ⟨a, y, hq, hne⟩
        rw [← hq]
        have h1 : cutoffLift (realCutoff r n) a y ≠ 0 := (mul_ne_zero_iff.mp hne).1
        have hc : r.rho n (q a y.val) ≠ 0 := by
          intro h0
          exact h1 (by simp only [cutoffLift, realCutoff, h0, Complex.ofReal_zero])
        exact subset_tsupport _ (Function.mem_support.mpr hc)
      exact (r.compact_support n).of_isClosed_subset isClosed_closure hsub⟩

theorem cutoff_mem_domain
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (r : Cutoffs (U := U) (H := H)) (n : ℕ) (w : SmoothSection (U := U) (H := H)) :
    iota (cutoffTest r n w) ∈
      (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization).domain := by
  exact (kp_cont_actual_sector_test_friedrichs F ζ hζ μG hμG U R hR P H
    realization).friedrichs.test_mem_laplacian (cutoffTest r n w)

def graphPair
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (r : Cutoffs (U := U) (H := H)) (n : ℕ) (w : SmoothSection (U := U) (H := H)) :
    KPContSectorClosedLpSubspace.H F ζ hζ R U × KPContSectorClosedLpSubspace.H F ζ hζ R U :=
  (iota (cutoffTest r n w),
    KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization
      ⟨iota (cutoffTest r n w), cutoff_mem_domain μG hμG hR realization r n w⟩)

def UniformTails {I : Type*} (f : I → KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i : I,
    (∫⁻ x, f i x ∂(KPContActualSectorCotangentL2.muU F ζ hζ U R P).restrict
      (KPCuspCutoffGraph.highEnds F ζ hζ H.totallyComplex U (H.atlas U) n)) < ENNReal.ofReal ε

def ThreeUniformTails {I : Type*} (w : I → GraphSection (U := U) (H := H)) : Prop :=
  UniformTails (U := U) (H := H) (fun i => squaredNorm F ζ hζ U R P H (w i).val.val) ∧
  UniformTails (U := U) (H := H) (fun i x => (normSquare (gradient (w i).val) x : ℝ≥0∞)) ∧
  UniformTails (U := U) (H := H) (fun i => squaredNorm F ζ hζ U R P H (localLaplacian (w i).val))

 def labeled (d n : ℕ) (p : Fin d ≃ Fin n) :
    HyperbolicChart.Space d ≃L[ℝ] KPArch.Space n :=
  (CotangentLogCoframe.A d).trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => KPArch.H3) p)
private lemma labeled_apply (d n : ℕ) (p : Fin d ≃ Fin n)
    (x : HyperbolicChart.Space d) (k : Fin n) :
    labeled d n p x k = CotangentLogCoframe.A d x (p.symm k) := by
  simp [labeled, ContinuousLinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft,
    Equiv.piCongrLeft, Equiv.piCongrLeft', Equiv.piCongrLeft'_apply]
private lemma labeled_vector (d n : ℕ) (p : Fin d ≃ Fin n) (i : Fin d) (k : Fin 3) :
    labeled d n p (HyperbolicChart.coordinateVector d i k) =
      KPContFlatCuspCasimirSpecialization.coordinateDirection n (p i) k := by
  funext j
  simp only [labeled_apply, CotangentLogCoframe.A_apply,
    HyperbolicChart.coordinateVector, WithLp.toLp,
    KPContFlatCuspCasimirSpecialization.coordinateDirection]
  by_cases h : p.symm j = i
  · have hj : j = p i := by simpa using congrArg p h
    subst j
    fin_cases k <;> simp [Pi.single_eq_same]
  · have hj : j ≠ p i := by intro he; exact h (by simp [he])
    simp [h, hj]
private lemma labeled_first (d n : ℕ) (p : Fin d ≃ Fin n)
    (f : KPArch.Space n → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) (k : Fin 3)
    (x : HyperbolicChart.Space d) :
    HyperbolicChart.coordinateDerivative d i k (f ∘ labeled d n p) x =
      fderiv ℝ f (labeled d n p x)
        (KPContFlatCuspCasimirSpecialization.coordinateDirection n (p i) k) := by
  have hh := ((hf.differentiable (by simp) _).hasFDerivAt.comp x
    (labeled d n p).hasFDerivAt).fderiv
  change fderiv ℝ (f ∘ labeled d n p) x _ = _
  rw [hh, ContinuousLinearMap.comp_apply]
  exact congrArg _ (labeled_vector d n p i k)

private lemma differential_relabel (d n : ℕ) (p : Fin d ≃ Fin n)
    (f : KPArch.Space n → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : HyperbolicChart.Space d) (i : Fin d) (k : Fin 3) :
    HyperbolicChart.differential d (f ∘ labeled d n p) x i k =
      HyperbolicChart.differential n (f ∘ CotangentLogCoframe.A n)
        ((CotangentLogCoframe.A n).symm (labeled d n p x)) (p i) k := by
  have hrefl : labeled n n (Equiv.refl _) = CotangentLogCoframe.A n := by
    apply ContinuousLinearEquiv.ext
    funext y j
    exact labeled_apply n n (Equiv.refl _) y j
  have hheight : ((CotangentLogCoframe.A n).symm (labeled d n p x)) (p i, 2) = x (i, 2) := by
    have h := congrArg (fun z : KPArch.Space n => (z (p i)).2)
      ((CotangentLogCoframe.A n).apply_symm_apply (labeled d n p x))
    simpa [CotangentLogCoframe.A_apply, labeled_apply] using h
  unfold HyperbolicChart.differential
  fin_cases k <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  all_goals rw [labeled_first d n p f hf]
  all_goals rw [← hrefl, labeled_first n n (Equiv.refl _) f hf]
  all_goals simp only [hrefl, ContinuousLinearEquiv.apply_symm_apply, Equiv.refl_apply, hheight]
  all_goals simp
  all_goals rw [labeled_first d n p f hf, ← hrefl, labeled_first n n (Equiv.refl _) f hf]
  all_goals simp [hrefl]

private lemma differential_norm_relabel (d n : ℕ) (p : Fin d ≃ Fin n)
    (f : KPArch.Space n → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : HyperbolicChart.Space d) :
    ‖CotangentLogCoframe.j d (HyperbolicChart.differential d (f ∘ labeled d n p) x)‖ =
      Real.sqrt (∑ i : Fin n, ∑ k : Fin 3,
        ‖HyperbolicChart.differential n (f ∘ CotangentLogCoframe.A n)
          ((CotangentLogCoframe.A n).symm (labeled d n p x)) i k‖ ^ 2) := by
  rw [PiLp.norm_eq_of_L2]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [CotangentLogCoframe.j_apply, differential_relabel d n p f hf]
  exact Equiv.sum_comp p (fun i : Fin n => ∑ k : Fin 3,
    ‖HyperbolicChart.differential n (f ∘ CotangentLogCoframe.A n)
      ((CotangentLogCoframe.A n).symm (labeled d n p x)) i k‖ ^ 2)
private theorem cutoff_lift_germ (r : Cutoffs (U := U) (H := H)) (n : ℕ)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    liftExtension a (cutoffLift (realCutoff r n) a) =ᶠ[nhds x.val]
      (fun y => (r.rho n (KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex U
        (H.atlas U) a.component (labeled (d F) (KPCuspLogShape.dimension F) (placeEquiv F ζ hζ) y)) : ℂ)) := by
  have hopen : IsOpen (omega a) := a.domain_open.preimage (by unfold labeledA; fun_prop)
  filter_upwards [hopen.mem_nhds x.property] with y hy
  simp only [liftExtension, dite_true, hy, cutoffLift, realCutoff]
  congr 1

private theorem differential_congr {d : ℕ} {f g : HyperbolicChart.Space d → ℂ}
    {x : HyperbolicChart.Space d} (h : f =ᶠ[nhds x] g) :
    HyperbolicChart.differential d f x = HyperbolicChart.differential d g x := by
  have hf := h.fderiv_eq (𝕜 := ℝ)
  funext i k
  simp only [HyperbolicChart.differential, HyperbolicChart.coordinateDerivative, hf]

private theorem actual_cutoff_bounds (r : Cutoffs (U := U) (H := H)) :
    ∀ (n : ℕ) (a : ActualChart (U := U) (H := H)) (x : omega a),
      ‖cutoffDifferential (realCutoff r n) a x‖ +
        ‖HyperbolicChart.laplacian (d F) (liftExtension a (cutoffLift (realCutoff r n) a)) x.val‖ ≤ r.bound := by
  intro n a x
  let f : KPArch.Space (KPCuspLogShape.dimension F) → ℂ := fun z =>
    (r.rho n (KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex U (H.atlas U) a.component z) : ℂ)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := Complex.ofRealCLM.contDiff.comp (r.smooth n a.component)
  let z := labeled (d F) (KPCuspLogShape.dimension F) (placeEquiv F ζ hζ) x.val
  have hgrad : ‖cutoffDifferential (realCutoff r n) a x‖ =
      KPCuspCutoffGraph.scalarGradientNorm F ζ hζ H.totallyComplex U (H.atlas U) (r.rho n) a.component z := by
    unfold cutoffDifferential chartDifferential
    rw [differential_congr (cutoff_lift_germ r n a x)]
    have hA : (CotangentLogCoframe.A (KPCuspLogShape.dimension F) : HyperbolicChart.Space (KPCuspLogShape.dimension F) → KPArch.Space (KPCuspLogShape.dimension F)) = KPCuspCutoffGraph.toArch F := by
      funext y j
      apply Prod.ext
      · apply Complex.ext <;> simp [CotangentLogCoframe.A_apply, KPCuspCutoffGraph.toArch]
      · rfl
    have hAi : (CotangentLogCoframe.A (KPCuspLogShape.dimension F)).symm z = KPCuspCutoffGraph.fromArch F z := by rfl
    have hv := differential_norm_relabel _ _ (placeEquiv F ζ hζ) f hf x.val
    change _ = Real.sqrt (∑ i, ∑ k, ‖HyperbolicChart.differential _
      (f ∘ CotangentLogCoframe.A _) ((CotangentLogCoframe.A _).symm z) i k‖ ^ 2) at hv
    rw [hAi] at hv
    rw [hA] at hv
    exact hv
  have hlap : HyperbolicChart.laplacian (d F) (liftExtension a (cutoffLift (realCutoff r n) a)) x.val =
      KPCuspCutoffGraph.scalarLaplacian F ζ hζ H.totallyComplex U (H.atlas U) (r.rho n) a.component z := by
    rw [KPCuspCutoffGraphApproximation.laplacian_congr_nhds (d F) (cutoff_lift_germ r n a x)]
    have hb := KPContArchLaplacianCoordinateBridge.bridge_equiv (d F) (KPCuspLogShape.dimension F)
      (placeEquiv F ζ hζ) f hf x.val
    have hc := KPContArchLaplacianCoordinateBridge.bridge F f hf z
    change KPContActualSphericalFlatStage.localLaplacian _ f z = _ at hb
    have hfun : (fun y => f (fun k => CotangentLogCoframe.A (d F) y ((placeEquiv F ζ hζ).symm k))) =
        f ∘ labeled (d F) (KPCuspLogShape.dimension F) (placeEquiv F ζ hζ) := by
      funext y
      congr 1
    rw [hfun] at hb
    change HyperbolicChart.laplacian _ (f ∘ labeled _ _ _) x.val = _
    rw [← hb, hc]
    rfl
  rw [hgrad, hlap]
  exact r.derivative_bound n a.component z

variable (F ζ hζ) (U R P H)
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

local notation "Δ" => KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization

private theorem local_laplacian_chart_local (w : SmoothSection (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    sectionFields (localLaplacian w) a x =
      HyperbolicChart.laplacian (d F) (liftExtension a (sectionFields w.val a)) x.val := by
  have he : liftExtension a (sectionFields w.val a) =ᶠ[nhds x.val]
      fun y => (w.val a.component).val (labeledA (placeEquiv F ζ hζ) y) := by
    have ho : IsOpen (omega a) := a.domain_open.preimage
      contDiff_labeledA.continuous
    filter_upwards [ho.mem_nhds x.property] with y hy
    simp only [liftExtension, dif_pos hy]
    simp [sectionFields, KPContCotangentActualOverlap.LiftedChart.coefficient,
      KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative]
  rw [KPCuspCutoffGraphApproximation.laplacian_congr_nhds (d F) he]
  have hb := KPContArchLaplacianCoordinateBridge.bridge_equiv (d F)
    (KPCuspLogShape.dimension F) (placeEquiv F ζ hζ)
    (w.val a.component).val (w.property a.component) x.val
  simp only [sectionFields, localLaplacian, KPCuspCutoffGraph.localLaplacianSection,
    KPContCotangentActualOverlap.LiftedChart.coefficient, KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
    ChartKind.representative, map_one, Units.val_one, one_mul, one_smul]
  rw [show KPCuspCutoffGraph.localLaplacianComplex F ζ hζ H.totallyComplex U (H.atlas U)
        w.val a.component (labeledA (placeEquiv F ζ hζ) x.val) =
      KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
        (w.val a.component).val (labeledA (placeEquiv F ζ hζ) x.val) from
    (KPContArchLaplacianCoordinateBridge.bridge F (w.val a.component).val
      (w.property a.component) (labeledA (placeEquiv F ζ hζ) x.val)).symm]
  exact hb

private theorem test_action_local
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (r : Cutoffs (U := U) (H := H)) (n : ℕ) (w : SmoothSection (U := U) (H := H)) :
    (graphPair μG hμG hR realization r n w).2 = iota (δ_U (D_U (cutoffTest r n w))) :=
  (kp_cont_actual_sector_test_friedrichs F ζ hζ μG hμG U R hR P H
    realization).friedrichs.test_laplacian (cutoffTest r n w)

private theorem norm_j_differential (d : ℕ) (f : HyperbolicChart.Space d → ℂ)
    (x : HyperbolicChart.Space d) :
    ‖CotangentLogCoframe.j d (HyperbolicChart.differential d f x)‖ =
      Real.sqrt (∑ i : Fin d, ∑ k : Fin 3, ‖HyperbolicChart.differential d f x i k‖ ^ 2) := by
  rw [PiLp.norm_eq_of_L2, Fintype.sum_prod_type]
  rfl

include μG hμG hR realization in

theorem cutoff_commutator_bound (r : Cutoffs (U := U) (H := H))
    (w : SmoothSection (U := U) (H := H)) (n : ℕ)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    ‖(δ_U (D_U (cutoffTest r n w))).val a x -
        cutoffLift (realCutoff r n) a x * sectionFields (localLaplacian w) a x‖ ≤
      r.bound * (‖sectionFields w.val a x‖ +
        2 * ‖coefficient (gradient w) a x‖) := by
  let f : M F → ℂ := fun y =>
    (r.rho n (KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex U (H.atlas U)
      a.component (labeledA (placeEquiv F ζ hζ) y)) : ℂ)
  let g : M F → ℂ := fun y => (w.val a.component).val (labeledA (placeEquiv F ζ hζ) y)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    Complex.ofRealCLM.contDiff.comp ((r.smooth n a.component).comp contDiff_labeledA)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := (w.property a.component).comp contDiff_labeledA
  have hfgerm : liftExtension a (cutoffLift (realCutoff r n) a) =ᶠ[nhds x.val] f :=
    cutoff_lift_germ r n a x
  have hggerm : liftExtension a (sectionFields w.val a) =ᶠ[nhds x.val] g := by
    filter_upwards [(isOpen_omega a).mem_nhds x.property] with y hy
    simp [liftExtension, hy, sectionFields, g, KPContCotangentActualOverlap.LiftedChart.coefficient,
      KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative]
  have hprod : liftExtension a ((cutoffTest r n w).val a) =ᶠ[nhds x.val] fun y => f y * g y := by
    filter_upwards [hfgerm, hggerm, (isOpen_omega a).mem_nhds x.property] with y hfy hgy hy
    simp only [liftExtension, dite_eq_left hy, cutoffTest] at hfy hgy ⊢
    rw [← hfy, ← hgy]
  have hpointf : f x.val = cutoffLift (realCutoff r n) a x := by
    simpa only [liftExtension, dite_eq_left x.property] using hfgerm.eq_of_nhds.symm
  have hpointg : g x.val = sectionFields w.val a x := by
    simpa only [liftExtension, dite_eq_left x.property] using hggerm.eq_of_nhds.symm
  have hnormf : Real.sqrt (∑ i, ∑ k, ‖HyperbolicChart.differential (d F) f x.val i k‖ ^ 2) =
      ‖cutoffDifferential (realCutoff r n) a x‖ := by
    rw [← norm_j_differential]
    unfold cutoffDifferential chartDifferential
    rw [differential_congr hfgerm]
  have hnormg : Real.sqrt (∑ i, ∑ k, ‖HyperbolicChart.differential (d F) g x.val i k‖ ^ 2) =
      ‖coefficient (gradient w) a x‖ := by
    rw [← norm_j_differential]
    change _ = ‖CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F)
      (liftExtension a (sectionFields w.val a)) x.val)‖
    rw [differential_congr hggerm]
  have hbound := actual_cutoff_bounds r n a x
  have hlf := KPCuspCutoffGraphApproximation.laplacian_congr_nhds (d F) hfgerm
  have hlg := KPCuspCutoffGraphApproximation.laplacian_congr_nhds (d F) hggerm
  rw [(kp_cont_actual_sector_test_differential_descent F ζ hζ μG hμG U R hR P H realization).laplacian_chart,
    local_laplacian_chart_local F ζ hζ U R P H, KPCuspCutoffGraphApproximation.laplacian_congr_nhds (d F) hprod,
    hlg, ← hpointf]
  have he := KPCuspCutoffGraphApproximation.cutoff_hyperbolic_laplacian_error_bound (d F) f g hf hg x.val
  rw [hpointg, hnormf, hnormg, ← hlf] at he
  refine he.trans ?_
  have hd : ‖cutoffDifferential (realCutoff r n) a x‖ ≤ r.bound := by
    linarith [norm_nonneg (HyperbolicChart.laplacian (d F)
      (liftExtension a (cutoffLift (realCutoff r n) a)) x.val)]
  have hl : ‖HyperbolicChart.laplacian (d F)
      (liftExtension a (cutoffLift (realCutoff r n) a)) x.val‖ ≤ r.bound := by
    linarith [norm_nonneg (cutoffDifferential (realCutoff r n) a x)]
  nlinarith [norm_nonneg (sectionFields w.val a x), norm_nonneg (coefficient (gradient w) a x)]

 def rawCutoffs (r : Cutoffs (U := U) (H := H)) :
    KPCuspCutoffGraphApproximation.Cutoffs F ζ hζ H.totallyComplex U (H.atlas U) where
  rho := r.rho
  smooth := r.smooth
  compact_support := r.compact_support
  nonnegative := r.nonnegative
  le_one := r.le_one
  height_bound := r.height_bound
  above_atlas_threshold := r.above_atlas_threshold
  on_core := r.on_core
  on_sublevel := r.on_sublevel
  above_next := r.above_next
  bound := r.bound
  bound_nonnegative := r.bound_nonnegative
  derivative_bound := r.derivative_bound

include μG hμG hR realization in

theorem cutoff_next_laplacian_eq_off_tail (r : Cutoffs (U := U) (H := H))
    (w : SmoothSection (U := U) (H := H)) (n : ℕ) (hn : r.height_bound ≤ n)
    (a : ActualChart (U := U) (H := H)) (x : omega a)
    (hx : q a x.val ∉ KPCuspCutoffGraph.highEnds F ζ hζ H.totallyComplex U (H.atlas U) n) :
    (δ_U (D_U (cutoffTest r (n+1) w))).val a x = sectionFields (localLaplacian w) a x := by
  have he := KPCuspCutoffGraphApproximation.cutoff_next_eventually_one F ζ hζ H.totallyComplex U (H.atlas U)
    (rawCutoffs F ζ hζ U R P H r) n hn a.component (labeledA (placeEquiv F ζ hζ) x.val) hx
  have hA : Continuous (labeledA (placeEquiv F ζ hζ) : M F → KPCuspGenuineMonodromy.SymmetricSpace F) :=
    contDiff_labeledA.continuous
  have hprod : liftExtension a ((cutoffTest r (n+1) w).val a) =ᶠ[nhds x.val]
      liftExtension a (sectionFields w.val a) := by
    filter_upwards [hA.continuousAt.eventually he, (isOpen_omega a).mem_nhds x.property] with y hy hyo
    simp only [liftExtension, dite_eq_left hyo, cutoffTest]
    have hcut : cutoffLift (realCutoff r (n+1)) a ⟨y,hyo⟩ = 1 := by
      change (r.rho (n+1) (KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex U (H.atlas U)
        a.component (labeledA (placeEquiv F ζ hζ) y)) : ℂ) = 1
      have hyr : r.rho (n+1) (KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex U (H.atlas U)
          a.component (labeledA (placeEquiv F ζ hζ) y)) = 1 := hy
      rw [hyr, Complex.ofReal_one]
    rw [hcut, one_mul]
  rw [(kp_cont_actual_sector_test_differential_descent F ζ hζ μG hμG U R hR P H realization).laplacian_chart,
    local_laplacian_chart_local F ζ hζ U R P H, KPCuspCutoffGraphApproximation.laplacian_congr_nhds (d F) hprod]

include μG hμG hR realization in

theorem cutoff_laplacian_eventually_eq (r : Cutoffs (U := U) (H := H))
    (w : SmoothSection (U := U) (H := H)) (a : ActualChart (U := U) (H := H)) (x : omega a) :
    ∀ᶠ n : ℕ in Filter.atTop, (δ_U (D_U (cutoffTest r n w))).val a x =
      sectionFields (localLaplacian w) a x := by
  have hev := KPCuspCutoffGraphApproximation.ExhaustionGeometry.eventually_not_highEnds F ζ hζ H.totallyComplex U
    (H.atlas U) (q a x.val)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  filter_upwards [Filter.eventually_ge_atTop (max N r.height_bound + 1)] with n hn
  have hnn : n = (n-1)+1 := by omega
  rw [hnn]
  exact cutoff_next_laplacian_eq_off_tail F ζ hζ U R P H μG hμG hR realization r w (n-1)
    (by omega) a x (hN (n-1) (by omega))

private theorem sectionNorm_chart (s : Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    sectionNorm F ζ hζ U R P H s (q a x.val) = ‖sectionFields s a x‖ := by
  have he : q a x.val = (H.atlas U).components
      ⟨a.component, Quotient.mk _ (labeledA (placeEquiv F ζ hζ) x.val)⟩ :=
    ((H.atlas U).components_formula _ _).symm
  rw [he, sectionNorm_component]
  simp [sectionFields, KPContCotangentActualOverlap.LiftedChart.coefficient,
    KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative]

private theorem chart_at_base (b : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ (a : ActualChart (U := U) (H := H)) (x : omega a), q a x.val = b := by
  obtain ⟨cover⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  have hb : b ∈ ⋃ n, (cover.chart n).baseDomain := by rw [cover.covers]; trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hb
  obtain ⟨y, hy⟩ := hn
  refine ⟨cover.chart n, KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y, ?_⟩
  have hc : labeledA (placeEquiv F ζ hζ)
      (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y).val = y.val := by
    funext k
    simp [KPContActualCotangentPieceHilbertSum.coordinates, labeledA, labeledAInv]
  change KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative (cover.chart n).component)
    (KPCuspSiegel.projection F _ (labeledA (placeEquiv F ζ hζ)
      (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y).val)) = b
  rw [hc]
  exact hy

private theorem fields_scalarSections (f : S_U F ζ hζ U R P H) :
    sectionFields (scalarSections f) = f.val := (Classical.choose_spec (scalar_gluing f)).1.2.2

 def testBorel (f : S_U F ζ hζ U R P H) : BorelL2Sections F ζ hζ U R P H :=
  ⟨scalarSections f, ⟨fun i => ((Classical.choose_spec (scalar_gluing f)).1.1 i).continuous.measurable,
    (finite_integral_iff F ζ hζ U R P H _ (fun i =>
      ((Classical.choose_spec (scalar_gluing f)).1.1 i).continuous.measurable)).mpr (scalar_memLp f)⟩⟩

private theorem toSector_test (f : S_U F ζ hζ U R P H) :
    toSector F ζ hζ U R P H (testBorel F ζ hζ U R P H f) = iota f := by
  apply Subtype.ext
  rfl

private theorem toSector_norm_sq (s : BorelL2Sections F ζ hζ U R P H) :
    ‖toSector F ζ hζ U R P H s‖ ^ 2 = (normIntegral F ζ hζ U R P H s.val).toReal :=
  norm_sq F ζ hζ U R P H s

include μG hμG hR realization in
private theorem error_norm_at_base (r : Cutoffs (U := U) (H := H))
    (w : SmoothSection (U := U) (H := H)) (n : ℕ) (b : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    sectionNorm F ζ hζ U R P H (scalarSections (δ_U (D_U (cutoffTest r n w))) - localLaplacian w) b ≤
      (2 * r.bound + 1) * (sectionNorm F ζ hζ U R P H w.val b +
        Real.sqrt (normSquare (gradient w) b : ℝ) +
        sectionNorm F ζ hζ U R P H (localLaplacian w) b) := by
  obtain ⟨a, x, rfl⟩ := chart_at_base F ζ hζ U R P H b
  rw [sectionNorm_chart F ζ hζ U R P H, sectionNorm_chart F ζ hζ U R P H,
    sectionNorm_chart F ζ hζ U R P H, normSquare_chart]
  have hsq : Real.sqrt ((‖coefficient (gradient w) a x‖₊ ^ 2 : NNReal) : ℝ) =
      ‖coefficient (gradient w) a x‖ := by
    simp only [NNReal.coe_pow, coe_nnnorm]
    exact Real.sqrt_sq (norm_nonneg _)
  rw [hsq]
  change ‖sectionFields (scalarSections (δ_U (D_U (cutoffTest r n w))) - localLaplacian w) a x‖ ≤ _
  have he : sectionFields (scalarSections (δ_U (D_U (cutoffTest r n w))) - localLaplacian w) a x =
      (δ_U (D_U (cutoffTest r n w))).val a x - sectionFields (localLaplacian w) a x := by
    have hh := congrArg (fun z : ScalarFields F ζ hζ U R P H => z a x)
      (fields_scalarSections F ζ hζ U R P H (δ_U (D_U (cutoffTest r n w))))
    have hs : sectionFields (scalarSections (δ_U (D_U (cutoffTest r n w))) - localLaplacian w) a x =
        sectionFields (scalarSections (δ_U (D_U (cutoffTest r n w)))) a x -
          sectionFields (localLaplacian w) a x := by
      simp [sectionFields, KPContCotangentActualOverlap.LiftedChart.coefficient,
        KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative]
    rw [hs, hh]
  rw [he]
  have h := cutoff_commutator_bound F ζ hζ U R P H μG hμG hR realization r w n a x
  have hρ : ‖cutoffLift (realCutoff r n) a x - 1‖ ≤ 1 := by
    change ‖(r.rho n (q a x.val) : ℂ) - 1‖ ≤ 1
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [r.nonnegative n (q a x.val)], by linarith [r.le_one n (q a x.val)]⟩
  calc
    _ = ‖((δ_U (D_U (cutoffTest r n w))).val a x -
          cutoffLift (realCutoff r n) a x * sectionFields (localLaplacian w) a x) +
        (cutoffLift (realCutoff r n) a x - 1) * sectionFields (localLaplacian w) a x‖ := by congr 1; ring
    _ ≤ r.bound * (‖sectionFields w.val a x‖ + 2 * ‖coefficient (gradient w) a x‖) +
        ‖sectionFields (localLaplacian w) a x‖ := by
      exact (norm_add_le _ _).trans (add_le_add h (by rw [norm_mul]; nlinarith [norm_nonneg (sectionFields (localLaplacian w) a x)]))
    _ ≤ _ := by nlinarith [r.bound_nonnegative, norm_nonneg (sectionFields w.val a x),
      norm_nonneg (coefficient (gradient w) a x), norm_nonneg (sectionFields (localLaplacian w) a x)]

 def lapError (r : Cutoffs (U := U) (H := H)) (w : GraphSection (U := U) (H := H)) (n : ℕ) :
    BorelL2Sections F ζ hζ U R P H := testBorel F ζ hζ U R P H (δ_U (D_U (cutoffTest r n w.val))) -
      ⟨localLaplacian w.val, ⟨fun i => measurable_localLaplacianComplex w.val.val w.val.property i, w.property.2.2⟩⟩

private theorem fields_sub (s t : Sections F ζ hζ U R P H) (a : ActualChart (U := U) (H := H)) (x : omega a) :
    sectionFields (s-t) a x = sectionFields s a x - sectionFields t a x := by
  simp [sectionFields, KPContCotangentActualOverlap.LiftedChart.coefficient,
    KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative]

include μG hμG hR realization in
private theorem lapError_zero_off (r : Cutoffs (U := U) (H := H)) (w : GraphSection (U := U) (H := H))
    (n : ℕ) (hn : r.height_bound ≤ n) (b : KPFiniteCuspAtlas.rawXU F ζ hζ U)
    (hb : b ∉ KPCuspCutoffGraph.highEnds F ζ hζ H.totallyComplex U (H.atlas U) n) :
    squaredNorm F ζ hζ U R P H (lapError F ζ hζ U R P H r w (n+1)).val b = 0 := by
  obtain ⟨a,x,rfl⟩ := chart_at_base F ζ hζ U R P H b
  unfold squaredNorm
  rw [sectionNorm_chart F ζ hζ U R P H]
  change ENNReal.ofReal (‖sectionFields (scalarSections (δ_U (D_U (cutoffTest r (n+1) w.val))) -
    localLaplacian w.val) a x‖ ^ 2) = 0
  rw [fields_sub F ζ hζ U R P H]
  have hf := congrArg (fun z : ScalarFields F ζ hζ U R P H => z a x)
    (fields_scalarSections F ζ hζ U R P H (δ_U (D_U (cutoffTest r (n+1) w.val))))
  rw [hf, cutoff_next_laplacian_eq_off_tail F ζ hζ U R P H μG hμG hR realization r w.val n hn a x hb]
  simp

 def threeSquares (w : GraphSection (U := U) (H := H)) (b : KPFiniteCuspAtlas.rawXU F ζ hζ U) : ℝ≥0∞ :=
  squaredNorm F ζ hζ U R P H w.val.val b + (normSquare (gradient w.val) b : ℝ≥0∞) +
    squaredNorm F ζ hζ U R P H (localLaplacian w.val) b

private theorem threeSquares_finite (w : GraphSection (U := U) (H := H)) :
    (∫⁻ b, threeSquares F ζ hζ U R P H w b ∂(baseMeasure (U := U) (R := R) (P := P))) < ⊤ := by
  unfold threeSquares
  have hm := squaredNorm_measurable F ζ hζ U R P H w.val.val (fun i => (w.val.property i).continuous.measurable)
  have hgme : Measurable (fun b => (normSquare (gradient w.val) b : ℝ≥0∞)) :=
    (measurable_normSquare (gradient w.val)).coe_nnreal_ennreal
  rw [lintegral_add_left (show Measurable (fun b => squaredNorm F ζ hζ U R P H w.val.val b +
    (normSquare (gradient w.val) b : ℝ≥0∞)) from hm.add hgme), lintegral_add_left hm]
  have hg : (∫⁻ b, (normSquare (gradient w.val) b : ℝ≥0∞) ∂baseMeasure (U := U) (R := R) (P := P)) < ⊤ := by
    simpa only [squareFinite, ENNReal.ofReal_coe_nnreal] using w.property.2.1
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨w.property.1, hg⟩, w.property.2.2⟩

include μG hμG hR realization in
private theorem lapError_bound (r : Cutoffs (U := U) (H := H)) (w : GraphSection (U := U) (H := H))
    (n : ℕ) (b : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    squaredNorm F ζ hζ U R P H (lapError F ζ hζ U R P H r w n).val b ≤
      ENNReal.ofReal (3*(2*r.bound+1)^2) * threeSquares F ζ hζ U R P H w b := by
  let A := sectionNorm F ζ hζ U R P H w.val.val b
  let B := Real.sqrt (normSquare (gradient w.val) b : ℝ)
  let D := sectionNorm F ζ hζ U R P H (localLaplacian w.val) b
  let Z := sectionNorm F ζ hζ U R P H (lapError F ζ hζ U R P H r w n).val b
  have hz : 0 ≤ Z := by
    change 0 ≤ sectionNorm F ζ hζ U R P H (lapError F ζ hζ U R P H r w n).val b
    obtain ⟨a,x,rfl⟩ := chart_at_base F ζ hζ U R P H b
    rw [sectionNorm_chart F ζ hζ U R P H]
    exact norm_nonneg _
  have he : Z ≤ (2*r.bound+1)*(A+B+D) := error_norm_at_base F ζ hζ U R P H μG hμG hR realization r w.val n b
  have hs : Z^2 ≤ (3*(2*r.bound+1)^2)*(A^2+B^2+D^2) := by
    have hh : (A+B+D)^2 ≤ 3*(A^2+B^2+D^2) := by nlinarith [sq_nonneg (A-B), sq_nonneg (A-D), sq_nonneg (B-D)]
    nlinarith [r.bound_nonnegative, sq_nonneg (2*r.bound+1), sq_nonneg (Z+(2*r.bound+1)*(A+B+D))]
  have hB : B^2 = (normSquare (gradient w.val) b : ℝ) := Real.sq_sqrt (NNReal.coe_nonneg _)
  have hen := ENNReal.ofReal_le_ofReal hs
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (sq_nonneg _),
    ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), hB, ENNReal.ofReal_coe_nnreal] at hen
  exact hen

 def scalarError (r : Cutoffs (U := U) (H := H)) (w : GraphSection (U := U) (H := H)) (n : ℕ) :
    BorelL2Sections F ζ hζ U R P H := testBorel F ζ hζ U R P H (cutoffTest r n w.val) -
      ⟨w.val.val, ⟨fun i => (w.val.property i).continuous.measurable, w.property.1⟩⟩

private theorem scalarError_formula (r : Cutoffs (U := U) (H := H)) (w : GraphSection (U := U) (H := H))
    (n : ℕ) (a : ActualChart (U := U) (H := H)) (x : omega a) :
    sectionFields (scalarError F ζ hζ U R P H r w n).val a x =
      ((r.rho n (q a x.val) : ℂ)-1)*sectionFields w.val.val a x := by
  change sectionFields (scalarSections (cutoffTest r n w.val) - w.val.val) a x = _
  rw [fields_sub F ζ hζ U R P H]
  have hf := congrArg (fun z : ScalarFields F ζ hζ U R P H => z a x)
    (fields_scalarSections F ζ hζ U R P H (cutoffTest r n w.val))
  rw [hf]
  change (r.rho n (q a x.val) : ℂ)*_ - _ = _
  ring

private theorem scalarError_bound (r : Cutoffs (U := U) (H := H)) (w : GraphSection (U := U) (H := H))
    (n : ℕ) (b : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    squaredNorm F ζ hζ U R P H (scalarError F ζ hζ U R P H r w n).val b ≤
      squaredNorm F ζ hζ U R P H w.val.val b := by
  obtain ⟨a,x,rfl⟩ := chart_at_base F ζ hζ U R P H b
  unfold squaredNorm
  rw [sectionNorm_chart F ζ hζ U R P H, sectionNorm_chart F ζ hζ U R P H,
    scalarError_formula F ζ hζ U R P H, norm_mul]
  have hr : ‖(r.rho n (q a x.val) : ℂ)-1‖ ≤ 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [r.nonnegative n (q a x.val)], by linarith [r.le_one n (q a x.val)]⟩
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (by simpa using mul_le_mul_of_nonneg_right hr (norm_nonneg (sectionFields w.val.val a x))) 2

private theorem scalarError_zero_off (r : Cutoffs (U := U) (H := H)) (w : GraphSection (U := U) (H := H))
    (n : ℕ) (hn : r.height_bound ≤ n) (b : KPFiniteCuspAtlas.rawXU F ζ hζ U)
    (hb : b ∉ KPCuspCutoffGraph.highEnds F ζ hζ H.totallyComplex U (H.atlas U) n) :
    squaredNorm F ζ hζ U R P H (scalarError F ζ hζ U R P H r w n).val b = 0 := by
  obtain ⟨a,x,rfl⟩ := chart_at_base F ζ hζ U R P H b
  unfold squaredNorm
  rw [sectionNorm_chart F ζ hζ U R P H, scalarError_formula F ζ hζ U R P H,
    r.on_sublevel n hn _ hb]
  simp

private theorem norm_tendsto_of_integral (e : ℕ → BorelL2Sections F ζ hζ U R P H)
    (he : Filter.Tendsto (fun n => normIntegral F ζ hζ U R P H (e n).val) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ‖toSector F ζ hζ U R P H (e n)‖) Filter.atTop (nhds 0) := by
  have ht := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp he
  have hs := (Real.continuous_sqrt.tendsto (0:ℝ)).comp ht
  simpa only [Function.comp_def, ENNReal.toReal_zero, Real.sqrt_zero,
    ← toSector_norm_sq F ζ hζ U R P H, Real.sqrt_sq (norm_nonneg _)] using hs

include μG hμG hR realization in
private theorem error_integral_tendsto (r : Cutoffs (U := U) (H := H)) (w : GraphSection (U := U) (H := H)) :
    Filter.Tendsto (fun n => normIntegral F ζ hζ U R P H (scalarError F ζ hζ U R P H r w n).val)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => normIntegral F ζ hζ U R P H (lapError F ζ hζ U R P H r w n).val)
      Filter.atTop (nhds 0) := by
  have hscalar : ∀ b, ∀ᶠ n : ℕ in Filter.atTop,
      squaredNorm F ζ hζ U R P H (scalarError F ζ hζ U R P H r w n).val b = 0 := by
    intro b
    filter_upwards [Filter.eventually_ge_atTop r.height_bound,
      KPCuspCutoffGraphApproximation.ExhaustionGeometry.eventually_not_highEnds F ζ hζ H.totallyComplex U (H.atlas U) b] with n hn hb
    exact scalarError_zero_off F ζ hζ U R P H r w n hn b hb
  have hlap : ∀ b, ∀ᶠ n : ℕ in Filter.atTop,
      squaredNorm F ζ hζ U R P H (lapError F ζ hζ U R P H r w n).val b = 0 := by
    intro b
    obtain ⟨a,x,rfl⟩ := chart_at_base F ζ hζ U R P H b
    filter_upwards [cutoff_laplacian_eventually_eq F ζ hζ U R P H μG hμG hR realization r w.val a x] with n hn
    unfold squaredNorm
    rw [sectionNorm_chart F ζ hζ U R P H]
    change ENNReal.ofReal (‖sectionFields (scalarSections (δ_U (D_U (cutoffTest r n w.val))) - localLaplacian w.val) a x‖^2) = 0
    rw [fields_sub F ζ hζ U R P H]
    have hf := congrArg (fun z : ScalarFields F ζ hζ U R P H => z a x)
      (fields_scalarSections F ζ hζ U R P H (δ_U (D_U (cutoffTest r n w.val))))
    rw [hf, hn]
    simp
  constructor
  · have ht := tendsto_lintegral_of_dominated_convergence
      (μ := baseMeasure (U := U) (R := R) (P := P))
      (squaredNorm F ζ hζ U R P H w.val.val)
      (fun n => squaredNorm_measurable F ζ hζ U R P H _ (scalarError F ζ hζ U R P H r w n).property.1)
      (fun n => Filter.Eventually.of_forall (scalarError_bound F ζ hζ U R P H r w n))
      (ne_of_lt w.property.1)
      (Filter.Eventually.of_forall (fun b => tendsto_const_nhds.congr' ((hscalar b).mono (fun n hn => hn.symm))))
    simpa only [normIntegral, lintegral_zero] using ht
  · have hfin : (∫⁻ b, ENNReal.ofReal (3*(2*r.bound+1)^2)*threeSquares F ζ hζ U R P H w b
        ∂baseMeasure (U := U) (R := R) (P := P)) ≠ ⊤ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (threeSquares_finite F ζ hζ U R P H w))
    have ht := tendsto_lintegral_of_dominated_convergence
      (μ := baseMeasure (U := U) (R := R) (P := P))
      (fun b => ENNReal.ofReal (3*(2*r.bound+1)^2)*threeSquares F ζ hζ U R P H w b)
      (fun n => squaredNorm_measurable F ζ hζ U R P H _ (lapError F ζ hζ U R P H r w n).property.1)
      (fun n => Filter.Eventually.of_forall (lapError_bound F ζ hζ U R P H μG hμG hR realization r w n)) hfin
      (Filter.Eventually.of_forall (fun b => tendsto_const_nhds.congr' ((hlap b).mono (fun n hn => hn.symm))))
    simpa only [normIntegral, lintegral_zero] using ht

include μG hμG hR realization in
private theorem graph_error_classes (r : Cutoffs (U := U) (H := H)) (w : GraphSection (U := U) (H := H)) (n : ℕ) :
    (graphPair μG hμG hR realization r n w.val).1 - sectionClass w =
      toSector F ζ hζ U R P H (scalarError F ζ hζ U R P H r w n) ∧
    (graphPair μG hμG hR realization r n w.val).2 - laplacianClass w =
      toSector F ζ hζ U R P H (lapError F ζ hζ U R P H r w n) := by
  constructor
  · change iota (cutoffTest r n w.val) - toSector F ζ hζ U R P H _ =
      toSector F ζ hζ U R P H (_ - _)
    rw [map_sub (toSector F ζ hζ U R P H), toSector_test]
  · rw [test_action_local F ζ hζ U R P H μG hμG hR realization]
    change iota (δ_U (D_U (cutoffTest r n w.val))) - toSector F ζ hζ U R P H _ =
      toSector F ζ hζ U R P H (_ - _)
    rw [map_sub (toSector F ζ hζ U R P H), toSector_test]

include μG hμG hR realization in
private theorem graph_limit_local (r : Cutoffs (U := U) (H := H)) (w : GraphSection (U := U) (H := H)) :
    Filter.Tendsto (fun n => graphPair μG hμG hR realization r n w.val)
      Filter.atTop (nhds (sectionClass w, laplacianClass w)) := by
  obtain ⟨hs,hl⟩ := error_integral_tendsto F ζ hζ U R P H μG hμG hR realization r w
  apply Filter.Tendsto.prodMk_nhds
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have he := fun n => (graph_error_classes F ζ hζ U R P H μG hμG hR realization r w n).1
    change Filter.Tendsto (fun n => ‖(graphPair μG hμG hR realization r n w.val).1 - sectionClass w‖) _ _
    simp_rw [he]
    exact norm_tendsto_of_integral F ζ hζ U R P H _ hs
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have he := fun n => (graph_error_classes F ζ hζ U R P H μG hμG hR realization r w n).2
    change Filter.Tendsto (fun n => ‖(graphPair μG hμG hR realization r n w.val).2 - laplacianClass w‖) _ _
    simp_rw [he]
    exact norm_tendsto_of_integral F ζ hζ U R P H _ hl

include μG hμG hR realization in
private theorem scalarError_next_zero_off (r : Cutoffs (U := U) (H := H)) (w : GraphSection (U := U) (H := H))
    (n : ℕ) (hn : r.height_bound ≤ n) (b : KPFiniteCuspAtlas.rawXU F ζ hζ U)
    (hb : b ∉ KPCuspCutoffGraph.highEnds F ζ hζ H.totallyComplex U (H.atlas U) n) :
    squaredNorm F ζ hζ U R P H (scalarError F ζ hζ U R P H r w (n+1)).val b = 0 := by
  obtain ⟨a,x,rfl⟩ := chart_at_base F ζ hζ U R P H b
  have he := KPCuspCutoffGraphApproximation.cutoff_next_eventually_one F ζ hζ H.totallyComplex U (H.atlas U)
    (rawCutoffs F ζ hζ U R P H r) n hn a.component (labeledA (placeEquiv F ζ hζ) x.val) hb
  have hr : r.rho (n+1) (q a x.val) = 1 := he.self_of_nhds
  unfold squaredNorm
  rw [sectionNorm_chart F ζ hζ U R P H, scalarError_formula F ζ hζ U R P H, hr]
  simp

include μG hμG hR realization in
private theorem error_tail_bound (r : Cutoffs (U := U) (H := H)) (w : GraphSection (U := U) (H := H))
    (n : ℕ) (hn : r.height_bound ≤ n) :
    normIntegral F ζ hζ U R P H (scalarError F ζ hζ U R P H r w (n+1)).val ≤
      ENNReal.ofReal (3*(2*r.bound+1)^2) *
        ∫⁻ b, threeSquares F ζ hζ U R P H w b
          ∂(baseMeasure (U := U) (R := R) (P := P)).restrict
            (KPCuspCutoffGraph.highEnds F ζ hζ H.totallyComplex U (H.atlas U) n) ∧
    normIntegral F ζ hζ U R P H (lapError F ζ hζ U R P H r w (n+1)).val ≤
      ENNReal.ofReal (3*(2*r.bound+1)^2) *
        ∫⁻ b, threeSquares F ζ hζ U R P H w b
          ∂(baseMeasure (U := U) (R := R) (P := P)).restrict
            (KPCuspCutoffGraph.highEnds F ζ hζ H.totallyComplex U (H.atlas U) n) := by
  let Q := ENNReal.ofReal (3*(2*r.bound+1)^2)
  let s := KPCuspCutoffGraph.highEnds F ζ hζ H.totallyComplex U (H.atlas U) n
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [r.bound_nonnegative]
  have hb (e : BorelL2Sections F ζ hζ U R P H)
      (hz : ∀ b ∉ s, squaredNorm F ζ hζ U R P H e.val b = 0)
      (he : ∀ b, squaredNorm F ζ hζ U R P H e.val b ≤ Q*threeSquares F ζ hζ U R P H w b) :
      normIntegral F ζ hζ U R P H e.val ≤ Q*∫⁻ b in s, threeSquares F ζ hζ U R P H w b
        ∂baseMeasure (U := U) (R := R) (P := P) := by
    calc
      _ ≤ ∫⁻ b, s.indicator (fun b => Q*threeSquares F ζ hζ U R P H w b) b
          ∂baseMeasure (U := U) (R := R) (P := P) := lintegral_mono (fun b => by
            by_cases h : b ∈ s
            · rw [Set.indicator_of_mem h]; exact he b
            · rw [Set.indicator_of_notMem h, hz b h])
      _ ≤ ∫⁻ b in s, Q*threeSquares F ζ hζ U R P H w b
          ∂baseMeasure (U := U) (R := R) (P := P) := lintegral_indicator_le _ _
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  constructor
  · apply hb _ (scalarError_next_zero_off F ζ hζ U R P H μG hμG hR realization r w n hn)
    intro b
    apply (scalarError_bound F ζ hζ U R P H r w (n+1) b).trans
    apply (show squaredNorm F ζ hζ U R P H w.val.val b ≤ threeSquares F ζ hζ U R P H w b from
      (le_add_right le_rfl).trans (le_add_right le_rfl)).trans
    exact le_mul_of_one_le_left' hQ
  · exact hb _ (lapError_zero_off F ζ hζ U R P H μG hμG hR realization r w n hn)
      (lapError_bound F ζ hζ U R P H μG hμG hR realization r w (n+1))

private theorem norm_lt_of_integral_le (e : BorelL2Sections F ζ hζ U R P H) (ε : ℝ) (hε : 0 < ε)
    (he : normIntegral F ζ hζ U R P H e.val ≤ ENNReal.ofReal (ε^2/2)) :
    ‖toSector F ζ hζ U R P H e‖ < ε := by
  have ht := (ENNReal.toReal_le_toReal (ne_of_lt e.property.2) ENNReal.ofReal_ne_top).mpr he
  rw [ENNReal.toReal_ofReal (by positivity), ← toSector_norm_sq F ζ hζ U R P H] at ht
  nlinarith [norm_nonneg (toSector F ζ hζ U R P H e)]

include μG hμG hR realization in
private theorem uniform_graph_limit_local (r : Cutoffs (U := U) (H := H))
    {I : Type*} (w : I → GraphSection (U := U) (H := H)) (hw : ThreeUniformTails w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i : I,
      dist (graphPair μG hμG hR realization r n (w i).val)
        (sectionClass (w i), laplacianClass (w i)) < ε := by
  let Q : ℝ := 3*(2*r.bound+1)^2
  have hQ : 0 < Q := by dsimp [Q]; nlinarith [r.bound_nonnegative]
  let η : ℝ := ε^2/(6*Q)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨Ns,hs⟩ := hw.1 η hη
  obtain ⟨Ng,hg⟩ := hw.2.1 η hη
  obtain ⟨Nl,hl⟩ := hw.2.2 η hη
  refine ⟨max (max Ns Ng) (max Nl r.height_bound)+1, ?_⟩
  intro n hn i
  have hn0 : n = (n-1)+1 := by omega
  have htail : ENNReal.ofReal Q * (∫⁻ b, threeSquares F ζ hζ U R P H (w i) b
      ∂(baseMeasure (U := U) (R := R) (P := P)).restrict
        (KPCuspCutoffGraph.highEnds F ζ hζ H.totallyComplex U (H.atlas U) (n-1 : ℕ))) ≤
      ENNReal.ofReal (ε^2/2) := by
    have hm := squaredNorm_measurable F ζ hζ U R P H (w i).val.val
      (fun j => ((w i).val.property j).continuous.measurable)
    have hgm : Measurable (fun b => (normSquare (gradient (w i).val) b : ℝ≥0∞)) :=
      (measurable_normSquare (gradient (w i).val)).coe_nnreal_ennreal
    unfold threeSquares
    rw [lintegral_add_left (show Measurable (fun b => squaredNorm F ζ hζ U R P H (w i).val.val b +
      (normSquare (gradient (w i).val) b : ℝ≥0∞)) from hm.add hgm), lintegral_add_left hm]
    have hs' := (hs (n-1) (by omega) i).le
    have hg' := (hg (n-1) (by omega) i).le
    have hl' := (hl (n-1) (by omega) i).le
    have hsum := add_le_add (add_le_add hs' hg') hl'
    have hprod := mul_le_mul_right hsum (ENNReal.ofReal Q)
    have hη0 : 0 ≤ η := le_of_lt hη
    have hid : Q*(η+η+η) = ε^2/2 := by dsimp [η]; field_simp; ring
    rw [← ENNReal.ofReal_add hη0 hη0,
      ← ENNReal.ofReal_add (by positivity) hη0, ← ENNReal.ofReal_mul (le_of_lt hQ), hid] at hprod
    exact hprod
  obtain ⟨hes,hel⟩ := error_tail_bound F ζ hζ U R P H μG hμG hR realization r (w i) (n-1) (by omega)
  rw [← hn0] at hes hel
  have hsc := norm_lt_of_integral_le F ζ hζ U R P H _ ε hε (hes.trans htail)
  have hlc := norm_lt_of_integral_le F ζ hζ U R P H _ ε hε (hel.trans htail)
  have hc := graph_error_classes F ζ hζ U R P H μG hμG hR realization r (w i) n
  rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm, hc.1, hc.2]
  exact max_lt hsc hlc

structure Properties (r : Cutoffs (U := U) (H := H)) : Prop where

  local_laplacian_chart : ∀ (w : SmoothSection (U := U) (H := H))
      (a : ActualChart (U := U) (H := H)) (x : omega a),
    sectionFields (localLaplacian w) a x =
      HyperbolicChart.laplacian (d F) (liftExtension a (sectionFields w.val a)) x.val

  actual_derivative_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ)
      (a : ActualChart (U := U) (H := H)) (x : omega a),
    ‖cutoffDifferential (realCutoff r n) a x‖ +
      ‖HyperbolicChart.laplacian (d F) (liftExtension a (cutoffLift (realCutoff r n) a)) x.val‖ ≤ C

  test_action : ∀ (n : ℕ) (w : SmoothSection (U := U) (H := H)),
    (graphPair μG hμG hR realization r n w).2 = iota (δ_U (D_U (cutoffTest r n w)))
  graph_limit : ∀ w : GraphSection (U := U) (H := H),
    Filter.Tendsto (fun n => graphPair μG hμG hR realization r n w.val)
      Filter.atTop (nhds (sectionClass w, laplacianClass w))

  closed_graph_consequence : ∀ w : GraphSection (U := U) (H := H),
    ∃ hw : sectionClass w ∈ (Δ).domain, (Δ) ⟨sectionClass w, hw⟩ = laplacianClass w

  uniform_graph_limit : ∀ {I : Type*} (w : I → GraphSection (U := U) (H := H)),
    ThreeUniformTails w → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i : I,
        dist (graphPair μG hμG hR realization r n (w i).val)
          (sectionClass (w i), laplacianClass (w i)) < ε

end DedekindZetaZeroFree.KPContActualSectorCutoffGraphLimit

namespace DedekindZetaZeroFree

theorem kp_cont_actual_sector_cutoff_graph_limit
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    ∃ r : KPContActualSectorCutoffGraphLimit.Cutoffs (U := U) (H := H),
      KPContActualSectorCutoffGraphLimit.Properties F ζ hζ U R P H μG hμG hR realization r := by
  obtain ⟨r⟩ := KPCuspCutoffGraph.cutoffs_exist F ζ hζ H.totallyComplex U (H.atlas U)
  refine ⟨r, ?_⟩
  exact
    { local_laplacian_chart := fun w a x =>
        KPContActualSectorCutoffGraphLimit.local_laplacian_chart_local
          F ζ hζ U R P H w a x
      actual_derivative_bound := ⟨r.bound, r.bound_nonnegative,
        KPContActualSectorCutoffGraphLimit.actual_cutoff_bounds r⟩
      test_action := fun n w =>
        KPContActualSectorCutoffGraphLimit.test_action_local
          F ζ hζ U R P H μG hμG hR realization r n w
      graph_limit := fun w => KPContActualSectorCutoffGraphLimit.graph_limit_local
        F ζ hζ U R P H μG hμG hR realization r w
      closed_graph_consequence := fun w =>
        KPCuspCutoffGraphApproximation.closed_graph_limit
          (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization)
          (kp_cont_actual_sector_test_friedrichs F ζ hζ μG hμG U R hR P H realization).friedrichs.laplacian_closed
          (fun n => KPContActualSectorCutoffGraphLimit.graphPair μG hμG hR realization r n w.val)
          (fun n => ⟨KPContActualSectorCutoffGraphLimit.cutoff_mem_domain μG hμG hR realization r n w.val, rfl⟩)
          _ _ (KPContActualSectorCutoffGraphLimit.graph_limit_local F ζ hζ U R P H μG hμG hR realization r w)
      uniform_graph_limit := fun w hw ε hε =>
        KPContActualSectorCutoffGraphLimit.uniform_graph_limit_local
          F ζ hζ U R P H μG hμG hR realization r w hw ε hε }

end DedekindZetaZeroFree

end

module

public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.SmoothScalarAndCotangentTests

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescentCalculus

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

private theorem continuous_q (a : ActualChart (U := U) (H := H)) : Continuous (q a) := by
  have hp : Continuous (KPCuspSiegel.projection F
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)) :=
    continuous_quotient_mk'
  have hc : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U
      ((H.atlas U).representative a.component)) := by
    have hh := (H.atlas U).components.continuous.comp (continuous_sigmaMk (i := a.component))
    simpa only [Function.comp_def, (H.atlas U).components_formula] using hh
  exact hc.comp (hp.comp continuous_labeledA_self)

 def scalarDifferentialZeroExtension (a : ActualChart (U := U) (H := H)) (f : omega a → ℂ) : M F → ℂ :=
  fun x => if hx : x ∈ omega a then f ⟨x, hx⟩ else 0

private theorem smooth_zext {a : ActualChart (U := U) (H := H)} {f : omega a → ℂ}
    (hf : SmoothOnLift a f) : ContDiffOn ℝ (⊤ : ℕ∞) (scalarDifferentialZeroExtension a f) (omega a) := by
  obtain ⟨g, hg, he⟩ := hf
  refine hg.congr (f₁ := scalarDifferentialZeroExtension a f) ?_
  intro x hx
  simpa [scalarDifferentialZeroExtension, hx] using (he ⟨x, hx⟩).symm

private theorem smooth_differential {a : ActualChart (U := U) (H := H)} {f : omega a → ℂ}
    (hf : SmoothOnLift a f) : SmoothOnLift a (fun x => CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (scalarDifferentialZeroExtension a f) x.val)) := by
  refine ⟨fun x => CotangentLogCoframe.j (d F)
    (HyperbolicChart.differential (d F) (scalarDifferentialZeroExtension a f) x), ?_, fun _ => rfl⟩
  rw [contDiffOn_piLp]
  rintro ⟨i, k⟩
  have hd := (smooth_zext hf).fderiv_of_isOpen (isOpen_omega a) (m := (⊤ : ℕ∞)) (by simp)
  have hcd (k : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞)
      (HyperbolicChart.coordinateDerivative (d F) i k (scalarDifferentialZeroExtension a f)) (omega a) :=
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

private theorem smooth_mul {a : ActualChart (U := U) (H := H)} {f g : omega a → ℂ}
    (hf : SmoothOnLift a f) (hg : SmoothOnLift a g) :
    SmoothOnLift a (fun x => f x * g x) := by
  obtain ⟨f', hf', he⟩ := hf
  obtain ⟨g', hg', he'⟩ := hg
  exact ⟨fun x => f' x * g' x, hf'.mul hg', fun x => by dsimp; rw [he x, he' x]⟩

private theorem smooth_ofReal {a : ActualChart (U := U) (H := H)} {f : omega a → ℝ}
    (hf : SmoothOnLift a f) : SmoothOnLift a (fun x => (f x : ℂ)) := by
  obtain ⟨g, hg, he⟩ := hf
  exact ⟨fun x => (g x : ℂ), Complex.ofRealCLM.contDiff.comp_contDiffOn hg,
    fun x => by dsimp; rw [he x]⟩

private theorem differential_zero_germ {d : ℕ} {f : HyperbolicChart.Space d → ℂ}
    {x : HyperbolicChart.Space d} (h : f =ᶠ[𝓝 x] 0) :
    HyperbolicChart.differential d f x = 0 := by
  funext i k
  fin_cases k <;> simp [HyperbolicChart.differential, HyperbolicChart.coordinateDerivative,
    h.fderiv_eq]

private theorem differential_support (f : ScalarFields F ζ hζ U R P H)
    (hv : IsMeasurableCotangentFamily (fun a x => CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (scalarDifferentialZeroExtension a (f a)) x.val))) :
    cotangentSupport ⟨_, hv⟩ ⊆ scalarSupport f := by
  apply closure_minimal _ isClosed_closure
  rintro x ⟨a, y, hq, hne⟩
  rw [← hq]
  let A : Set (M F) := {z | ∃ hz : z ∈ omega a, f a ⟨z, hz⟩ ≠ 0}
  have hy : y.val ∈ closure A := by
    by_contra hn
    have he : scalarDifferentialZeroExtension a (f a) =ᶠ[𝓝 y.val] 0 := by
      filter_upwards [(isClosed_closure.isOpen_compl.inter (isOpen_omega a)).mem_nhds
        ⟨hn, y.property⟩] with z hz
      have hzA : z ∉ A := fun h => hz.1 (subset_closure h)
      have hfz : f a ⟨z, hz.2⟩ = 0 := by
        by_contra hfz
        exact hzA ⟨hz.2, hfz⟩
      simp [scalarDifferentialZeroExtension, hz.2, hfz]
    apply hne
    change CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (scalarDifferentialZeroExtension a (f a)) y.val) = 0
    rw [differential_zero_germ he, map_zero]
  have himg := image_closure_subset_closure_image (s := A) (continuous_q a)
  apply closure_mono (t := {x | ∃ (b : ActualChart (U := U) (H := H)) (z : omega b),
    q b z.val = x ∧ f b z ≠ 0}) _ (himg (Set.mem_image_of_mem (q a) hy))
  rintro x ⟨z, ⟨hz, hne⟩, rfl⟩
  exact ⟨a, ⟨z, hz⟩, rfl, hne⟩

private theorem q_isotropy (a : ActualChart (U := U) (H := H)) (γ : Gamma a) (x : M F) :
    q a ((isotropyArrow a γ).psi x) = q a x := by
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U
    ((H.atlas U).representative a.component))
  have hA (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y) = y := by
    funext k
    simp [labeledA, labeledAInv]
  change KPCuspSiegel.projection F _
    (labeledA (placeEquiv F ζ hζ)
      (coordinateMap (isotropyChart a) (isotropyChart a) γ.val.1.val x)) = _
  simp only [coordinateMap, isotropyChart, ChartKind.representative, inv_one,
    one_mul, mul_one, hA]
  apply Quotient.sound
  exact ⟨γ.val.1.val, rfl⟩

private theorem q_branch {a b : ActualChart (U := U) (H := H)} (e : ActualBranch a b)
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
  simp only [coordinateMap, targetChart, isotropyChart, ChartKind.representative,
    inv_one, one_mul, mul_one, hA]
  apply Quotient.sound
  exact ⟨e.gamma, rfl⟩

private theorem scalar_cutoff (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : ∀ a : ActualChart (U := U) (H := H), SmoothOnLift a (fun x => η (q a x.val)))
    (f : S_U F ζ hζ U R P H) :
    (fun a x => (η (q a x.val) : ℂ) * f.val a x) ∈ scalarTests := by
  refine ⟨fun a => smooth_mul (smooth_ofReal (hη a)) (f.property.1 a), ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro a γ x hx
      dsimp
      rw [q_isotropy, f.property.2.1.1 a γ x hx]
      ring
    · intro a b e x hx
      dsimp
      rw [q_branch, f.property.2.1.2 a b e x hx]
      ring
  · apply f.property.2.2.of_isClosed_subset isClosed_closure
    apply closure_mono
    rintro x ⟨a, y, hq, hn⟩
    exact ⟨a, y, hq, (mul_ne_zero_iff.mp hn).2⟩

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
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
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
    DifferentiableAt ℝ (scalarDifferentialZeroExtension a f) x.val :=
  ((smooth_zext hf).differentiableOn (by simp) x.val x.property).differentiableAt
    ((isOpen_omega a).mem_nhds x.property)

private theorem differential_measurable (f : ScalarFields F ζ hζ U R P H)
    (hf : ∀ a, SmoothOnLift a (f a)) (hc : ScalarCompatible f) :
    IsMeasurableCotangentFamily (fun a x => CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (scalarDifferentialZeroExtension a (f a)) x.val)) := by
  refine ⟨fun a => measurable_smooth (smooth_differential (hf a)), ?_, ?_⟩
  · intro a γ x hx
    apply differential_arrow (isotropyArrow a γ) (scalarDifferentialZeroExtension a (f a)) (scalarDifferentialZeroExtension a (f a)) x
      (omega_subset_larger a hx) (differentiable_zext (hf a) ⟨x, hx⟩)
      (differentiable_zext (hf a) ⟨_, isotropy_mem a γ x hx⟩)
    filter_upwards [(isOpen_omega a).mem_nhds hx] with y hy
    simpa [scalarDifferentialZeroExtension, hy, isotropy_mem a γ y hy] using hc.1 a γ y hy
  · intro a b e x hx
    apply differential_arrow e.arrow (scalarDifferentialZeroExtension a (f a)) (scalarDifferentialZeroExtension b (f b)) x hx
      (differentiable_zext (hf a) ⟨x, e.source_shrinking hx⟩)
      (differentiable_zext (hf b) ⟨_, e.target_shrinking hx⟩)
    filter_upwards [e.arrow.isOpen_domain.mem_nhds hx] with y hy
    simpa [scalarDifferentialZeroExtension, e.source_shrinking hy, e.target_shrinking hy] using hc.2 a b e y hy

private theorem support_normSquare (v : Family (U := U) (H := H)) :
    tsupport (normSquare v) = cotangentSupport v := by
  have hzero (a : ActualChart (U := U) (H := H)) (x : omega a)
      (hx : q a x.val ∉ cotangentSupport v) : coefficient v a x = 0 := by
    by_contra hn
    exact hx (subset_closure ⟨a, x, rfl, hn⟩)
  let g : KPFiniteCuspAtlas.rawXU F ζ hζ U → NNReal :=
    fun x => if x ∈ cotangentSupport v then normSquare v x else 0
  have hg : Measurable g := (measurable_normSquare v).piecewise
    isClosed_closure.measurableSet measurable_const
  have he : g = normSquare v := (Classical.choose_spec (normSquare_descends v)).2 g
    ⟨hg, by
      intro a x
      by_cases hx : q a x.val ∈ cotangentSupport v
      · simp [g, hx, normSquare_chart]
      · simp [g, hx, hzero a x hx]⟩
  apply Set.Subset.antisymm
  · apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    change x ∉ cotangentSupport v at hn
    exact hx (by rw [← he]; simp only [g, if_neg hn])
  · apply closure_mono
    rintro x ⟨a, y, hq, hn⟩
    rw [← hq, Function.mem_support, normSquare_chart]
    simpa using hn

private theorem compact_family_of_support (v : Family (U := U) (H := H))
    {K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)} (hK : IsCompact K)
    (hs : cotangentSupport v ⊆ K) : HasCompactSupport (normSquare v) := by
  rw [HasCompactSupport, support_normSquare]
  exact hK.of_isClosed_subset isClosed_closure hs

private theorem smooth_smul {a : ActualChart (U := U) (H := H)}
    {f : omega a → ℂ} {W : omega a → E F} (hf : SmoothOnLift a f) (hW : SmoothOnLift a W) :
    SmoothOnLift a (fun x => f x • W x) := by
  obtain ⟨g, hg, he⟩ := hf
  obtain ⟨V, hV, he'⟩ := hW
  exact ⟨fun x => g x • V x, hg.smul hV, fun x => by dsimp; rw [he x, he' x]⟩

private theorem cutoff_cotangent (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : ∀ a : ActualChart (U := U) (H := H), SmoothOnLift a (fun x => η (q a x.val)))
    (W : T_U F ζ hζ U R P H) :
    IsMeasurableCotangentFamily (fun a x => (η (q a x.val) : ℂ) • coefficient W.val a x) := by
  refine ⟨fun a => measurable_smooth (smooth_smul (smooth_ofReal (hη a)) (W.property.1 a)),
    ?_, ?_⟩
  · intro a γ x hx
    change (η (q a ((isotropyArrow a γ).psi x)) : ℂ) • W.val.val a ⟨_, _⟩ = _
    rw [q_isotropy, W.val.property.2.1 a γ x hx, map_smul]
    rfl
  · intro a b e x hx
    change (η (q b (e.arrow.psi x)) : ℂ) • W.val.val b ⟨_, _⟩ = _
    rw [q_branch, W.val.property.2.2 a b e x hx, map_smul]
    rfl

private theorem smul_support_left (f : ScalarFields F ζ hζ U R P H)
    (v : ChartFields F ζ hζ U R P H)
    (hv : IsMeasurableCotangentFamily (fun a x => f a x • v a x)) :
    cotangentSupport ⟨_, hv⟩ ⊆ scalarSupport f := by
  apply closure_mono
  rintro x ⟨a, y, hq, hn⟩
  exact ⟨a, y, hq, (smul_ne_zero_iff.mp hn).1⟩

private theorem smul_support_right (f : ScalarFields F ζ hζ U R P H)
    (v : Family (U := U) (H := H))
    (hv : IsMeasurableCotangentFamily (fun a x => f a x • coefficient v a x)) :
    cotangentSupport ⟨_, hv⟩ ⊆ cotangentSupport v := by
  apply closure_mono
  rintro x ⟨a, y, hq, hn⟩
  exact ⟨a, y, hq, (smul_ne_zero_iff.mp hn).2⟩

private theorem cutoff_gradient (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : ∀ a : ActualChart (U := U) (H := H), SmoothOnLift a (fun x => η (q a x.val)))
    (f : S_U F ζ hζ U R P H) :
    IsMeasurableCotangentFamily (fun a x => f.val a x • CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (scalarDifferentialZeroExtension a (fun y => (η (q a y.val) : ℂ))) x.val)) := by
  let u : ScalarFields F ζ hζ U R P H := fun a y => (η (q a y.val) : ℂ)
  have hu a : SmoothOnLift a (u a) := smooth_ofReal (hη a)
  refine ⟨fun a => measurable_smooth (smooth_smul (f.property.1 a)
    (smooth_differential (hu a))), ?_, ?_⟩
  · intro a γ x hx
    have hd := differential_arrow_const (isotropyArrow a γ) 1 (scalarDifferentialZeroExtension a (u a)) (scalarDifferentialZeroExtension a (u a))
      x (omega_subset_larger a hx) (differentiable_zext (hu a) ⟨x, hx⟩)
      (differentiable_zext (hu a) ⟨_, isotropy_mem a γ x hx⟩) (by
        filter_upwards [(isOpen_omega a).mem_nhds hx] with y hy
        simp [scalarDifferentialZeroExtension, u, hy, isotropy_mem a γ y hy, q_isotropy])
    change f.val a ⟨_, _⟩ • _ = _
    rw [hd, one_smul, f.property.2.1.1 a γ x hx]
    change _ = (isotropyArrow a γ).phase x •
      KPContCotangentRealOrthogonalComplexification.operatorComplexification _
        (Q (isotropyArrow a γ) x) (f.val a ⟨x, hx⟩ • _)
    rw [map_smul, smul_smul]
  · intro a b e x hx
    have hd := differential_arrow_const e.arrow 1 (scalarDifferentialZeroExtension a (u a)) (scalarDifferentialZeroExtension b (u b)) x hx
      (differentiable_zext (hu a) ⟨x, e.source_shrinking hx⟩)
      (differentiable_zext (hu b) ⟨_, e.target_shrinking hx⟩) (by
        filter_upwards [e.arrow.isOpen_domain.mem_nhds hx] with y hy
        simp [scalarDifferentialZeroExtension, u, e.source_shrinking hy, e.target_shrinking hy, q_branch])
    change f.val b ⟨_, _⟩ • _ = _
    rw [hd, one_smul, f.property.2.1.2 a b e x hx]
    change _ = e.arrow.phase x •
      KPContCotangentRealOrthogonalComplexification.operatorComplexification _
        (Q e.arrow x) (f.val a ⟨x, e.source_shrinking hx⟩ • _)
    rw [map_smul, smul_smul]

theorem scalar_differential_descent :
  let L : (a : ActualChart (U := U) (H := H)) → (omega a → ℂ) → M F → ℂ :=
    fun a f x => if hx : x ∈ omega a then f ⟨x, hx⟩ else 0
  let D : (a : ActualChart (U := U) (H := H)) → (omega a → ℂ) → omega a → E F :=
    fun a f x => CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (L a f) x.val)
  let lift : (KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ) →
      (a : ActualChart (U := U) (H := H)) → omega a → ℂ :=
    fun η a x => (η (q a x.val) : ℂ)
  (∀ f : S_U F ζ hζ U R P H,
    IsMeasurableCotangentFamily (fun a => D a (f.val a)) ∧
    ∀ hv : IsMeasurableCotangentFamily (fun a => D a (f.val a)),
      (⟨fun a => D a (f.val a), hv⟩ : Family (U := U) (H := H)) ∈ cotangentTests ∧
      cotangentSupport ⟨fun a => D a (f.val a), hv⟩ ⊆ scalarSupport f.val) ∧
  (∀ (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
      (hη : ∀ a : ActualChart (U := U) (H := H),
        SmoothOnLift a (fun x => η (q a x.val))),
    (∀ f : S_U F ζ hζ U R P H,
      (fun a x => lift η a x * f.val a x) ∈ scalarTests) ∧
    (∀ W : T_U F ζ hζ U R P H,
      IsMeasurableCotangentFamily (fun a x => lift η a x • coefficient W.val a x) ∧
      ∀ hv : IsMeasurableCotangentFamily (fun a x => lift η a x • coefficient W.val a x),
        (⟨fun a x => lift η a x • coefficient W.val a x, hv⟩ :
          Family (U := U) (H := H)) ∈ cotangentTests) ∧
    (∀ f : S_U F ζ hζ U R P H,
      IsMeasurableCotangentFamily (fun a x => f.val a x • D a (lift η a) x) ∧
      ∀ hv : IsMeasurableCotangentFamily (fun a x => f.val a x • D a (lift η a) x),
        (⟨fun a x => f.val a x • D a (lift η a) x, hv⟩ :
          Family (U := U) (H := H)) ∈ cotangentTests)) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro f
    refine ⟨differential_measurable f.val f.property.1 f.property.2.1, ?_⟩
    intro hv
    have hs := differential_support f.val hv
    refine ⟨?_, hs⟩
    exact ⟨fun a => smooth_differential (f.property.1 a),
      compact_family_of_support ⟨_, hv⟩ f.property.2.2 hs⟩
  · intro η hη
    refine ⟨scalar_cutoff η hη, ?_, ?_⟩
    · intro W
      refine ⟨cutoff_cotangent η hη W, ?_⟩
      intro hv
      refine ⟨fun a => smooth_smul (smooth_ofReal (hη a)) (W.property.1 a), ?_⟩
      have hs := smul_support_right (fun a x => (η (q a x.val) : ℂ)) W.val hv
      have hK : IsCompact (cotangentSupport W.val) := by
        rw [← support_normSquare]
        exact W.property.2
      exact compact_family_of_support ⟨_, hv⟩ hK hs
    · intro f
      refine ⟨cutoff_gradient η hη f, ?_⟩
      intro hv
      refine ⟨fun a => smooth_smul (f.property.1 a)
        (smooth_differential (smooth_ofReal (hη a))), ?_⟩
      exact compact_family_of_support ⟨_, hv⟩ f.property.2.2
        (smul_support_left f.val _ hv)

end DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescentCalculus

end

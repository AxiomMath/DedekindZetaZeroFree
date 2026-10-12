module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.WeakSections.SupportAndMultiplication
public import DedekindZetaZeroFree.Analysis.EllipticEquations.Regularity.IntegerOrderEstimateTransfer

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorFormWeakLocalization
open KPContSectorLineL2Isometry KPContActualSectorSmoothTestModules
open KPContActualSectorTestDifferentialDescent
open KPContSectorScalarLineAlgebra KPContSectorCoveredQuotientVocabulary
open KPContActualSectorTestEmbeddings
open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentOverlapRationalBranches
open KPContActualCotangentMeasurableFamilies KPContActualCotangentPieceHilbertSum
open KPContActualSectorChartEquivariantInputs KPContLocalNorm
open KPContActualCotangentChartRestriction

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem compactMultiplier_bounded
    (η : CompactMultiplier (U := U) (H := H)) :
    ∃ B D : ℝ, 0 ≤ B ∧ 0 ≤ D ∧ (∀ x, |η.val.val x| ≤ B) ∧
      ∀ (a : ActualChart (U := U) (H := H)) (y : KPContCotangentOverlapRationalBranches.omega a),
        ‖cutoffDifferential η.val a y‖ ≤ D :=
  KPContActualSectorMultiplier.compactCutoff_bounds
    F ζ hζ U R P H η.val η.property

 def actualBorelProduct (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : Measurable η) (B : ℝ) (hB : ∀ x, |η x| ≤ B)
    (s : BorelL2Sections F ζ hζ U R P H) : BorelL2Sections F ζ hζ U R P H := by
  let v := scalarRepresentative F ζ hζ U R P H s.val
  let f : GenuineCoveredScalars F ζ hζ U :=
    ⟨fun x => (η (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x) : ℂ) * v.val x, by
      intro ε x
      simp only [q_z, v.property ε x]
      ring⟩
  have hq : Measurable (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U) :=
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable
  have hf : Measurable f.val :=
    ((Complex.measurable_ofReal.comp hη).comp hq).mul
      ((borel_iff F ζ hζ U R P H s.val).mp s.property.1)
  have hlp : MemLp f.val 2 (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U) := by
    refine (representative_memLp F ζ hζ U R P H s).of_le_mul hf.aestronglyMeasurable
      (c := B) (Filter.Eventually.of_forall (fun x => ?_))
    change ‖(η _ : ℂ) * v.val x‖ ≤ B * ‖v.val x‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  exact borelS F ζ hζ U R P H ⟨f, hf, hlp⟩

private theorem actualBorelProduct_coefficient
    (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : Measurable η) (B : ℝ) (hB : ∀ x, |η x| ≤ B)
    (s : BorelL2Sections F ζ hζ U R P H) (a : ActualChart (U := U) (H := H))
    (y : a.domain) :
    (a.coefficient (actualBorelProduct η hη B hB s).val y : ℂ) =
      (η (a.toBase y) : ℂ) * (a.coefficient s.val y : ℂ) := by
  change (S F ζ hζ U R P H ⟨_,_⟩ a.component).val y.val = _
  rw [S_apply]
  change (η (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U (Quotient.mk _
      (y.val, (H.atlas U).representative a.component))) : ℂ) *
    (scalarRepresentative F ζ hζ U R P H s.val).val
      (Quotient.mk _ (y.val, (H.atlas U).representative a.component)) = _
  rw [q_mk]
  have he := congrArg (fun t : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H =>
      (t a.component).val y.val)
    ((S F ζ hζ U R P H).apply_symm_apply s.val)
  rw [S_apply] at he
  change (scalarRepresentative F ζ hζ U R P H s.val).val
    (Quotient.mk _ (y.val, (H.atlas U).representative a.component)) = _ at he
  rw [he]
  congr 2

private theorem continuous_labeledA_self :
    Continuous (labeledA (placeEquiv F ζ hζ) : M F → KPCuspGenuineMonodromy.SymmetricSpace F) := by
  apply continuous_pi
  intro k
  exact (continuous_apply (placeEquiv F ζ hζ |>.symm k)).comp
    (CotangentLogCoframe.A (d F)).continuous
private theorem isOpen_omega (a : ActualChart (U := U) (H := H)) : IsOpen (omega a) :=
  a.domain_open.preimage continuous_labeledA_self

private lemma q_coordinates (a : ActualChart (U := U) (H := H)) (y : a.domain) :
    q a (coordinates a y).val = a.toBase y := by
  have hi : ∀ z : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
    intro z; funext k; simp [labeledA, labeledAInv]
  simp only [ShrunkChart.toBase, KPContCotangentOverlapRationalBranches.q, coordinates]
  rw [hi]
private theorem continuous_iff_isQuotientMap {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {q : X → Y} (hq : IsQuotientMap q)
    (f : Y → Z) : Continuous f ↔ Continuous (f ∘ q) := by
  refine ⟨fun h => h.comp hq.continuous, fun h => ?_⟩
  exact Continuous.mk fun s hs => by
    rw [← hq.isOpen_preimage]
    exact h.isOpen_preimage s hs
private theorem continuous_of_all_lifts (f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hf : ∀ a : ActualChart (U := U) (H := H), Continuous (fun y : omega a => f (q a y.val))) :
    Continuous f := by
  obtain ⟨cover⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  refine continuous_of_cover_nhds (s := fun n => (cover.chart n).baseDomain) ?_ ?_
  · intro x
    have hx : x ∈ ⋃ n, (cover.chart n).baseDomain := by rw [cover.covers]; trivial
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact ⟨n, (cover.properties n).base_open.mem_nhds hn⟩
  · intro n
    let a := cover.chart n
    have hloc : Continuous ((fun z : a.baseDomain => f z.val) ∘ a.quotientMap) := by
      convert (hf a).comp (coordinates_continuous a) using 1
      funext y
      exact congrArg f (q_coordinates a y).symm
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_iff_isQuotientMap (cover.properties n).quotient _).mpr hloc
private theorem cutoff_continuous (η : RealSmoothCutoff F ζ hζ U R P H) : Continuous η.val := by
  apply continuous_of_all_lifts
  intro a
  obtain ⟨g,hg,he⟩ := η.smooth a
  convert hg.continuousOn.domRestrict using 1
  exact funext (fun y => (he y).symm)
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

private theorem smooth_ofReal {a : ActualChart (U := U) (H := H)} {f : omega a → ℝ}
    (hf : SmoothOnLift a f) : SmoothOnLift a (fun x => (f x : ℂ)) := by
  obtain ⟨g, hg, he⟩ := hf
  exact ⟨fun x => (g x : ℂ), Complex.ofRealCLM.contDiff.comp_contDiffOn hg,
    fun x => by dsimp; rw [he x]⟩

private theorem differentiable_liftExtension {a : ActualChart (U := U) (H := H)}
    {f : omega a → ℂ} (hf : SmoothOnLift a f) (x : omega a) :
    DifferentiableAt ℝ (liftExtension a f) x.val :=
  ((smooth_liftExtension hf).differentiableOn (by simp) x.val x.property).differentiableAt
    ((isOpen_omega a).mem_nhds x.property)

private theorem sectionFields_apply (s : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    sectionFields s a x = (s a.component).val (labeledA (placeEquiv F ζ hζ) x.val) := by
  have hcoe : (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient s x.val =
      (KPCuspGenuineMonodromy.chi F ζ hζ
          ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).splitting x.val) : ℂ) *
        (s a.component).val
          ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).kind.representative •
            labeledA (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).places x.val) :=
    rfl
  rw [sectionFields, hcoe]
  simp [KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative]

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

private theorem measurable_sectionFields
    (s : BorelL2Sections F ζ hζ U R P H) (a : ActualChart (U := U) (H := H)) :
    Measurable (sectionFields s.val a) := by
  have he : sectionFields s.val a = fun x =>
      (s.val a.component).val (labeledA (placeEquiv F ζ hζ) x.val) :=
    funext (sectionFields_apply s.val a)
  rw [he]
  exact (s.property.1 a.component).comp
    (continuous_labeledA_self.measurable.comp measurable_subtype_coe)

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

 theorem cutoff_gradient (η : RealSmoothCutoff F ζ hζ U R P H)
    (s : BorelL2Sections F ζ hζ U R P H) :
    IsMeasurableCotangentFamily (fun a x => sectionFields s.val a x • CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (liftExtension a (fun y => (η.val (q a y.val) : ℂ))) x.val)) := by
  let u : ScalarFields F ζ hζ U R P H := fun a y => (η.val (q a y.val) : ℂ)
  have hu a : SmoothOnLift a (u a) := smooth_ofReal (η.smooth a)
  refine ⟨fun a => (measurable_sectionFields s a).smul
    (measurable_smooth (smooth_differential (hu a))), ?_, ?_⟩
  · intro a γ x hx
    have hd := differential_arrow_const (isotropyArrow a γ) 1 (liftExtension a (u a)) (liftExtension a (u a))
      x (omega_subset_larger a hx) (differentiable_liftExtension (hu a) ⟨x, hx⟩)
      (differentiable_liftExtension (hu a) ⟨_, isotropy_mem a γ x hx⟩) (by
        filter_upwards [(isOpen_omega a).mem_nhds hx] with y hy
        simp [liftExtension, u, hy, isotropy_mem a γ y hy, q_isotropy])
    change sectionFields s.val a ⟨_, _⟩ • _ = _
    rw [hd, one_smul, (section_compatible s.val).1 a γ x hx]
    change _ = (isotropyArrow a γ).phase x •
      KPContCotangentRealOrthogonalComplexification.operatorComplexification _
        (Q (isotropyArrow a γ) x) (sectionFields s.val a ⟨x, hx⟩ • _)
    rw [map_smul, smul_smul]
  · intro a b e x hx
    have hd := differential_arrow_const e.arrow 1 (liftExtension a (u a)) (liftExtension b (u b)) x hx
      (differentiable_liftExtension (hu a) ⟨x, e.source_shrinking hx⟩)
      (differentiable_liftExtension (hu b) ⟨_, e.target_shrinking hx⟩) (by
        filter_upwards [e.arrow.isOpen_domain.mem_nhds hx] with y hy
        simp [liftExtension, u, e.source_shrinking hy, e.target_shrinking hy, q_branch])
    change sectionFields s.val b ⟨_, _⟩ • _ = _
    rw [hd, one_smul, (section_compatible s.val).2 a b e x hx]
    change _ = e.arrow.phase x •
      KPContCotangentRealOrthogonalComplexification.operatorComplexification _
        (Q e.arrow x) (sectionFields s.val a ⟨x, e.source_shrinking hx⟩ • _)
    rw [map_smul, smul_smul]

 theorem cutoff_family (η : RealSmoothCutoff F ζ hζ U R P H)
    (W : Family (U := U) (H := H)) :
    IsMeasurableCotangentFamily (fun a x => cutoffLift η a x • coefficient W a x) := by
  refine ⟨fun a => (measurable_smooth (smooth_ofReal (η.smooth a))).smul
    (W.property.1 a), ?_, ?_⟩
  · intro a γ x hx
    change (η.val (q a _) : ℂ) • _ = _
    simp only [cutoffLift, coefficient]
    rw [q_isotropy, W.property.2.1 a γ x hx, map_smul]
  · intro a b e x hx
    change (η.val (q b _) : ℂ) • _ = _
    simp only [cutoffLift, coefficient]
    rw [q_branch, W.property.2.2 a b e x hx, map_smul]

 def productFamily (η : RealSmoothCutoff F ζ hζ U R P H)
    (s : BorelL2Sections F ζ hζ U R P H) (W : Family (U := U) (H := H)) :
    Family (U := U) (H := H) :=
  (⟨fun a x => cutoffLift η a x • coefficient W a x, cutoff_family η W⟩ : Family) +
    ⟨fun a x => sectionFields s.val a x • cutoffDifferential η a x, cutoff_gradient η s⟩

private theorem base_direction (j : Fin (3*d F)) :
    (baseReindex (F:=F)).symm (EuclideanSpace.single j 1) =
      HyperbolicChart.coordinateVector (d F) ((coefficientIndex (F:=F)).symm j).1
        ((coefficientIndex (F:=F)).symm j).2 := by
  ext ik
  simp only [baseReindex, LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.symm_symm, HyperbolicChart.coordinateVector,
    WithLp.ofLp_toLp]
  simp [EuclideanSpace.single_apply, Pi.single_apply, ← Equiv.apply_eq_iff_eq_symm_apply]
private theorem decoder_differential (a : ActualChart (U:=U) (H:=H)) (f : omega a → ℂ)
    (x : Space (3*d F)) (hx : x ∈ coordinateDomain a) (j : Fin (3*d F)) :
    (let p := (baseReindex (F:=F)).symm x
     let ik := (coefficientIndex (F:=F)).symm j
     let v := chartDifferential a f ⟨p,hx⟩
     ![(Real.exp (-p (ik.1,2)):ℂ) * v (ik.1,1),
       (Real.exp (-p (ik.1,2)):ℂ) * v (ik.1,2), v (ik.1,0)] ik.2) =
    HyperbolicChart.coordinateDerivative (d F) ((coefficientIndex (F:=F)).symm j).1
      ((coefficientIndex (F:=F)).symm j).2 (liftExtension a f) ((baseReindex (F:=F)).symm x) := by
  generalize hi : (coefficientIndex (F:=F)).symm j = ik
  obtain ⟨i,k⟩ := ik
  fin_cases k <;> simp [chartDifferential, CotangentLogCoframe.j_apply,
    HyperbolicChart.differential, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
    ← Complex.exp_add]

private theorem flattened_differential (a : ActualChart (U := U) (H := H))
    (f : omega a → ℂ) (x : Space (3 * d F)) (hx : x ∈ coordinateDomain a)
    (hf : DifferentiableAt ℝ (liftExtension a f) ((baseReindex (F := F)).symm x))
    (j : Fin (3 * d F)) :
    fderiv ℝ (fun y => liftExtension a f ((baseReindex (F := F)).symm y)) x
      (EuclideanSpace.single j 1) =
    HyperbolicChart.coordinateDerivative (d F) ((coefficientIndex (F := F)).symm j).1
      ((coefficientIndex (F := F)).symm j).2 (liftExtension a f)
        ((baseReindex (F := F)).symm x) := by
  have hd := hf.hasFDerivAt.comp x
    ((baseReindex (F := F)).symm.toContinuousLinearEquiv.hasFDerivAt)
  change HasFDerivAt (fun y => liftExtension a f ((baseReindex (F := F)).symm y)) _ x at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  rw [base_direction]
  rfl

private theorem coordinateDomain_isOpen (a : ActualChart (U := U) (H := H)) :
    IsOpen (coordinateDomain a) := by
  change IsOpen ((toActual (F := F) (ζ := ζ) (hζ := hζ)) ⁻¹' a.domain)
  apply a.domain_open.preimage
  unfold toActual labeledA
  fun_prop

private theorem smooth_liftExtension_flat (a : ActualChart (U := U) (H := H))
    (f : omega a → ℂ) (hf : SmoothOnLift a f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (liftExtension a f) (omega a) := by
  obtain ⟨g, hg, he⟩ := hf
  apply hg.congr
  intro x hx
  simpa only [liftExtension, dite_eq_left hx] using (he ⟨x, hx⟩).symm

private theorem smooth_flattened (a : ActualChart (U := U) (H := H))
    (f : omega a → ℂ) (hf : SmoothOnLift a f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => liftExtension a f ((baseReindex (F := F)).symm x))
      (coordinateDomain a) :=
  (smooth_liftExtension_flat a f hf).comp (baseReindex (F := F)).symm.contDiff.contDiffOn
    (fun _ hx => hx)

 def mulBall {n : ℕ} (B : LocalBall n) (b : Space n → ℂ)
    (hb : MemLp b ⊤ (volume.restrict B.carrier)) : BallL2 B →L[ℂ] BallL2 B :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (volume.restrict B.carrier) ⊤ 2 2 (hb.toLp b)
 theorem mulBall_ae {n : ℕ} (B : LocalBall n) (b : Space n → ℂ)
    (hb : MemLp b ⊤ (volume.restrict B.carrier)) (u : BallL2 B) :
    (fun x => mulBall B b hb u x) =ᵐ[volume.restrict B.carrier] (fun x => b x * u x) := by
  have he := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (hb.toLp b) u
  filter_upwards [he, hb.coeFn_toLp] with x hx hxb
  simpa only [mulBall, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', hxb] using hx
 theorem memLp_top_on_ball {n : ℕ} (B : LocalBall n) (Ω : Set (Space n))
    (hΩ : IsOpen Ω) (hB : IsCompact (closure B.carrier) ∧ closure B.carrier ⊆ Ω)
    (b : Space n → ℂ) (hb : ContinuousOn b Ω) :
    MemLp b ⊤ (volume.restrict B.carrier) := by
  obtain ⟨C,hC⟩ := hB.1.exists_bound_of_continuousOn (hb.mono hB.2)
  apply memLp_top_of_bound (hb.mono (subset_closure.trans hB.2) |>.aestronglyMeasurable B.toOpens.isOpen.measurableSet) C
  exact ae_restrict_of_forall_mem B.toOpens.isOpen.measurableSet (fun x hx => hC x (subset_closure hx))

private theorem smooth_cutoff_flat (η : CompactMultiplier (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (multiplierCoordinate η a) (coordinateDomain a) := by
  apply smooth_flattened
  obtain ⟨g,hg,he⟩ := η.val.smooth a
  exact ⟨fun x => (g x : ℂ), Complex.ofRealCLM.contDiff.comp_contDiffOn hg,
    fun x => congrArg Complex.ofReal (he x)⟩

 def decode (x : Space (3*d F)) (j : Fin (3*d F)) (v : KPContCotangentActualGenuineTwistIsotropy.E F) : ℂ :=
  let p := (baseReindex (F := F)).symm x
  let ik := (coefficientIndex (F := F)).symm j
  ![(Real.exp (-p (ik.1,2)) : ℂ) * v (ik.1,1),
    (Real.exp (-p (ik.1,2)) : ℂ) * v (ik.1,2), v (ik.1,0)] ik.2

private theorem decode_add_smul (x : Space (3*d F)) (j : Fin (3*d F))
    (b c : ℂ) (v w : KPContCotangentActualGenuineTwistIsotropy.E F) :
    decode x j (b • v + c • w) = b * decode x j v + c * decode x j w := by
  generalize hi : (coefficientIndex (F := F)).symm j = ik
  rcases ik with ⟨i,k⟩
  fin_cases k <;> simp [decode, hi, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> ring

 def cutoffPartial (η : CompactMultiplier (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (j : Fin (3*d F)) (x : Space (3*d F)) : ℂ :=
  fderiv ℝ (multiplierCoordinate η a) x (EuclideanSpace.single j 1)

private theorem cutoffPartial_decode (η : CompactMultiplier (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (j : Fin (3*d F))
    (x : Space (3*d F)) (hx : x ∈ coordinateDomain a) :
    cutoffPartial η a j x = decode x j
      (cutoffDifferential η.val a ⟨(baseReindex (F := F)).symm x, hx⟩) := by
  have hp := (smooth_liftExtension_flat a (cutoffLift η.val a) (by
    obtain ⟨g,hg,he⟩ := η.val.smooth a
    exact ⟨fun x => (g x : ℂ), Complex.ofRealCLM.contDiff.comp_contDiffOn hg,
      fun x => congrArg Complex.ofReal (he x)⟩)).differentiableOn (by simp) _ hx
  have hpd := hp.differentiableAt ((show IsOpen (omega a) from a.domain_open.preimage (by
    unfold labeledA; fun_prop)).mem_nhds hx)
  exact (flattened_differential a _ x hx hpd j).trans (decoder_differential a _ x hx j).symm

 theorem index_cases {n : ℕ} (α : MultiIndex n 1) :
    α = zeroIndex n ∨ ∃ i : Fin n, α = KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex i := by
  by_cases hz : ∀ i, (α.val i).val = 0
  · left
    apply Subtype.ext
    funext i
    exact Fin.ext (hz i)
  · obtain ⟨i, hi⟩ := not_forall.mp hz
    right
    refine ⟨i, ?_⟩
    have hone : (α.val i).val = 1 := by omega
    apply Subtype.ext
    funext j
    apply Fin.ext
    by_cases hji : j = i
    · subst j; simpa [KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex] using hone
    · have hj : (α.val j).val = 0 := by
        have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => (α.val i).val)
          (show ({i,j} : Finset (Fin n)) ⊆ Finset.univ from Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
        have h := α.property
        simp [Finset.sum_pair (Ne.symm hji), hone] at hsum
        omega
      simpa [KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, hji] using hj
open WeakJets.Raw
 theorem counts_first {n : ℕ} (i : Fin n) :
    counts (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex i) = unitCount i := by
  classical
  funext j
  by_cases hji : j = i <;>
    simp [counts, KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, unitCount, hji]

 def multipliedSobolev {n : ℕ} (B : LocalBall n) (Ω : Set (Space n))
    (hΩ : IsOpen Ω) (hB : IsCompact (closure B.carrier) ∧ closure B.carrier ⊆ Ω)
    (b : Space n → ℂ) (hb : ContDiffOn ℝ (⊤ : ℕ∞) b Ω)
    (u : IntegerSobolev B 1) : IntegerSobolev B 1 := by
  let db := fun j x => fderiv ℝ b x (EuclideanSpace.single j 1)
  have hpartial j : ContinuousOn (db j) Ω :=
    ((hb.fderiv_of_isOpen hΩ (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffOn_const).continuousOn
  let M := mulBall B b (memLp_top_on_ball B Ω hΩ hB b hb.continuousOn)
  let N := fun j => mulBall B (db j) (memLp_top_on_ball B Ω hΩ hB _ (hpartial j))
  let pick := fun α : MultiIndex n 1 => α.directions.headD ⟨0, B.dimension_pos⟩
  let v := fun α : MultiIndex n 1 => if α = zeroIndex n then M (u.derivatives α)
    else M (u.derivatives α) + N (pick α) (u.derivatives (zeroIndex n))
  have hzero : v (zeroIndex n) = M (u.derivatives (zeroIndex n)) := by simp [v]
  have hfirst j : v (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j) =
      M (u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j)) +
        N j (u.derivatives (zeroIndex n)) := by
    have hn : KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j ≠ zeroIndex n := by
      intro h
      have he := congrArg (fun α : MultiIndex n 1 => (α.val j).val) h
      simp [KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, zeroIndex] at he
    simp [v, hn, pick, KPContLocalEnergy.SobolevEnergyEstimates.firstIndex_directions]
  refine ⟨v, ?_⟩
  intro α
  change IsWeakDerivative B α (v (zeroIndex n)) (v α)
  rcases index_cases α with rfl | ⟨j, rfl⟩
  · intro φ
    have hd : (zeroIndex n).directions = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro i hi
      simp [zeroIndex]
    simp only [coordinateDerivative, hd, coordinateDerivativeList]
    have hdeg : (zeroIndex n).degree = 0 := by simp [MultiIndex.degree, zeroIndex]
    rw [hdeg]
    simp
  · intro φ
    change (∫ x in B.carrier, v (zeroIndex n) x *
      coordinateDerivative (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j) (fun y => φ y) x) = _
    rw [hzero, hfirst]
    have hcount : (∑ i, ((0 : Counts n) + unitCount j) i) ≤ 1 := by
      simp [unitCount]
    have hjet : jet u (unitCount j) = u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j) := by
      rw [← counts_first, jet_index]
    have hw := weak_product_rule_first u 0 j hcount (hb.mono (subset_closure.trans hB.2)) φ
    simp only [zero_add, jet_zero, hjet] at hw
    simp only [IsWeakDerivative, coordinateDerivative,
      KPContLocalEnergy.SobolevEnergyEstimates.firstIndex_directions]
    have hdegree : (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j).degree = 1 := by
      simp only [MultiIndex.degree, KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex,
        apply_ite Fin.val, Fin.val_one, Fin.val_zero]
      simp
    rw [hdegree, pow_one, neg_one_mul]
    calc
      _ = ∫ x in B.carrier, b x * u.derivatives (zeroIndex n) x *
          coordinateDerivativeList [j] (fun y => φ y) x := by
        apply integral_congr_ae
        filter_upwards [mulBall_ae B b _ (u.derivatives (zeroIndex n))] with x hx
        rw [hx]
      _ = -(∫ x in B.carrier, (db j x * u.derivatives (zeroIndex n) x +
          b x * u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j) x) * φ x) := hw
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (M (u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j)))
          (N j (u.derivatives (zeroIndex n))),
          mulBall_ae B b _ (u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j)),
          mulBall_ae B (db j) _ (u.derivatives (zeroIndex n))] with x h1 h2 h3
        rw [h1]
        change (_ + _) * φ x = (M _ x + N j _ x) * φ x
        change M _ x = _ at h2
        change N j _ x = _ at h3
        rw [h2, h3, add_comm]

private theorem multipliedSobolev_zero {n : ℕ} (B : LocalBall n) (Ω : Set (Space n))
    (hΩ : IsOpen Ω) (hB : IsCompact (closure B.carrier) ∧ closure B.carrier ⊆ Ω)
    (b : Space n → ℂ) (hb : ContDiffOn ℝ (⊤ : ℕ∞) b Ω)
    (u : IntegerSobolev B 1) :
    (fun x => (multipliedSobolev B Ω hΩ hB b hb u).derivatives (zeroIndex n) x)
      =ᵐ[volume.restrict B.carrier] fun x => b x * u.derivatives (zeroIndex n) x := by
  simp only [multipliedSobolev, ↓reduceIte]
  exact mulBall_ae B b _ _

private theorem multipliedSobolev_first {n : ℕ} (B : LocalBall n) (Ω : Set (Space n))
    (hΩ : IsOpen Ω) (hB : IsCompact (closure B.carrier) ∧ closure B.carrier ⊆ Ω)
    (b : Space n → ℂ) (hb : ContDiffOn ℝ (⊤ : ℕ∞) b Ω)
    (u : IntegerSobolev B 1) (j : Fin n) :
    (fun x => (multipliedSobolev B Ω hΩ hB b hb u).derivatives
      (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j) x) =ᵐ[volume.restrict B.carrier]
      fun x => b x * u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j) x +
        fderiv ℝ b x (EuclideanSpace.single j 1) * u.derivatives (zeroIndex n) x := by
  have hn : KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j ≠ zeroIndex n := by
    intro h
    have he := congrArg (fun α : MultiIndex n 1 => (α.val j).val) h
    simp [KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, zeroIndex] at he
  simp only [multipliedSobolev, hn, ↓reduceIte, KPContLocalEnergy.SobolevEnergyEstimates.firstIndex_directions,
    List.headD_cons]
  let M := mulBall B b (memLp_top_on_ball B Ω hΩ hB b hb.continuousOn)
  let N := mulBall B (fun x => fderiv ℝ b x (EuclideanSpace.single j 1))
    (memLp_top_on_ball B Ω hΩ hB _
      ((hb.fderiv_of_isOpen hΩ (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffOn_const).continuousOn)
  filter_upwards [Lp.coeFn_add (M (u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j)))
      (N (u.derivatives (zeroIndex n))), mulBall_ae B b _
      (u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j)),
    mulBall_ae B (fun x => fderiv ℝ b x (EuclideanSpace.single j 1)) _
      (u.derivatives (zeroIndex n))] with x h1 h2 h3
  rw [h1]
  simp only [Pi.add_apply]
  rw [h2, h3]

private theorem actualBorelProduct_fields
    (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : Measurable η) (B : ℝ) (hB : ∀ x, |η x| ≤ B)
    (s : BorelL2Sections F ζ hζ U R P H) (a : ActualChart (U := U) (H := H))
    (x : omega a) :
    sectionFields (actualBorelProduct η hη B hB s).val a x =
      (η (q a x.val) : ℂ) * sectionFields s.val a x := by
  rw [sectionFields_apply, sectionFields_apply]
  exact actualBorelProduct_coefficient η hη B hB s a ⟨_, x.property⟩

private theorem scalarCoordinate_product
    (η : CompactMultiplier (U := U) (H := H))
    (hη : Measurable η.val.val) (C : ℝ) (hC : ∀ x, |η.val.val x| ≤ C)
    (s : BorelL2Sections F ζ hζ U R P H) (a : ActualChart (U := U) (H := H))
    (x : Space (3*d F)) (hx : x ∈ coordinateDomain a) :
    scalarCoordinate (actualBorelProduct η.val.val hη C hC s) a x =
      multiplierCoordinate η a x * scalarCoordinate s a x := by
  simp only [scalarCoordinate, multiplierCoordinate, liftExtension, dite_eq_left (show (baseReindex (F := F)).symm x ∈ omega a from hx)]
  exact actualBorelProduct_fields η.val.val hη C hC s a ⟨_, hx⟩

private theorem covariantCoordinate_product
    (η : CompactMultiplier (U := U) (H := H))
    (s : BorelL2Sections F ζ hζ U R P H) (W : Family (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (x : Space (3*d F))
    (hx : x ∈ coordinateDomain a) (j : Fin (3*d F)) :
    covariantCoordinate (productFamily η.val s W) a x j =
      multiplierCoordinate η a x * covariantCoordinate W a x j +
        cutoffPartial η a j x * scalarCoordinate s a x := by
  have hD := cutoffPartial_decode η a j x hx
  have hdecode (Z : Family (U := U) (H := H)) : covariantCoordinate Z a x j =
      decode x j (coefficient Z a ⟨(baseReindex (F := F)).symm x, hx⟩) := by
    simp only [covariantCoordinate, decode, liftExtension, dite_eq_left (show (baseReindex (F := F)).symm x ∈ omega a from hx)]
  rw [hdecode, hdecode]
  have hc : coefficient (productFamily η.val s W) a ⟨(baseReindex (F := F)).symm x, hx⟩ =
      cutoffLift η.val a ⟨_, hx⟩ • coefficient W a ⟨_, hx⟩ +
        sectionFields s.val a ⟨_, hx⟩ • cutoffDifferential η.val a ⟨_, hx⟩ := rfl
  rw [hc, decode_add_smul, ← hD]
  simp only [multiplierCoordinate, scalarCoordinate, liftExtension, dite_eq_left (show (baseReindex (F := F)).symm x ∈ omega a from hx)]
  ring

private theorem product_weakChartData
    (η : CompactMultiplier (U := U) (H := H))
    (hη : Measurable η.val.val) (C : ℝ) (hC : ∀ x, |η.val.val x| ≤ C)
    (s : BorelL2Sections F ζ hζ U R P H) (W : Family (U := U) (H := H))
    (hw : WeakChartData s W) :
    WeakChartData (actualBorelProduct η.val.val hη C hC s) (productFamily η.val s W) := by
  intro a B hB ε
  obtain ⟨h, hzero, hfirst⟩ := hw a B hB ε
  let v := multipliedSobolev B (coordinateDomain a) (coordinateDomain_isOpen a) hB
    (multiplierCoordinate η a) (smooth_cutoff_flat η a) h
  refine ⟨v, ?_, ?_⟩
  · filter_upwards [multipliedSobolev_zero B (coordinateDomain a) (coordinateDomain_isOpen a) hB
      (multiplierCoordinate η a) (smooth_cutoff_flat η a) h,
      hzero, ae_restrict_mem B.toOpens.isOpen.measurableSet] with x hv hx hmem
    rw [hv, hx, scalarCoordinate_product η hη C hC s a x (hB.2 (subset_closure hmem))]
    ring
  · intro α j hj
    have hα : α = KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j := by
      rcases index_cases α with hα | ⟨k, hα⟩
      · simp [hα, zeroIndex] at hj
      · have hkj : j = k := by
          by_contra hn
          simp [hα, KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, hn] at hj
        simpa [hkj] using hα
    subst α
    have hj' : ((KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j).val j).val = 1 := by
      simp [KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex]
    filter_upwards [multipliedSobolev_first B (coordinateDomain a) (coordinateDomain_isOpen a) hB
        (multiplierCoordinate η a) (smooth_cutoff_flat η a) h j,
      hzero, hfirst _ j hj', ae_restrict_mem B.toOpens.isOpen.measurableSet] with x hv h0 h1 hx
    rw [hv, h0, h1, covariantCoordinate_product η s W a x (hB.2 (subset_closure hx)) j]
    dsimp [cutoffPartial]
    ring

private theorem actualBorelProduct_supported
    (η : CompactMultiplier (U := U) (H := H))
    (hη : Measurable η.val.val) (C : ℝ) (hC : ∀ x, |η.val.val x| ≤ C)
    (s : BorelL2Sections F ζ hζ U R P H) (x : KPFiniteCuspAtlas.rawXU F ζ hζ U)
    (hx : x ∉ tsupport η.val.val) :
    squaredNorm F ζ hζ U R P H (actualBorelProduct η.val.val hη C hC s).val x = 0 := by
  obtain ⟨y, rfl⟩ := KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U x
  have he : η.val.val (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U y) = 0 :=
    image_eq_zero_of_notMem_tsupport hx
  unfold squaredNorm
  change ENNReal.ofReal
    (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ U R P H
      (S F ζ hζ U R P H ⟨_, _⟩) (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U y) ^ 2) = 0
  rw [KPContSectorSmoothFramesSupport.sectionNorm_pullback]
  change ENNReal.ofReal (‖(η.val.val (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U y) : ℂ) *
    (scalarRepresentative F ζ hζ U R P H s.val).val y‖ ^ 2) = 0
  simp [he]

theorem compactMultiplier_product_weakH1
    (η : CompactMultiplier (U := U) (H := H))
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (hweak : ActualWeakH1Loc (H := H) u) :
    ∃ v : KPContSectorClosedLpSubspace.H F ζ hζ R U,
      IsActualProduct η u v ∧ ActualWeakH1Loc (H := H) v ∧
      ∃ L : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), IsCompact L ∧ SupportedAE (H := H) v L := by
  obtain ⟨s, W, hs, hw⟩ := hweak
  obtain ⟨C, D, hC0, hD0, hC, hD⟩ := compactMultiplier_bounded η
  have hη : Measurable η.val.val := (cutoff_continuous η.val).measurable
  let t := actualBorelProduct η.val.val hη C hC s
  let v := (sectorLineIsometry F ζ hζ U R P H).symm (mk F ζ hζ U R P H t)
  have hv : sectorLineIsometry F ζ hζ U R P H v = mk F ζ hζ U R P H t :=
    (sectorLineIsometry F ζ hζ U R P H).apply_symm_apply _
  refine ⟨v, ⟨s, t, hs, hv, ?_⟩, ⟨t, productFamily η.val s W, hv, ?_⟩,
    tsupport η.val.val, η.property, t, hv, ?_⟩
  · intro a
    exact Filter.Eventually.of_forall fun y =>
      actualBorelProduct_fields η.val.val hη C hC s a (coordinates a y)
  · exact product_weakChartData η hη C hC s W hw
  · exact Filter.Eventually.of_forall fun x hx => actualBorelProduct_supported η hη C hC s x hx

end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

end

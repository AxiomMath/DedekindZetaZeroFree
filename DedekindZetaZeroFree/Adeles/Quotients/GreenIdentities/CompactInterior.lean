module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.HyperbolicCharts.LogarithmicCoframe
public import DedekindZetaZeroFree.Adeles.Quotients.GreenIdentities.InteriorZeroExtension

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualGlobalGreen

open KPContActualCotangentCountableShrinking KPContActualSectorSmoothTestModules
open KPContActualSectorTestDifferentialDescent KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContSectorSmoothFramesSupport
open KPContActualCotangentPieceHilbertSum

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem smoothOnLift_sectionFields
    (a : ShrunkChart F ζ hζ U R P H)
    (s : Sections F ζ hζ U R P H)
    (hs : IsSmoothSections F ζ hζ U R P H s) :
    SmoothOnLift a (sectionFields s a) := by
  have hA : ContDiff ℝ (⊤ : ℕ∞)
      (labeledA (placeEquiv F ζ hζ) : M F → KPCuspGenuineMonodromy.SymmetricSpace F) := by
    apply contDiff_pi.mpr
    intro k
    exact (contDiff_apply ℝ (ℂ × ℝ) ((placeEquiv F ζ hζ).symm k)).comp
      (CotangentLogCoframe.A (d F)).contDiff
  refine ⟨fun x => (s a.component).val (labeledA (placeEquiv F ζ hζ) x),
    ((hs a.component).comp hA).contDiffOn, ?_⟩
  intro x

  simp [sectionFields, LiftedChart.coefficient,
    KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative]

private lemma cd_eventually (d : ℕ) (f g : HyperbolicChart.Space d → ℂ)
    (x : HyperbolicChart.Space d) (h : f =ᶠ[nhds x] g) (i : Fin d) (k : Fin 3) :
    HyperbolicChart.coordinateDerivative d i k f =ᶠ[nhds x]
      HyperbolicChart.coordinateDerivative d i k g := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun A : HyperbolicChart.Space d →L[ℝ] ℂ =>
    A (HyperbolicChart.coordinateVector d i k)) hy

private lemma lap_local (d : ℕ) (f g : HyperbolicChart.Space d → ℂ)
    (x : HyperbolicChart.Space d) (h : f =ᶠ[nhds x] g) :
    HyperbolicChart.laplacian d f x = HyperbolicChart.laplacian d g x := by
  unfold HyperbolicChart.laplacian
  apply Finset.sum_congr rfl
  intro i hi
  have hc := fun k => cd_eventually d f g x h i k
  have hcc := fun k => cd_eventually d _ _ x (hc k) i k
  rw [(hc 2).eq_of_nhds, (hcc 2).eq_of_nhds, (hcc 0).eq_of_nhds, (hcc 1).eq_of_nhds]

private lemma lap_zero (d : ℕ) (f : HyperbolicChart.Space d → ℂ)
    (x : HyperbolicChart.Space d) (hx : x ∉ tsupport f) : HyperbolicChart.laplacian d f x = 0 := by
  rw [lap_local d f (fun _ => 0) x (notMem_tsupport_iff_eventuallyEq.mp hx)]
  have hz : ∀ i k, HyperbolicChart.coordinateDerivative d i k
      (fun _ => (0 : ℂ)) = fun _ => 0 := by
    intro i k; funext p; simp [HyperbolicChart.coordinateDerivative]
  simp only [HyperbolicChart.laplacian, hz]
  simp

private lemma compact_green (d : ℕ) (hd : 1 ≤ d)
    (Ω : Set (HyperbolicChart.Space d)) (hΩ : IsOpen Ω)
    (f g : HyperbolicChart.Space d → ℂ)
    (hf : HyperbolicChart.IsTestFunction d Ω f) (hg : HyperbolicChart.IsTestFunction d Ω g) :
    (∫ p in Ω, f p * star (HyperbolicChart.laplacian d g p) ∂HyperbolicChart.measure d) =
      ∫ p in Ω, HyperbolicChart.laplacian d f p * star (g p) ∂HyperbolicChart.measure d := by
  have hw : HyperbolicChart.IsTestField d Ω (fun _ => 0) := by
    refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
    simp
  have hfg := (kp_cont_hyperbolic_chart_green d hd Ω hΩ f g (fun _ => 0)
    hf hg hw 1 (by norm_num) 1 (by norm_num)).2.2.2.2.2
  have hgf := (kp_cont_hyperbolic_chart_green d hd Ω hΩ g f (fun _ => 0)
    hg hf hw 1 (by norm_num) 1 (by norm_num)).2.2.2.2.2
  have hmeasure : HyperbolicChart.chartMeasure d 1 1 = HyperbolicChart.measure d := by
    norm_num [HyperbolicChart.chartMeasure]
  rw [hmeasure] at hfg hgf
  have hs := congrArg star hfg
  have intstar (v : HyperbolicChart.Space d → ℂ) :
      (∫ p in Ω, star (v p) ∂HyperbolicChart.measure d) =
        star (∫ p in Ω, v p ∂HyperbolicChart.measure d) := by
    simpa only [starRingEnd_apply] using (integral_conj (f := v) (μ := (HyperbolicChart.measure d).restrict Ω))
  rw [← intstar, ← intstar] at hs
  calc
    _ = ∫ p in Ω, star (star (f p) * HyperbolicChart.laplacian d g p) ∂HyperbolicChart.measure d := by
      congr 1; funext p; simp [mul_comm]
    _ = ∫ p in Ω, star (HyperbolicChart.pairing d (HyperbolicChart.differential d f p)
      (HyperbolicChart.differential d g p)) ∂HyperbolicChart.measure d := hs
    _ = ∫ p in Ω, HyperbolicChart.pairing d (HyperbolicChart.differential d g p)
      (HyperbolicChart.differential d f p) ∂HyperbolicChart.measure d := by
      congr 1; funext p; simp [HyperbolicChart.pairing, star_sum, mul_comm]
    _ = _ := by rw [← hgf]; congr 1; funext p; ring

private lemma compact_localization {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Set E) (hΩ : IsOpen Ω)
    (K : Set E) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (f : E → ℂ)
    (hf : ContDiffOn ℝ ∞ f Ω) :
    ∃ F : E → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ Ω ∧
      ∀ x ∈ K, F =ᶠ[nhds x] f := by
  classical
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure hK hΩ hKΩ
  obtain ⟨W, hWo, hKW, hWV, hWc⟩ := exists_open_between_and_isCompact_closure hK hVo hKV
  obtain ⟨χ, hχ, hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hVo isClosed_closure hWV
  let F : E → ℂ := fun x => if x ∈ Ω then (χ x : ℂ) * f x else 0
  have hsupp : Function.support F ⊆ V := by
    intro x hx
    rw [← hχsupport]
    by_contra hn
    have hz : χ x = 0 := Function.notMem_support.mp hn
    by_cases hxo : x ∈ Ω <;> simp [F, hxo, hz] at hx
  have hts : tsupport F ⊆ closure V := closure_mono hsupp
  refine ⟨F, ?_, HasCompactSupport.of_support_subset_isCompact hVc (hsupp.trans subset_closure), hts.trans hVΩ, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Ω
    · apply (((Complex.ofRealCLM.contDiff.comp hχ).contDiffAt).mul
        (hf.contDiffAt (hΩ.mem_nhds hx))).congr_of_eventuallyEq
      filter_upwards [hΩ.mem_nhds hx] with y hy
      simp [F, hy]
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      have hv : x ∉ closure V := fun h => hx (hVΩ h)
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hv] with y hy
      exact Function.notMem_support.mp (fun h => hy (subset_closure (hsupp h)))
  · intro x hx
    filter_upwards [hWo.mem_nhds (hKW hx), hΩ.mem_nhds (hKΩ hx)] with y hyW hyΩ
    simp [F, hyΩ, (hχone y).mp (subset_closure hyW)]

private lemma local_green (d : ℕ) (hd : 1 ≤ d)
    (Ω : Set (HyperbolicChart.Space d)) (hΩ : IsOpen Ω)
    (f g : HyperbolicChart.Space d → ℂ)
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : HyperbolicChart.IsTestFunction d Ω g) :
    (∫ p in Ω, f p * star (HyperbolicChart.laplacian d g p) ∂HyperbolicChart.measure d) =
      ∫ p in Ω, HyperbolicChart.laplacian d f p * star (g p) ∂HyperbolicChart.measure d := by
  obtain ⟨F, hF, hFc, hFΩ, hFe⟩ := compact_localization Ω hΩ (tsupport g) hg.2.1 hg.2.2 f hf
  have hleft : (fun p => f p * star (HyperbolicChart.laplacian d g p)) =
      (fun p => F p * star (HyperbolicChart.laplacian d g p)) := by
    funext p
    by_cases hp : p ∈ tsupport g
    · rw [(hFe p hp).eq_of_nhds]
    · rw [lap_zero d g p hp, star_zero, mul_zero, mul_zero]
  have hright : (fun p => HyperbolicChart.laplacian d f p * star (g p)) =
      (fun p => HyperbolicChart.laplacian d F p * star (g p)) := by
    funext p
    by_cases hp : p ∈ tsupport g
    · rw [lap_local d F f p (hFe p hp)]
    · rw [image_eq_zero_of_notMem_tsupport hp, star_zero, mul_zero, mul_zero]
  rw [hleft, hright]
  exact compact_green d hd Ω hΩ F g ⟨hF, hFc, hFΩ⟩ hg

 def compactCoordHomeomorph :
    KPContCotangentActualOverlap.M F ≃ₜ KPCuspGenuineMonodromy.SymmetricSpace F where
  toFun := KPContCotangentActualOverlap.labeledA (KPContCotangentActualOverlap.placeEquiv F ζ hζ)
  invFun := KPContCotangentActualOverlap.labeledAInv (KPContCotangentActualOverlap.placeEquiv F ζ hζ)
  left_inv x := by
    simp [KPContCotangentActualOverlap.labeledAInv, KPContCotangentActualOverlap.labeledA]
  right_inv x := by
    funext k
    simp [KPContCotangentActualOverlap.labeledAInv, KPContCotangentActualOverlap.labeledA]
  continuous_toFun := continuous_labeledA_actual
  continuous_invFun := by
    apply (CotangentLogCoframe.A (KPContCotangentActualOverlap.d F)).symm.continuous.comp
    exact continuous_pi fun k => continuous_apply _

private lemma map_compact_coordinates (a : ShrunkChart F ζ hζ U R P H) :
    Measure.map (fun y : a.domain => (coordinates a y).val) a.liftedMeasure =
      ((H.disintegration U).componentWeight a.component / (Nat.card a.Isotropy : ℝ≥0∞)) •
        (HyperbolicChart.measure (d F)).restrict (omega a) := by
  let c₀ : ℝ≥0∞ :=
    (H.disintegration U).componentWeight a.component / (Nat.card a.Isotropy : ℝ≥0∞)
  let c := compactCoordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)
  have hbridge : Measure.map c.symm
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))
      = HyperbolicChart.measure (KPContCotangentActualOverlap.d F) :=
    map_labeledAInv_hyperbolicVolume
  have he : c.symm ⁻¹' omega a = a.domain := by
    ext x
    change c (c.symm x) ∈ a.domain ↔ x ∈ a.domain
    rw [c.apply_symm_apply]
  change Measure.map (c.symm ∘
      (Subtype.val : a.domain → KPCuspGenuineMonodromy.SymmetricSpace F))
      a.liftedMeasure
    = c₀ • (HyperbolicChart.measure (KPContCotangentActualOverlap.d F)).restrict (omega a)
  rw [show a.liftedMeasure = c₀ •
      Measure.comap (Subtype.val : a.domain → KPCuspGenuineMonodromy.SymmetricSpace F)
        ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict a.domain) from rfl]
  rw [Measure.map_smul c₀ ((c.symm.measurable.comp measurable_subtype_coe).aemeasurable)]
  congr 1
  change Measure.map (c.symm ∘
      (Subtype.val : a.domain → KPCuspGenuineMonodromy.SymmetricSpace F))
      (Measure.comap (Subtype.val : a.domain → KPCuspGenuineMonodromy.SymmetricSpace F)
        ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict a.domain))
    = (HyperbolicChart.measure (KPContCotangentActualOverlap.d F)).restrict (omega a)
  rw [← Measure.map_map (f := (Subtype.val : a.domain → KPCuspGenuineMonodromy.SymmetricSpace F))
    (g := c.symm) c.symm.measurable measurable_subtype_coe]
  rw [map_comap_subtype_coe a.domain_open.measurableSet]
  rw [Measure.restrict_restrict a.domain_open.measurableSet, Set.inter_self]
  rw [← hbridge]
  rw [c.symm.measurableEmbedding.restrict_map]
  rw [he]

theorem compact_interior_green_lift
    (a : ShrunkChart F ζ hζ U R P H)
    (s : ScalarFields F ζ hζ U R P H) (hs : SmoothOnLift a (s a))
    (g : localScalarTests a)
    (hgcompact : HasCompactSupport (liftExtension a g.val))
    (hginterior : tsupport (liftExtension a g.val) ⊆ omega a) :
    (∫ y, liftExtension a (s a) (coordinates a y).val *
        star (HyperbolicChart.laplacian (d F) (liftExtension a g.val)
          (coordinates a y).val) ∂a.liftedMeasure) =
      ∫ y, HyperbolicChart.laplacian (d F) (liftExtension a (s a))
          (coordinates a y).val *
        star (liftExtension a g.val (coordinates a y).val) ∂a.liftedMeasure := by
  have hd : 1 ≤ d F := by
    obtain ⟨h1, h2⟩ := (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2
    change 1 ≤ Module.finrank ℚ F / 2
    omega
  let f := liftExtension a (s a)
  let v := liftExtension a g.val
  have hf : ContDiffOn ℝ ∞ f (omega a) := by
    obtain ⟨f₀, hf₀, he⟩ := hs
    apply hf₀.congr
    intro x hx
    change liftExtension a (s a) x = f₀ x
    simp only [liftExtension, dite_eq_left hx]
    exact (he ⟨x, hx⟩).symm
  have hv : HyperbolicChart.IsTestFunction (d F) (omega a) v :=
    ⟨interior_liftExtension_contDiff a g.val g.property.1 hginterior, hgcompact, hginterior⟩
  have hgreen := local_green (d F) hd (omega a) (isOpen_omega_actual a) f v hf hv
  have hem : MeasurableEmbedding (fun y : a.domain => (coordinates a y).val) := by
    refine (compactCoordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)).symm.measurableEmbedding.comp ?_
    exact MeasurableEmbedding.subtype_coe a.domain_open.measurableSet
  change (∫ y, f (coordinates a y).val *
      star (HyperbolicChart.laplacian (d F) v (coordinates a y).val) ∂a.liftedMeasure) =
    ∫ y, HyperbolicChart.laplacian (d F) f (coordinates a y).val *
      star (v (coordinates a y).val) ∂a.liftedMeasure
  rw [← hem.integral_map (fun p => f p * star (HyperbolicChart.laplacian (d F) v p)),
    ← hem.integral_map (fun p => HyperbolicChart.laplacian (d F) f p * star (v p)),
    map_compact_coordinates, integral_smul_measure, integral_smul_measure, hgreen]

end DedekindZetaZeroFree.KPContActualGlobalGreen

end

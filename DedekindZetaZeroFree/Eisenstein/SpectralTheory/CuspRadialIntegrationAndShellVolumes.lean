module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.SphericalHaarDisintegrationData
public import DedekindZetaZeroFree.Adeles.Quotients.ArithmeticProperActionsAndOrbifoldCharts

@[expose] public section

noncomputable section

open scoped Classical NumberField ENNReal

open MeasureTheory

namespace DedekindZetaZeroFree.KPMsFixedHaar

namespace RadialIntegrationSteps

instance quotientOpens {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {s : Setoid α} : OpensMeasurableSpace (Quotient s) := by
  constructor
  apply MeasurableSpace.generateFrom_le
  intro E hE
  apply measurableSet_quotient.mpr
  exact (hE.preimage continuous_quotient_mk').measurableSet

end RadialIntegrationSteps

end DedekindZetaZeroFree.KPMsFixedHaar

end

section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsFixedHaar

namespace RadialIntegrationSteps

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : Level F ζ hζ} (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (D : GeometricDisintegration A R P)

theorem beta_probability_lintegral (f : Omega A → ℝ≥0∞) :
    D.beta Set.univ * (∫⁻ ω, f ω ∂probability A D.beta) = ∫⁻ ω, f ω ∂D.beta := by
  letI := D.finite_beta
  rw [probability, lintegral_smul_measure]
  exact ENNReal.mul_inv_cancel_left D.positive_beta (measure_ne_top _ _)

theorem probability_section_lintegral (f : CrossSection A → ℝ≥0∞) (hf : Measurable f) :
    D.beta Set.univ * (∫⁻ ω, ∫⁻ x, f x ∂D.unipotent ω ∂probability A D.beta) =
      ∑ j : CuspIndex A,
        (D.componentWeight j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
          ∫⁻ x, f ⟨j,x⟩ ∂(Geometry A j).sectionMeasure := by
  rw [beta_probability_lintegral]
  exact (D.section_disintegration f hf).symm

theorem endMap_embedding (j : CuspIndex A) (T : ℝ) (hT : A.threshold ≤ T) :
    Topology.IsEmbedding (KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2) T) := by
  let C := A.cuspAtlas j.1
  let G := C.geometry j.2
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1)
  let eT := KPFiniteCuspAtlas.endMap F Γ (C.cusp j.2) (C.representative j.2) T
  let e₀ := KPFiniteCuspAtlas.endMap F Γ (C.cusp j.2) (C.representative j.2) C.threshold
  let inc : Set.Ioi T → Set.Ioi C.threshold := fun t =>
    ⟨t.val, by
      change C.threshold < t.val
      rw [show C.threshold = A.threshold from A.common_threshold j.1]
      exact lt_of_le_of_lt hT t.property⟩
  have hinc : Topology.IsEmbedding inc := by
    apply Topology.IsEmbedding.of_comp (continuous_subtype_val.subtype_mk _) continuous_subtype_val
    exact Topology.IsEmbedding.subtypeVal
  have heq : eT ∘ G.highPresentation T =
      e₀ ∘ G.highPresentation C.threshold ∘ Prod.map id inc := by
    funext x
    rcases x with ⟨p,t⟩
    induction p using Quotient.inductionOn with
    | h p =>
      simp only [Function.comp_apply, Prod.map_apply, id_eq,
        G.highPresentation_formula]
      rfl
  have hcomp : Topology.IsEmbedding (eT ∘ G.highPresentation T) := by
    rw [heq]
    exact (C.end_embedding j.2).comp
      ((G.highPresentation C.threshold).isEmbedding.comp
        (Topology.IsEmbedding.id.prodMap hinc))
  have hfinal := hcomp.comp (G.highPresentation T).symm.isEmbedding
  have heq' : (eT ∘ G.highPresentation T) ∘ (G.highPresentation T).symm = eT := by
    funext x
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  rw [heq'] at hfinal
  exact hfinal

theorem end_volume_at_cutoff (j : CuspIndex A) (T : ℝ) (hT : A.threshold ≤ T) :
    Measure.map (KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2) T)
      (Measure.map ((Geometry A j).highPresentation T)
        ((Geometry A j).sectionMeasure.prod
          (Measure.comap (Subtype.val : Set.Ioi T → ℝ)
            (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))))) =
    (KPFiniteCuspAtlas.quotientVolume F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      (A.cuspAtlas j.1).fundamentalDomain).restrict
        (KPFiniteCuspAtlas.endSet F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
          ((A.cuspAtlas j.1).representative j.2) T) := by
  exact KPFiniteAdelicCuspEnds.embedded_cusp_end_volume F hF _ _ _
    ((A.cuspAtlas j.1).representative_formula j.2) T (Parabolic A j) (Geometry A j) _
    (fun _ => rfl) (endMap_embedding A j T hT) _
    (A.cuspAtlas j.1).measurable_fundamentalDomain (A.cuspAtlas j.1).isFundamentalDomain

theorem spherical_open_positive : (sphericalMeasure F ζ hζ R P U).IsOpenPosMeasure := by
  letI : BorelSpace (X F ζ hζ) := ⟨rfl⟩
  letI := (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1
  apply (P.continuous U).isOpenPosMeasure_map
  intro x
  induction x using Quotient.inductionOn with
  | h x =>
    rcases x with ⟨x,c⟩
    let e : {v : NumberField.InfinitePlace F // v.IsComplex} ≃ Fin (KPCuspLogShape.dimension F) :=
      Fintype.equivFin _
    let g : KPSmoothActualFlowData.GInfinity F := fun v =>
      if hv : v.IsComplex then
        Matrix.ProjGenLinGroup.mk (KPArithmeticAction.hyperbolicGLSection (x (e ⟨v,hv⟩)))
      else 1
    refine ⟨KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ g * c), ?_⟩
    rw [P.formula]
    congr 1
    apply Prod.ext
    swap
    · rfl
    funext i
    change KPArch.action (g (KPCusp.complexPlace F i)).out (0,0) = x i
    have hc : (KPCusp.complexPlace F i).IsComplex := (e.symm i).property
    simp only [g, dif_pos hc]
    have hi : e ⟨KPCusp.complexPlace F i, hc⟩ = i := by
      exact e.apply_symm_apply i
    rw [hi]
    have he : KPArch.action (Quotient.out (Matrix.ProjGenLinGroup.mk
        (KPArithmeticAction.hyperbolicGLSection (x i)))) (0,0) =
        KPArch.action (KPArithmeticAction.hyperbolicGLSection (x i)) (0,0) := by
      have heq : Matrix.ProjGenLinGroup.mk (Quotient.out (Matrix.ProjGenLinGroup.mk
          (KPArithmeticAction.hyperbolicGLSection (x i)))) =
          Matrix.ProjGenLinGroup.mk (KPArithmeticAction.hyperbolicGLSection (x i)) :=
        Quotient.out_eq _
      obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp heq
      calc
        _ = KPArch.action ((Matrix.ProjGenLinGroup.mk
            (KPArithmeticAction.hyperbolicGLSection (x i))).out *
            Matrix.GeneralLinearGroup.scalar (Fin 2) u) (0,0) := by
          rw [(KPArch.action_laws _ _ _).2, KPArch.scalar_action]
        _ = _ := congrArg (fun k => KPArch.action k (0,0)) hu
    rw [he]
    exact KPArithmeticAction.hyperbolicGLSection_action (x i)

theorem end_coordinate_lintegral (j : CuspIndex A) (T : ℝ) (hT : A.threshold ≤ T)
    (φ : KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1)) → ℝ≥0∞)
    (hφ : Measurable φ) :
    (∫⁻ x in KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).representative j.2) T, φ x ∂KPFiniteCuspAtlas.quotientVolume F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      (A.cuspAtlas j.1).fundamentalDomain) =
    ∫⁻ p : KPCuspCharts.Coordinates F,
      φ (KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
        (((A.cuspAtlas j.1).representative j.2) • KPCuspCharts.toArch F p))
      ∂((((volume.prod (Geometry A j).shapeMeasure).prod
        (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))).restrict
        {p : KPCuspCharts.Coordinates F | p.1 ∈ (Geometry A j).fundamentalDomain}).restrict
        {p : KPCuspCharts.Coordinates F | T < p.2}) := by
  rw [← end_volume_at_cutoff A j T hT]
  rw [KPFiniteAdelicCuspEnds.cusp_end_coordinate_volume F hF _ _ _ T
    (Parabolic A j) (Geometry A j) _ (fun _ => rfl)]
  apply lintegral_map hφ
  exact measurable_quotient_mk''.comp
    ((KPCuspCharts.projectiveHomeomorph F ((A.cuspAtlas j.1).representative j.2)).continuous.measurable.comp
      (KPCuspCharts.toArchHomeomorph F (Geometry A j).positive_dimension).continuous.measurable)

theorem end_section_lintegral (j : CuspIndex A) (T : ℝ) (hT : A.threshold ≤ T)
    (φ : KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1)) → ℝ≥0∞)
    (hφ : Measurable φ) :
    (∫⁻ x in KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).representative j.2) T, φ x ∂KPFiniteCuspAtlas.quotientVolume F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      (A.cuspAtlas j.1).fundamentalDomain) =
    ∫⁻ t : Set.Ioi T, ∫⁻ p,
      φ (KPFiniteCuspAtlas.endMap F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
        ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2) T
        ((Geometry A j).highPresentation T (p,t))) ∂(Geometry A j).sectionMeasure
      ∂Measure.comap (Subtype.val : Set.Ioi T → ℝ)
        (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)) := by
  let G := Geometry A j
  let σ := (A.cuspAtlas j.1).representative j.2
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1)
  let f : KPCuspCharts.Coordinates F → ℝ≥0∞ := fun p =>
    φ (KPCuspSiegel.projection F Γ (σ • KPCuspCharts.toArch F p))
  have hf : Measurable f := hφ.comp (measurable_quotient_mk''.comp
    ((KPCuspCharts.projectiveHomeomorph F σ).continuous.measurable.comp
      (KPCuspCharts.toArchHomeomorph F G.positive_dimension).continuous.measurable))
  let μ := (volume.prod G.shapeMeasure).restrict G.fundamentalDomain
  let ν := KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)
  letI := G.haar_shapeMeasure
  letI : SFinite μ := inferInstance
  letI : SFinite ν := by unfold ν KPCuspCharts.radialMeasure; infer_instance
  rw [end_coordinate_lintegral A j T hT φ hφ]
  change (∫⁻ p, f p ∂((((volume.prod G.shapeMeasure).prod ν).restrict
    {p | p.1 ∈ G.fundamentalDomain}).restrict {p | T < p.2})) = _
  have heq : (((volume.prod G.shapeMeasure).prod ν).restrict
      {p : KPCuspCharts.Coordinates F | p.1 ∈ G.fundamentalDomain}).restrict
      {p | T < p.2} = μ.prod (ν.restrict (Set.Ioi T)) := by
    rw [Measure.restrict_restrict (measurableSet_lt measurable_const measurable_snd),
      Measure.prod_restrict]
    congr 1
    ext p
    simp [μ, Set.mem_prod, and_comm]
  rw [heq, lintegral_prod_symm' _ hf]
  rw [← lintegral_subtype_comap measurableSet_Ioi]
  apply lintegral_congr
  intro t
  rw [G.sectionMeasure_formula]
  rw [lintegral_map]
  · apply lintegral_congr
    intro p
    rw [(Geometry A j).highPresentation_formula]
    rfl
  · apply measurable_from_quotient.mpr
    convert hf.comp (measurable_id.prodMk (measurable_const (a := t.val))) using 1
    funext p
    simp only [Function.comp_apply]
    rw [(Geometry A j).highPresentation_formula]
    rfl
  · exact measurable_quotient_mk''

theorem shape_shift_fundamental_lintegral (j : CuspIndex A) (b : KPCuspCharts.Shape F)
    (f : KPCuspCharts.Cross F → ℝ≥0∞)
    (hinv : ∀ g p, f ((Geometry A j).crossAction g p) = f p) :
    (∫⁻ p in (Geometry A j).fundamentalDomain, f (p.1,p.2+b)
      ∂volume.prod (Geometry A j).shapeMeasure) =
    ∫⁻ p in (Geometry A j).fundamentalDomain, f p
      ∂volume.prod (Geometry A j).shapeMeasure := by
  let G := Geometry A j
  let S := KPCuspArithmetic.conjugatedStabilizer F
    (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
    ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2)
  letI := KPCuspCharts.homeomorphAction G.crossAction
  letI : MeasurableConstSMul S (KPCuspCharts.Cross F) :=
    ⟨fun g => (G.crossAction g).continuous.measurable⟩
  letI : SMulInvariantMeasure S (KPCuspCharts.Cross F) (volume.prod G.shapeMeasure) := by
    constructor
    intro g E hE
    have hh := congrArg (fun μ : Measure (KPCuspCharts.Cross F) => μ E) (G.measure_invariant g)
    rw [Measure.map_apply (G.crossAction g).continuous.measurable hE] at hh
    exact hh
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  letI : Countable (KPCuspArithmetic.PGL2 F) :=
    Matrix.ProjGenLinGroup.mk_surjective.countable
  let e := (Homeomorph.refl (KPCuspCharts.Horizontal F)).prodCongr (Homeomorph.addRight b)
  letI := G.haar_shapeMeasure
  have hp : MeasurePreserving e (volume.prod G.shapeMeasure) (volume.prod G.shapeMeasure) :=
    (MeasurePreserving.id volume).prod (measurePreserving_add_right G.shapeMeasure b)
  have hm : MeasurePreserving e.symm (volume.prod G.shapeMeasure) (volume.prod G.shapeMeasure) :=
    (MeasurePreserving.id volume).prod (measurePreserving_add_right G.shapeMeasure (-b))
  have hc : ∀ g : S, Function.Semiconj e (g • ·) (g • ·) := by
    intro g p
    obtain ⟨M,hM,hupper⟩ := (Parabolic A j).upper g g.property
    change e (G.crossAction g p) = G.crossAction g (e p)
    rw [G.crossAction_formula g M hM hupper, G.crossAction_formula g M hM hupper]
    apply Prod.ext
    · rfl
    · change (p.2 + _)+ b = (p.2+b)+ _
      abel
  have hd := G.isFundamentalDomain.image_of_equiv e.toEquiv hm.quasiMeasurePreserving
    (Equiv.refl S) hc
  calc
    _ = ∫⁻ p in e '' G.fundamentalDomain, f p ∂volume.prod G.shapeMeasure :=
      hp.setLIntegral_comp_emb e.measurableEmbedding f G.fundamentalDomain
    _ = _ := hd.setLIntegral_eq G.isFundamentalDomain f hinv

theorem radial_log_substitution (d : ℕ) (hd : 0 < d) (Y : ℝ) (hY : 0 < Y)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ r in Set.Ioi Y, f r ∂radialMeasure) =
    ENNReal.ofReal (2*(d:ℝ)) * ∫⁻ t in Set.Ioi (Real.log Y/(2*(d:ℝ))),
      f (Real.exp (2*(d:ℝ)*t)) ∂KPCuspCharts.radialMeasure d := by
  let c : ℝ := 2 * d
  have hc : 0 < c := mul_pos (by norm_num) (by exact_mod_cast hd)
  have hi : Set.InjOn (fun t : ℝ => Real.exp (c*t)) (Set.Ioi (Real.log Y/c)) := by
    intro x hx y hy he
    exact mul_left_cancel₀ hc.ne' (Real.exp_injective he)
  have himage : (fun t : ℝ => Real.exp (c*t)) '' Set.Ioi (Real.log Y/c) = Set.Ioi Y := by
    ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      have hh : Real.log Y < c*t := by simpa only [mul_comm] using (div_lt_iff₀ hc).mp ht
      simpa only [Real.exp_log hY, Set.mem_Ioi] using Real.exp_lt_exp.mpr hh
    · intro hr
      refine ⟨Real.log r/c, ?_, ?_⟩
      · exact (div_lt_div_iff_of_pos_right hc).mpr (Real.log_lt_log hY hr)
      · change Real.exp (c * (Real.log r/c)) = r
        rw [mul_div_cancel₀ _ hc.ne', Real.exp_log (lt_trans hY hr)]
  have hder : ∀ t ∈ Set.Ioi (Real.log Y/c),
      HasDerivWithinAt (fun t : ℝ => Real.exp (c*t)) (c*Real.exp (c*t))
        (Set.Ioi (Real.log Y/c)) t := by
    intro t ht
    simpa only [Function.comp_def, mul_one, one_mul, mul_comm] using ((Real.hasDerivAt_exp (c*t)).comp t
      ((hasDerivAt_id t).const_mul c)).hasDerivWithinAt
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hi
    (fun r => ENNReal.ofReal (r^2)⁻¹ * f r)
  rw [himage] at hj
  have hfinite : ∀ᵐ x ∂volume.restrict (Set.Ioi Y), ENNReal.ofReal (x^2)⁻¹ < ∞ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal (x^2)⁻¹) :=
    (measurable_id.pow_const 2).inv.ennreal_ofReal
  rw [radialMeasure, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable
    volume hm f (s := Set.Ioi Y) measurableSet_Ioi hfinite]
  change (∫⁻ r in Set.Ioi Y, ENNReal.ofReal (r^2)⁻¹ * f r) = _
  rw [hj]
  have hfinite' : ∀ᵐ x ∂volume.restrict (Set.Ioi (Real.log Y/c)),
      ENNReal.ofReal (Real.exp (-2*(d:ℝ)*x)) < ∞ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hm' : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-2*(d:ℝ)*x))) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.ennreal_ofReal
  rw [KPCuspCharts.radialMeasure, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable
    volume hm' _ (s := Set.Ioi (Real.log Y/(2*(d:ℝ)))) measurableSet_Ioi hfinite']
  simp only [Pi.mul_apply, show (-2*(d:ℝ)) = -c by dsimp [c]; ring]
  change _ = ENNReal.ofReal c * ∫⁻ t in Set.Ioi (Real.log Y/c),
    ENNReal.ofReal (Real.exp (-c*t)) * f (Real.exp (c*t))
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro t
  rw [abs_of_pos (mul_pos hc (Real.exp_pos _)), ← mul_assoc,
    ← ENNReal.ofReal_mul (le_of_lt (mul_pos hc (Real.exp_pos _)))]
  have he : c * Real.exp (c*t) * ((Real.exp (c*t))^2)⁻¹ = c * Real.exp (-c*t) := by
    rw [neg_mul, Real.exp_neg]
    field_simp
  rw [he, ENNReal.ofReal_mul hc.le, mul_assoc]

theorem quotient_cross_action (j : CuspIndex A) (g) (p : KPCuspCharts.Cross F) :
    (Quotient.mk _ ((Geometry A j).crossAction g p) : KPCuspCharts.CrossQuotient F
      (KPCuspArithmetic.conjugatedStabilizer F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
        ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2))) =
      Quotient.mk _ p := by
  apply Quotient.sound
  change MulAction.orbitRel _ _ (KPCuspCharts.toArch F (_,0)) (KPCuspCharts.toArch F (p,0))
  apply MulAction.orbitRel_apply.mpr
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨g, ?_⟩
  obtain ⟨M,hM,hupper⟩ := (Parabolic A j).upper g g.property
  rw [(Geometry A j).crossAction_formula g M hM hupper]
  exact (Geometry A j).actual_action g M hM hupper (p,0)

theorem shape_shift_section_lintegral (j : CuspIndex A) (b : KPCuspCharts.Shape F)
    (f : KPCuspCharts.CrossQuotient F
      (KPCuspArithmetic.conjugatedStabilizer F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
        ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2)) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ p in (Geometry A j).fundamentalDomain,
      f (Quotient.mk _ (p.1,p.2+b)) ∂volume.prod (Geometry A j).shapeMeasure) =
    ∫⁻ p, f p ∂(Geometry A j).sectionMeasure := by
  rw [(Geometry A j).sectionMeasure_formula, lintegral_map hf measurable_quotient_mk'']
  exact shape_shift_fundamental_lintegral A j b (fun p => f (Quotient.mk _ p))
    (fun g p => by rw [quotient_cross_action A j g p])

 abbrev component (i : Fin A.componentCount) :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i)
 abbrev ends (j : CuspIndex A) (T : ℝ) := KPFiniteCuspAtlas.endSet F
  (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
  ((A.cuspAtlas j.1).representative j.2) T
 theorem component_continuous (i : Fin A.componentCount) : Continuous (component A i) := by
  have he : component A i = A.components ∘ Sigma.mk i := by
    funext x
    exact (A.components_formula i x).symm
  rw [he]
  exact A.components.continuous.comp continuous_sigmaMk
private theorem component_open (i : Fin A.componentCount) : IsOpenMap (component A i) := by
  have he : component A i = A.components ∘ Sigma.mk i := by
    funext x
    exact (A.components_formula i x).symm
  rw [he]
  exact A.components.isOpenMap.comp isOpenMap_sigmaMk
private theorem component_injective (i : Fin A.componentCount) : Function.Injective (component A i) := by
  intro x y h
  have h' : A.components ⟨i,x⟩ = A.components ⟨i,y⟩ := by
    simpa only [A.components_formula] using h
  exact eq_of_heq (Sigma.mk.inj_iff.mp (A.components.injective h')).2
private theorem ends_subset (j : CuspIndex A) {T₀ T : ℝ} (hT : T₀ ≤ T) :
    ends A j T ⊆ ends A j T₀ := by
  apply Set.image_mono
  apply Set.image_mono
  intro z hz
  exact lt_of_le_of_lt hT hz
 theorem end_preimage (j : CuspIndex A) (T : ℝ) :
    component A j.1 ⁻¹' (component A j.1 '' ends A j T) = ends A j T :=
  Set.preimage_image_eq _ (component_injective A j.1)
 theorem end_measurable (j : CuspIndex A) (T : ℝ) :
    MeasurableSet (component A j.1 '' ends A j T) := by
  exact ((component_open A j.1) _
    (KPFiniteAdelicCuspEnds.component_open_end F _ _ T)).measurableSet
private theorem end_disjoint (T : ℝ) (hT : A.threshold ≤ T) :
    Pairwise (fun j k : CuspIndex A => Disjoint
      (component A j.1 '' ends A j T) (component A k.1 '' ends A k T)) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
  have he' : A.components ⟨k.1,y⟩ = A.components ⟨j.1,x⟩ := by
    simpa only [A.components_formula] using he
  have hij : k.1 = j.1 := (Sigma.mk.inj_iff.mp (A.components.injective he')).1
  rcases j with ⟨i,a⟩
  rcases k with ⟨l,b⟩
  dsimp at hij
  subst l
  have hxy : y = x := component_injective A i he
  subst y
  have hab : a ≠ b := by intro h; subst b; exact hjk rfl
  have hd := (A.cuspAtlas i).disjoint_ends hab
  apply Set.disjoint_left.mp hd
  · apply ends_subset A ⟨i,a⟩ (T₀ := (A.cuspAtlas i).threshold) (T := T)
      (by rw [A.common_threshold]; exact hT) hx
  · apply ends_subset A ⟨i,b⟩ (T₀ := (A.cuspAtlas i).threshold) (T := T)
      (by rw [A.common_threshold]; exact hT) hy

theorem cusp_component_lintegral (Y : ℝ) (hY : AdmissibleCutoff A Y)
    (φ : Spherical F ζ hζ U → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ x in cuspEnds A Y, φ x ∂sphericalMeasure F ζ hζ R P U) =
    ∑ j : CuspIndex A, D.componentWeight j.1 *
      ∫⁻ x in KPFiniteCuspAtlas.endSet F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
        ((A.cuspAtlas j.1).representative j.2) (logHeight (F := F) Y),
        φ (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) x)
        ∂KPFiniteCuspAtlas.quotientVolume F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
          (A.cuspAtlas j.1).fundamentalDomain := by
  rw [cuspEnds, lintegral_iUnion (end_measurable A · _) (end_disjoint A _ hY.2), tsum_fintype]
  apply Finset.sum_congr rfl
  intro j hj
  let E := component A j.1 '' ends A j (logHeight (F := F) Y)
  have hE : MeasurableSet E := end_measurable A j _
  have hsub : E ⊆ Set.range (component A j.1) := Set.image_subset_range _ _
  have heq : ((sphericalMeasure F ζ hζ R P U).restrict (Set.range (component A j.1))).restrict E =
      (sphericalMeasure F ζ hζ R P U).restrict E := by
    rw [Measure.restrict_restrict hE, Set.inter_eq_left.mpr hsub]
  change (∫⁻ x, φ x ∂(sphericalMeasure F ζ hζ R P U).restrict E) = _
  rw [← heq, D.component_measure]
  rw [Measure.restrict_smul]
  rw [Measure.restrict_map (component_continuous A j.1).measurable hE]
  rw [lintegral_smul_measure, lintegral_map hφ (component_continuous A j.1).measurable]
  rw [end_preimage A j]
  rfl

theorem pinned_section (j : CuspIndex A) (Y : ℝ) (hY : AdmissibleCutoff A Y)
    (r : Set.Ioi Y) (t : Set.Ioi (logHeight (F := F) Y))
    (ht : logHeight (F := F) r.val = t.val)
    (φ : Spherical F ζ hζ U → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ p, φ (D.chart Y hY (⟨j,p⟩,r)) ∂(Geometry A j).sectionMeasure) =
    ∫⁻ p, φ (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1)
      (KPFiniteCuspAtlas.endMap F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
        ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2)
        (logHeight (F := F) Y) ((Geometry A j).highPresentation _ (p,t))))
      ∂(Geometry A j).sectionMeasure := by
  let G := Geometry A j
  let σ := (A.cuspAtlas j.1).representative j.2
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1)
  let b := sectionShape F hF D.radial.slot ⟨r.val, lt_trans hY.1 r.property⟩
  let f := fun p => φ (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1)
    (KPFiniteCuspAtlas.endMap F Γ ((A.cuspAtlas j.1).cusp j.2) σ
      (logHeight (F := F) Y) (G.highPresentation _ (p,t))))
  have hf : Measurable f := by
    apply measurable_from_quotient.mpr
    have hm : Measurable (fun p : KPCuspCharts.Cross F => φ
        (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1)
          (KPCuspSiegel.projection F Γ (σ • KPCuspCharts.toArch F (p,t.val))))) :=
      hφ.comp ((component_continuous A j.1).measurable.comp (measurable_quotient_mk''.comp
        ((KPCuspCharts.projectiveHomeomorph F σ).continuous.measurable.comp
          ((KPCuspCharts.toArchHomeomorph F G.positive_dimension).continuous.measurable.comp
            (measurable_id.prodMk measurable_const)))))
    convert hm using 1
    funext p
    dsimp [Function.comp_def, f]
    rw [G.highPresentation_formula]
    rfl
  have hleft : Measurable (fun p => φ (D.chart Y hY (⟨j,p⟩,r))) :=
    hφ.comp ((D.measurable_chart Y hY).comp
      ((continuous_sigmaMk.measurable).prodMk measurable_const))
  conv_lhs => rw [G.sectionMeasure_formula, lintegral_map hleft measurable_quotient_mk'']
  have heq : (fun p : KPCuspCharts.Cross F => φ (D.chart Y hY (⟨j,Quotient.mk _ p⟩,r))) =
      fun p => f (Quotient.mk _ (p.1,p.2+b)) := by
    funext p
    rw [D.chart_formula]
    dsimp [f]
    rw [G.highPresentation_formula]
    dsimp [KPFiniteCuspAtlas.endMap]
    rw [ht]
    rfl
  rw [heq]
  exact shape_shift_section_lintegral A j b f hf

def expRadius (d : ℕ) (hd : 0 < d) (Y : ℝ) (hY : 0 < Y)
    (t : Set.Ioi (Real.log Y/(2*(d:ℝ)))) : Set.Ioi Y :=
  ⟨Real.exp (2*(d:ℝ)*t.val), by
    have hc : 0 < 2*(d:ℝ) := mul_pos (by norm_num) (by exact_mod_cast hd)
    have hh : Real.log Y < 2*(d:ℝ)*t.val := by
      simpa only [mul_comm] using (div_lt_iff₀ hc).mp t.property
    simpa only [Real.exp_log hY, Set.mem_Ioi] using Real.exp_lt_exp.mpr hh⟩
theorem radial_subtype_substitution (d : ℕ) (hd : 0 < d) (Y : ℝ) (hY : 0 < Y)
    (g : Set.Ioi Y → ℝ≥0∞) :
    (∫⁻ r, g r ∂Measure.comap (Subtype.val : Set.Ioi Y → ℝ) radialMeasure) =
    ENNReal.ofReal (2*(d:ℝ)) * ∫⁻ t, g (expRadius d hd Y hY t)
      ∂Measure.comap (Subtype.val : Set.Ioi (Real.log Y/(2*(d:ℝ))) → ℝ)
        (KPCuspCharts.radialMeasure d) := by
  let f : ℝ → ℝ≥0∞ := Function.extend (Subtype.val : Set.Ioi Y → ℝ) g (fun _ => 0)
  have hfg : ∀ r : Set.Ioi Y, f r.val = g r :=
    Subtype.val_injective.extend_apply g _
  calc
    _ = ∫⁻ r : Set.Ioi Y, f r.val ∂Measure.comap Subtype.val radialMeasure :=
      lintegral_congr (fun r => (hfg r).symm)
    _ = ∫⁻ r in Set.Ioi Y, f r ∂radialMeasure := lintegral_subtype_comap measurableSet_Ioi _
    _ = _ := by
      rw [radial_log_substitution d hd Y hY f, ← lintegral_subtype_comap measurableSet_Ioi]
      congr 1
      apply lintegral_congr
      intro t
      exact hfg (expRadius d hd Y hY t)

theorem pinned_end (j : CuspIndex A) (Y : ℝ) (hY : AdmissibleCutoff A Y)
    (φ : Spherical F ζ hζ U → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ x in KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).representative j.2) (logHeight (F := F) Y),
      φ (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) x)
      ∂KPFiniteCuspAtlas.quotientVolume F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
        (A.cuspAtlas j.1).fundamentalDomain) =
    (ENNReal.ofReal (2*(KPCuspLogShape.dimension F:ℝ)))⁻¹ *
      ∫⁻ r, ∫⁻ p, φ (D.chart Y hY (⟨j,p⟩,r)) ∂(Geometry A j).sectionMeasure
        ∂Measure.comap (Subtype.val : Set.Ioi Y → ℝ) radialMeasure := by
  let d := KPCuspLogShape.dimension F
  have hd := (Geometry A j).positive_dimension
  have hlog : ∀ t : Set.Ioi (logHeight (F := F) Y),
      logHeight (F := F) (expRadius d hd Y hY.1 t).val = t.val := by
    intro t
    dsimp [expRadius, logHeight, d]
    rw [Real.log_exp, mul_div_cancel_left₀]
    exact mul_ne_zero (by norm_num) (by exact_mod_cast hd.ne')
  have hh := end_section_lintegral A j _ hY.2 _ (hφ.comp (component_continuous A j.1).measurable)
  simp only [Function.comp_apply] at hh
  rw [hh]
  rw [radial_subtype_substitution d hd Y hY.1]
  rw [ENNReal.inv_mul_cancel_left (ENNReal.ofReal_ne_zero_iff.mpr
    (mul_pos (by norm_num) (by exact_mod_cast hd))) ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro t
  exact (pinned_section A R P D j Y hY (expRadius d hd Y hY.1 t) t (hlog t) φ hφ).symm

theorem cusp_integration (Y : ℝ) (hY : AdmissibleCutoff A Y)
    (φ : Spherical F ζ hζ U → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ x in cuspEnds A Y, φ x ∂sphericalMeasure F ζ hζ R P U) =
    D.beta Set.univ * ∫⁻ r : Set.Ioi Y, ∫⁻ ω, ∫⁻ x,
      φ (D.chart Y hY (x,r)) ∂D.unipotent ω ∂probability A D.beta
      ∂Measure.comap (Subtype.val : Set.Ioi Y → ℝ) radialMeasure := by
  let g : CuspIndex A → Set.Ioi Y → ℝ≥0∞ := fun j r =>
    ∫⁻ p, φ (D.chart Y hY (⟨j,p⟩,r)) ∂(Geometry A j).sectionMeasure
  have hg : ∀ j, Measurable (g j) := by
    intro j
    letI := (Geometry A j).finite_sectionMeasure
    apply Measurable.lintegral_prod_left
    exact hφ.comp ((D.measurable_chart Y hY).comp
      ((continuous_sigmaMk.measurable.comp measurable_fst).prodMk measurable_snd))
  rw [cusp_component_lintegral A R P D Y hY φ hφ]
  simp_rw [pinned_end A R P D _ Y hY φ hφ, ← mul_assoc, ← div_eq_mul_inv]
  letI := D.finite_beta
  rw [← lintegral_const_mul' _ _ (measure_ne_top D.beta Set.univ)]
  have heq : ∀ r : Set.Ioi Y,
      D.beta Set.univ * (∫⁻ ω, ∫⁻ x, φ (D.chart Y hY (x,r))
        ∂D.unipotent ω ∂probability A D.beta) =
      ∑ j : CuspIndex A, (D.componentWeight j.1 / ENNReal.ofReal (2*(KPCuspLogShape.dimension F:ℝ))) * g j r := by
    intro r
    exact probability_section_lintegral A R P D _
      (hφ.comp ((D.measurable_chart Y hY).comp (measurable_id.prodMk measurable_const)))
  simp_rw [heq]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    exact (lintegral_const_mul _ (hg j)).symm
  · intro j hj
    exact measurable_const.mul (hg j)

theorem radial_shell (Y : ℝ) (hY : 0 < Y) :
    radialMeasure (Set.Ioc Y (2*Y)) = ENNReal.ofReal (2*Y)⁻¹ := by
  have hab : Y ≤ 2*Y := by linarith
  have hc : ContinuousOn (fun r : ℝ => (r^2)⁻¹) (Set.Icc Y (2*Y)) :=
    (continuous_id.pow 2).continuousOn.inv₀ (fun x hx => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hY hx.1)))
  have hi : IntegrableOn (fun r : ℝ => (r^2)⁻¹) (Set.Ioc Y (2*Y)) :=
    hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  rw [radialMeasure, withDensity_apply _ measurableSet_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun r => inv_nonneg.mpr (sq_nonneg r)))]
  rw [← intervalIntegral.integral_of_le hab]
  have heq : (fun r : ℝ => (r^2)⁻¹) = fun r => r ^ (-2 : ℝ) := by
    funext r
    rw [Real.rpow_neg_ofNat]
    simp
  rw [heq, integral_rpow (Or.inr ⟨by norm_num, ?_⟩)]
  · norm_num
    rw [Real.rpow_neg_one, Real.rpow_neg_one]
    congr 1
    field_simp
    ring
  · rw [Set.uIcc_of_le hab]
    intro h
    exact (not_le_of_gt hY) h.1

theorem shell_eval (Y : ℝ) (hY : AdmissibleCutoff A Y)
    (hrad : radialMeasure (Set.Ioc Y (2*Y)) = ENNReal.ofReal (2*Y)⁻¹) :
    D.beta Set.univ = ENNReal.ofReal (2*Y) *
      sphericalMeasure F ζ hζ R P U
        (cuspEnds A Y ∩ {x : Spherical F ζ hζ U | Y < D.modulus x ∧ D.modulus x ≤ 2*Y}) := by
  let E := {x : Spherical F ζ hζ U | Y < D.modulus x ∧ D.modulus x ≤ 2*Y}
  have hE : MeasurableSet E :=
    (measurableSet_lt measurable_const D.measurable_modulus).inter
      (measurableSet_le D.measurable_modulus measurable_const)
  have hi := cusp_integration A R P D Y hY (E.indicator (fun _ => 1))
    (measurable_const.indicator hE)
  have hi' : sphericalMeasure F ζ hζ R P U (cuspEnds A Y ∩ E) =
      D.beta Set.univ * radialMeasure (Set.Ioc Y (2*Y)) := by
    rw [lintegral_indicator hE, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, Measure.restrict_apply hE, Set.inter_comm] at hi
    simp only [one_mul] at hi
    have heq : ∀ r : Set.Ioi Y, ∀ x : CrossSection A,
        E.indicator (fun _ => (1 : ℝ≥0∞)) (D.chart Y hY (x,r)) =
        (Set.Iic (2*Y)).indicator (fun _ => (1 : ℝ≥0∞)) r.val := by
      intro r x
      simp only [E, Set.indicator_apply, Set.mem_setOf_eq, D.chart_modulus, Set.mem_Iic]
      have hr : Y < r.val := r.property
      simp only [hr, true_and]
    simp_rw [heq] at hi
    letI := D.probability_mass
    have hkernel : ∀ r : Set.Ioi Y, ∀ ω : Omega A,
        (∫⁻ x, (Set.Iic (2*Y)).indicator (fun _ => (1 : ℝ≥0∞)) r.val ∂D.unipotent ω) =
        (Set.Iic (2*Y)).indicator (fun _ => (1 : ℝ≥0∞)) r.val := by
      intro r ω
      letI := D.probability_unipotent ω
      simp
    simp_rw [hkernel] at hi
    simp only [lintegral_const, measure_univ, mul_one] at hi
    rw [lintegral_subtype_comap measurableSet_Ioi, lintegral_indicator measurableSet_Iic,
      lintegral_const, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, Measure.restrict_apply measurableSet_Iic] at hi
    have hs : Set.Iic (2*Y) ∩ Set.Ioi Y = Set.Ioc Y (2*Y) := by ext r; simp [and_comm]
    rw [hs, one_mul] at hi
    exact hi
  rw [hi', hrad]
  have hpos : 0 < 2*Y := mul_pos (by norm_num) hY.1
  have hmul := ENNReal.mul_inv_cancel_left (ENNReal.ofReal_ne_zero_iff.mpr hpos)
    ENNReal.ofReal_ne_top (b := D.beta Set.univ)
  calc
    _ = ENNReal.ofReal (2*Y) * ((ENNReal.ofReal (2*Y))⁻¹ * D.beta Set.univ) := hmul.symm
    _ = _ := by rw [ENNReal.ofReal_inv_of_pos hpos, mul_comm (D.beta Set.univ)]

end RadialIntegrationSteps

theorem fixed_haar_radial_integration
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : Level F ζ hζ} (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (D : GeometricDisintegration A R P) :
    RadialIntegration A R P D := by
  refine ⟨RadialIntegrationSteps.cusp_integration A R P D, ?_,
    RadialIntegrationSteps.spherical_open_positive R P⟩
  intro Y hY
  exact RadialIntegrationSteps.shell_eval A R P D Y hY
    (RadialIntegrationSteps.radial_shell Y hY.1)

end DedekindZetaZeroFree.KPMsFixedHaar

end
end

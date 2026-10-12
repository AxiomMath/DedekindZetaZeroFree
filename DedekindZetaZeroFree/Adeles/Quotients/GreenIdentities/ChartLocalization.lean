module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.HyperbolicCharts.LogarithmicCoframe
public import DedekindZetaZeroFree.Adeles.Quotients.GreenIdentities.InteriorZeroExtension

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualGlobalGreen

open KPContActualCotangentCountableShrinking
open KPContActualCotangentMeasurableFamilies
open KPContActualSectorTestDifferentialDescent
open KPContActualCotangentChartRestriction
open KPContActualSectorTestEmbeddings
open KPContActualSectorSmoothTestModules
open KPContCotangentOverlapRationalBranches

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

 def coordHomeomorph :
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

theorem chart_base_localization (a : ShrunkChart F ζ hζ U R P H)
    (G : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ)
    (hG : tsupport G ⊆ a.baseDomain)
    (hint : Integrable G (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U)) :
    ∫ x, G x ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U =
      ∫ y, G (a.toBase y) ∂a.liftedMeasure := by
  have hp := every_shrunkChart_properties F ζ hζ U R P H a
  have hzero : ∀ x, x ∉ a.baseDomain → G x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hG h))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  rw [show (∫ x in a.baseDomain, G x
        ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U)
      = ∫ x, G x
        ∂(KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict
          a.baseDomain from rfl]
  rw [← hp.exact_pushforward]
  rw [integral_map hp.measurable.aemeasurable]
  exact (hint.aestronglyMeasurable.restrict).mono_measure (le_of_eq hp.exact_pushforward)

theorem local_chart_green (a : ShrunkChart F ζ hζ U R P H)
    (φ : S_U F ζ hζ U R P H) (W : T_U F ζ hζ U R P H)
    (hφ : HasCompactSupport (liftExtension a (φ.val a)))
    (hφs : tsupport (liftExtension a (φ.val a)) ⊆ omega a)
    (hW : HasCompactSupport (fun p : KPContCotangentActualOverlap.M F =>
      (CotangentLogCoframe.j (KPContCotangentActualOverlap.d F)).symm
        (liftExtension a (coefficient W.val a) p)))
    (hWs : tsupport (fun p : KPContCotangentActualOverlap.M F =>
      (CotangentLogCoframe.j (KPContCotangentActualOverlap.d F)).symm
        (liftExtension a (coefficient W.val a) p)) ⊆ omega a) :
    (∫ y, inner ℂ (localCoefficient a (D_U φ).val y) (localCoefficient a W.val y)
        ∂a.liftedMeasure) =
      ∫ y, inner ℂ (localScalarCoefficient a φ y) (localScalarCoefficient a (δ_U W) y)
        ∂a.liftedMeasure := by
  have hd : 1 ≤ KPContCotangentActualOverlap.d F := by
    obtain ⟨h1, h2⟩ := (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2
    change 1 ≤ Module.finrank ℚ F / 2
    omega
  let f : KPContCotangentActualOverlap.M F → ℂ := liftExtension a (φ.val a)
  let w := liftExtension a (coefficient W.val a)
  let W' : KPContCotangentActualOverlap.M F →
      HyperbolicChart.Cotangent (KPContCotangentActualOverlap.d F) :=
    fun p => (CotangentLogCoframe.j (KPContCotangentActualOverlap.d F)).symm (w p)
  let c₀ : ℝ≥0∞ :=
    (H.disintegration U).componentWeight a.component / (Nat.card a.Isotropy : ℝ≥0∞)
  have hprops := every_shrunkChart_properties F ζ hζ U R P H a
  have hfin : (H.disintegration U).componentWeight a.component < ⊤ := hprops.normalization_finite
  have hpos : 0 < (H.disintegration U).componentWeight a.component := hprops.normalization_positive
  have hc₀0 : c₀ ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨hpos.ne', ENNReal.natCast_ne_top _⟩
  have hcard : (Nat.card a.Isotropy : ℝ≥0∞) ≠ 0 := by
    haveI : Finite a.Isotropy := hprops.finite_isotropy
    haveI : Nonempty a.Isotropy := ⟨1⟩
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hc₀T : c₀ ≠ ⊤ := ENNReal.div_ne_top hfin.ne hcard
  have hc₀pos : 0 < c₀.toReal := ENNReal.toReal_pos hc₀0 hc₀T
  have hchart : HyperbolicChart.chartMeasure (KPContCotangentActualOverlap.d F) c₀.toReal 1
      = c₀ • HyperbolicChart.measure (KPContCotangentActualOverlap.d F) := by
    rw [HyperbolicChart.chartMeasure]
    simp only [Nat.cast_one, div_one]
    rw [ENNReal.ofReal_toReal hc₀T]
  have hz : Measure.map
        (fun y : a.domain => (KPContActualCotangentPieceHilbertSum.coordinates a y).val)
        a.liftedMeasure
      = c₀ • (HyperbolicChart.measure (KPContCotangentActualOverlap.d F)).restrict (omega a) := by
    let c := coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)
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
    change Measure.map (c.symm ∘
        (Subtype.val : a.domain → KPCuspGenuineMonodromy.SymmetricSpace F))
        (c₀ • Measure.comap (Subtype.val : a.domain → KPCuspGenuineMonodromy.SymmetricSpace F)
          ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict a.domain))
      = c₀ • (HyperbolicChart.measure (KPContCotangentActualOverlap.d F)).restrict (omega a)
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
  have hts : tsupport W' = tsupport w := by
    have hsupp : Function.support W' = Function.support w := by
      ext p
      simp only [Function.mem_support]
      exact not_congr (CotangentLogCoframe.j (KPContCotangentActualOverlap.d F)).symm.map_eq_zero_iff
    show closure (Function.support W') = closure (Function.support w)
    rw [hsupp]
  have hws : tsupport w ⊆ omega a := hts ▸ hWs
  have hwc : ContDiff ℝ ∞ w :=
    interior_liftExtension_contDiff a (coefficient W.val a) (W.property.1 a) hws
  have hW'c : ContDiff ℝ ∞ W' := by
    change ContDiff ℝ ∞ (fun p => fun (i : Fin (KPContCotangentActualOverlap.d F)) (k : Fin 3) =>
      w p (i, k))
    rw [contDiff_pi]
    intro i
    rw [contDiff_pi]
    intro k
    exact ((EuclideanSpace.proj (𝕜 := ℂ) (i, k)).restrictScalars ℝ).contDiff.comp hwc
  have hW't : HyperbolicChart.IsTestField (KPContCotangentActualOverlap.d F) (omega a) W' :=
    ⟨hW'c, hW, hWs⟩
  have hfc : ContDiff ℝ ∞ f :=
    interior_liftExtension_contDiff a (φ.val a) (φ.property.1 a) hφs
  have hft : HyperbolicChart.IsTestFunction (KPContCotangentActualOverlap.d F) (omega a) f :=
    ⟨hfc, hφ, hφs⟩
  have hgreen := kp_cont_hyperbolic_chart_green (KPContCotangentActualOverlap.d F) hd (omega a)
    (isOpen_omega_actual a) f f W' hft hft hW't c₀.toReal hc₀pos 1 le_rfl
  have hL : (∫ y, inner ℂ (localCoefficient a (D_U φ).val y) (localCoefficient a W.val y)
        ∂a.liftedMeasure) =
      ∫ p in omega a, HyperbolicChart.pairing (KPContCotangentActualOverlap.d F)
        (HyperbolicChart.differential (KPContCotangentActualOverlap.d F) f p) (W' p)
        ∂HyperbolicChart.chartMeasure (KPContCotangentActualOverlap.d F) c₀.toReal 1 := by
    have hp : ∀ y : a.domain,
        inner ℂ (localCoefficient a (D_U φ).val y) (localCoefficient a W.val y)
          = HyperbolicChart.pairing (KPContCotangentActualOverlap.d F)
              (HyperbolicChart.differential (KPContCotangentActualOverlap.d F) f
                ((KPContActualCotangentPieceHilbertSum.coordinates a y).val))
              (W' ((KPContActualCotangentPieceHilbertSum.coordinates a y).val)) := by
      intro y
      have h1 : localCoefficient a (D_U φ).val y
          = CotangentLogCoframe.j (KPContCotangentActualOverlap.d F)
              (HyperbolicChart.differential (KPContCotangentActualOverlap.d F) f
                ((KPContActualCotangentPieceHilbertSum.coordinates a y).val)) := rfl
      have hWl : w ((KPContActualCotangentPieceHilbertSum.coordinates a y).val)
          = coefficient W.val a (KPContActualCotangentPieceHilbertSum.coordinates a y) := by
        unfold w liftExtension
        simp only [dif_pos (KPContActualCotangentPieceHilbertSum.coordinates a y).property]
      have h2 : localCoefficient a W.val y
          = CotangentLogCoframe.j (KPContCotangentActualOverlap.d F)
              (W' ((KPContActualCotangentPieceHilbertSum.coordinates a y).val)) := by
        show localCoefficient a W.val y
          = CotangentLogCoframe.j (KPContCotangentActualOverlap.d F)
              ((CotangentLogCoframe.j (KPContCotangentActualOverlap.d F)).symm
                (w ((KPContActualCotangentPieceHilbertSum.coordinates a y).val)))
        rw [hWl]
        simp [localCoefficient, coefficient]
      rw [h1, h2, CotangentLogCoframe.inner_j]
    rw [show (∫ y, inner ℂ (localCoefficient a (D_U φ).val y) (localCoefficient a W.val y) ∂a.liftedMeasure)
        = ∫ y : a.domain, HyperbolicChart.pairing (KPContCotangentActualOverlap.d F)
            (HyperbolicChart.differential (KPContCotangentActualOverlap.d F) f
              ((KPContActualCotangentPieceHilbertSum.coordinates a y).val))
            (W' ((KPContActualCotangentPieceHilbertSum.coordinates a y).val))
          ∂a.liftedMeasure from integral_congr_ae (ae_of_all a.liftedMeasure hp)]
    have hzem : MeasurableEmbedding
        (fun y : a.domain => (KPContActualCotangentPieceHilbertSum.coordinates a y).val) := by
      refine (coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)).symm.measurableEmbedding.comp ?_
      exact MeasurableEmbedding.subtype_coe a.domain_open.measurableSet
    rw [← hzem.integral_map (fun p => HyperbolicChart.pairing (KPContCotangentActualOverlap.d F)
      (HyperbolicChart.differential (KPContCotangentActualOverlap.d F) f p) (W' p)), hz,
      integral_smul_measure, hchart, Measure.restrict_smul, integral_smul_measure]
  have hR : (∫ y, inner ℂ (localScalarCoefficient a φ y)
        (localScalarCoefficient a (δ_U W) y) ∂a.liftedMeasure) =
      ∫ p in omega a, star (f p) *
        HyperbolicChart.codifferential (KPContCotangentActualOverlap.d F) W' p
        ∂HyperbolicChart.chartMeasure (KPContCotangentActualOverlap.d F) c₀.toReal 1 := by
    have hp : ∀ y : a.domain,
        inner ℂ (localScalarCoefficient a φ y) (localScalarCoefficient a (δ_U W) y)
          = star (f ((KPContActualCotangentPieceHilbertSum.coordinates a y).val)) *
              HyperbolicChart.codifferential (KPContCotangentActualOverlap.d F) W'
                ((KPContActualCotangentPieceHilbertSum.coordinates a y).val) := by
      intro y
      have h1 : localScalarCoefficient a φ y
          = f ((KPContActualCotangentPieceHilbertSum.coordinates a y).val) := by
        unfold f liftExtension
        simp only [dif_pos (KPContActualCotangentPieceHilbertSum.coordinates a y).property]
        rfl
      have h2 : localScalarCoefficient a (δ_U W) y
          = HyperbolicChart.codifferential (KPContCotangentActualOverlap.d F) W'
              ((KPContActualCotangentPieceHilbertSum.coordinates a y).val) := by
        show localScalarCoefficient a (δ_U W) y
          = HyperbolicChart.codifferential (KPContCotangentActualOverlap.d F)
              (fun y => (CotangentLogCoframe.j (KPContCotangentActualOverlap.d F)).symm (w y))
              ((KPContActualCotangentPieceHilbertSum.coordinates a y).val)
        rfl
      rw [h1, h2, RCLike.inner_apply']
      rfl
    rw [show (∫ y, inner ℂ (localScalarCoefficient a φ y)
          (localScalarCoefficient a (δ_U W) y) ∂a.liftedMeasure)
        = ∫ y : a.domain,
            star (f ((KPContActualCotangentPieceHilbertSum.coordinates a y).val)) *
              HyperbolicChart.codifferential (KPContCotangentActualOverlap.d F) W'
                ((KPContActualCotangentPieceHilbertSum.coordinates a y).val)
          ∂a.liftedMeasure from integral_congr_ae (ae_of_all a.liftedMeasure hp)]
    have hzem : MeasurableEmbedding
        (fun y : a.domain => (KPContActualCotangentPieceHilbertSum.coordinates a y).val) := by
      refine (coordHomeomorph (F := F) (ζ := ζ) (hζ := hζ)).symm.measurableEmbedding.comp ?_
      exact MeasurableEmbedding.subtype_coe a.domain_open.measurableSet
    rw [← hzem.integral_map (fun p => star (f p) *
      HyperbolicChart.codifferential (KPContCotangentActualOverlap.d F) W' p), hz,
      integral_smul_measure, hchart, Measure.restrict_smul, integral_smul_measure]
  rw [hL, hR, hgreen.2.2.2.2.1]

end DedekindZetaZeroFree.KPContActualGlobalGreen

end

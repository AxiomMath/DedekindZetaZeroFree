module

public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.SmoothScalarAndCotangentTests
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Cusps.CutoffGraphApproximation

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPContActualPartitionTransport
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
open KPContSectorSmoothFramesSupport KPContActualCotangentCountableShrinking
open KPContActualSectorSmoothTestModules KPContActualCotangentPieceHilbertSum

open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra

 theorem unit_product (u : Circle) (z w : ℂ) :
    (u : ℂ) * z * star ((u : ℂ) * w) = z * star w := by
  have hu : (u : ℂ) * star (u : ℂ) = 1 := by
    simpa [Complex.mul_conj] using u.normSq_coe
  rw [star_mul]
  calc _ = ((u : ℂ) * star (u : ℂ)) * (z * star w) := by ring
       _ = _ := by rw [hu, one_mul]

 def componentPair {V : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (s t : Sections F ζ hζ V R P H) (i : Fin (H.atlas V).componentCount) :
    KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ V ((H.atlas V).representative i)) → ℂ :=
  Quotient.lift (fun x => (s i).val x * star ((t i).val x)) (by
    intro x y hxy
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hxy)
    rw [← hγ]
    change (s i).val ((γ : KPCuspArithmetic.PGL2 F) • y) *
      star ((t i).val ((γ : KPCuspArithmetic.PGL2 F) • y)) = _
    rw [(s i).property.2 γ y, (t i).property.2 γ y]
    rw [← chi_coe F ζ hζ]
    exact unit_product _ _ _)

 def basePair {V : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (s t : Sections F ζ hζ V R P H) : KPMsFixedHaarDisintegration.Spherical F ζ hζ V → ℂ :=
  fun b => let p := (H.atlas V).components.symm b; componentPair s t p.1 p.2

private theorem basePair_component {V : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (s t : Sections F ζ hζ V R P H) (i : Fin (H.atlas V).componentCount)
    (x : SymmetricSpace F) :
    basePair s t ((H.atlas V).components ⟨i, Quotient.mk _ x⟩) =
      (s i).val x * star ((t i).val x) := by
  simp only [basePair, componentPair]
  rw [Homeomorph.symm_apply_apply, Quotient.lift_mk]

private theorem basePair_continuous {V : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (s t : Sections F ζ hζ V R P H)
    (hs : ∀ i, Continuous (s i).val) (ht : ∀ i, Continuous (t i).val) :
    Continuous (basePair s t) := by
  have hc : Continuous (fun p : Σ i, KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ V ((H.atlas V).representative i)) =>
      componentPair s t p.1 p.2) := by
    apply continuous_sigma
    intro i
    apply continuous_coinduced_dom.mpr
    change Continuous (fun x => (s i).val x * star ((t i).val x))
    exact (hs i).mul (ht i).star
  exact hc.comp (H.atlas V).components.symm.continuous

private theorem basePair_pullback {V : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (s t : Sections F ζ hζ V R P H) (v : CoveredSpherical F ζ hζ V) :
    basePair s t (q F ζ hζ V v) =
      ((S F ζ hζ V R P H).symm s).val v *
      star (((S F ζ hζ V R P H).symm t).val v) := by
  obtain ⟨⟨i, w⟩, rfl⟩ :=
    (KPContSectorPhaseComponentCharts.componentHomeomorph F ζ hζ V R P H).surjective v
  refine Quotient.inductionOn w ?_
  rintro ⟨m, x⟩
  refine Quotient.inductionOn m ?_
  intro ε
  rw [KPContSectorPhaseComponentCharts.componentHomeomorph_forget]
  change basePair s t ((H.atlas V).components ⟨i, Quotient.mk _ x⟩) = _
  rw [basePair_component, phase_component_restriction, phase_component_restriction]
  simp only [LinearEquiv.apply_symm_apply, phaseCoefficient_class]
  exact (unit_product _ _ _).symm

private theorem basePair_zero {V : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (s t : Sections F ζ hζ V R P H)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ V))
    (hT : ∀ j z, KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex V (H.atlas V) j z ∉ K →
      (t j).val z = 0) (b : KPFiniteCuspAtlas.rawXU F ζ hζ V) (hb : b ∉ K) :
    basePair s t b = 0 := by
  obtain ⟨⟨i, x⟩, rfl⟩ := (H.atlas V).components.surjective b
  refine Quotient.inductionOn x (fun z hb => ?_) hb
  rw [basePair_component, hT i z, star_zero, mul_zero]
  simpa only [KPCuspCutoffGraph.basePoint, KPCuspSiegel.projection,
    (H.atlas V).components_formula] using hb

private theorem basePair_chart {V : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (s t : Sections F ζ hζ V R P H) (a : ShrunkChart F ζ hζ V R P H) (y : a.domain) :
    basePair s t (a.toBase y) = sectionFields s a (coordinates a y) *
      star (sectionFields t a (coordinates a y)) := by
  have hf : a.toBase y = (H.atlas V).components ⟨a.component, Quotient.mk _ y.val⟩ :=
    ((H.atlas V).components_formula _ _).symm
  rw [hf, basePair_component]
  have hi : KPContCotangentActualOverlap.labeledA
      (KPContCotangentActualOverlap.placeEquiv F ζ hζ)
      (KPContCotangentActualOverlap.labeledAInv
        (KPContCotangentActualOverlap.placeEquiv F ζ hζ) y.val) = y.val := by
    funext k
    simp [KPContCotangentActualOverlap.labeledA,
      KPContCotangentActualOverlap.labeledAInv]
  simp [sectionFields, KPContCotangentActualOverlap.LiftedChart.coefficient,
    KPContCotangentActualGenuineTwistIsotropy.isotropyChart, coordinates, hi,
    KPContCotangentActualOverlap.ChartKind.representative]

theorem compact_original_scalar_chart_transport
    (V : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (s t : Sections F ζ hζ V R P H)
    (hs : ∀ i, Continuous (s i).val) (ht : ∀ i, Continuous (t i).val)
    (a : ShrunkChart F ζ hζ V R P H)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ V)) (hK : IsCompact K)
    (hKa : K ⊆ a.baseDomain)
    (hT : ∀ j z, KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex V (H.atlas V) j z ∉ K →
      (t j).val z = 0) :
    Integrable (fun x => ((KPContSectorScalarLineAlgebra.S F ζ hζ V R P H).symm s).val x *
      star (((KPContSectorScalarLineAlgebra.S F ζ hζ V R P H).symm t).val x))
      (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R V) ∧
    ((∫ x, ((KPContSectorScalarLineAlgebra.S F ζ hζ V R P H).symm s).val x *
      star (((KPContSectorScalarLineAlgebra.S F ζ hζ V R P H).symm t).val x)
      ∂KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R V) =
      ∫ y, sectionFields s a (coordinates a y) *
        star (sectionFields t a (coordinates a y)) ∂a.liftedMeasure) := by
  let μ := KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R V
  let ν := KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P V
  have ha := every_shrunkChart_properties F ζ hζ V R P H a
  have hc := basePair_continuous s t hs ht
  have hzero := basePair_zero s t K hT
  have hcomp : HasCompactSupport (basePair s t) := HasCompactSupport.intro hK hzero
  letI := KPContSectorFixedMeasureLocalFiniteness.sphericalMeasure_finiteOnCompacts F ζ hζ R P V
  have hi : Integrable (basePair s t) ν := hc.integrable_of_hasCompactSupport hcomp
  have hq := (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ V).measurable
  have hmap : Measure.map (q F ζ hζ V) μ = ν :=
    KPContSectorFixedPushforwardSupport.map_q_coveredMeasure F ζ hζ R P V
  have hip : Integrable (basePair s t ∘ q F ζ hζ V) μ := by
    exact (hmap.symm ▸ hi).comp_measurable hq
  have hcov : (fun x => ((S F ζ hζ V R P H).symm s).val x *
      star (((S F ζ hζ V R P H).symm t).val x)) = basePair s t ∘ q F ζ hζ V := by
    funext x
    exact (basePair_pullback s t x).symm
  rw [hcov]
  refine ⟨hip, ?_⟩
  calc
    (∫ x, (basePair s t ∘ q F ζ hζ V) x ∂μ) = ∫ b, basePair s t b ∂ν := by
      rw [← hmap]
      exact (integral_map hq.aemeasurable hc.aestronglyMeasurable).symm
    _ = ∫ b in a.baseDomain, basePair s t b ∂ν := by
      rw [← setIntegral_univ]
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (Set.subset_univ _)
      intro b hb
      exact hzero b (fun h => hb.2 (hKa h))
    _ = ∫ y, basePair s t (a.toBase y) ∂a.liftedMeasure := by
      rw [← ha.exact_pushforward]
      exact integral_map ha.measurable.aemeasurable
        hc.aestronglyMeasurable
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (basePair_chart s t a))

end DedekindZetaZeroFree.KPContActualPartitionTransport

end

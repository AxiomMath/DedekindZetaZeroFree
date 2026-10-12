module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Quotients.FiniteOrbitIntegration
public import DedekindZetaZeroFree.Metaplectic.Cubic.LineBundles.SmoothSectionsAndSupport

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPContSectorFixedLineNormIntegrals

open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra
open KPContSectorSmoothFramesSupport KPContSectorFixedPushforwardSupport
open KPMsFixedHaarDisintegration

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def lineNorm (f : GenuineCoveredScalars F ζ hζ U) :
    KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞ :=
  fun b => ENNReal.ofReal (sectionNorm F ζ hζ U R P H (S F ζ hζ U R P H f) b ^ 2)

def componentLineNorm (f : GenuineCoveredScalars F ζ hζ U)
    (i : Fin (H.atlas U).componentCount) :
    KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i)) → ℝ≥0∞ :=
  fun x => ENNReal.ofReal
    (componentNorm F ζ hζ U R P H (S F ζ hζ U R P H f) i x ^ 2)

structure NormIdentities (f : GenuineCoveredScalars F ζ hζ U) : Prop where

  fiber_norm : ∀ v w : CoveredSpherical F ζ hζ U,
    q F ζ hζ U v = q F ζ hζ U w → ‖f.val v‖ ^ 2 = ‖f.val w‖ ^ 2

  pullback : ∀ v : CoveredSpherical F ζ hζ U,
    lineNorm F ζ hζ U R P H f (q F ζ hζ U v) = ENNReal.ofReal (‖f.val v‖ ^ 2)

  borel : Measurable (lineNorm F ζ hζ U R P H f)

  unique : ∀ n : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞,
    (∀ v, n (q F ζ hζ U v) = ENNReal.ofReal (‖f.val v‖ ^ 2)) →
      n = lineNorm F ζ hζ U R P H f
  component : ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F),
    lineNorm F ζ hζ U R P H f ((H.atlas U).components ⟨i, Quotient.mk _ x⟩) =
      ENNReal.ofReal (‖(S F ζ hζ U R P H f i).val x‖ ^ 2)
  component_pullback : ∀ (i : Fin (H.atlas U).componentCount)
      (x : KPCuspSiegel.OrbitQuotient F
        (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))),
    lineNorm F ζ hζ U R P H f
      (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i) x) =
        componentLineNorm F ζ hζ U R P H f i x
  component_borel : ∀ i, Measurable (componentLineNorm F ζ hζ U R P H f i)

  restricted_pushforward : ∀ E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), MeasurableSet E →
    (∫⁻ v in (q F ζ hζ U) ⁻¹' E, ENNReal.ofReal (‖f.val v‖ ^ 2)
      ∂coveredMeasure F ζ hζ R U) =
    ∫⁻ b in E, lineNorm F ζ hζ U R P H f b ∂sphericalMeasure F ζ hζ R P U

  cutoff_pushforward : ∀ (c : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞), Measurable c →
    ∀ E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), MeasurableSet E →
    (∫⁻ v in (q F ζ hζ U) ⁻¹' E,
      c (q F ζ hζ U v) * ENNReal.ofReal (‖f.val v‖ ^ 2) ∂coveredMeasure F ζ hζ R U) =
    ∫⁻ b in E, c b * lineNorm F ζ hζ U R P H f b ∂sphericalMeasure F ζ hζ R P U

  component_integral : ∀ E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), MeasurableSet E →
    (∫⁻ b in E, lineNorm F ζ hζ U R P H f b ∂sphericalMeasure F ζ hζ R P U) =
    ∑ i : Fin (H.atlas U).componentCount, (H.disintegration U).componentWeight i *
      ∫⁻ x in (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i)) ⁻¹' E,
        componentLineNorm F ζ hζ U R P H f i x
        ∂KPFiniteCuspAtlas.quotientVolume F
          (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
          ((H.atlas U).cuspAtlas i).fundamentalDomain
  cutoff_component_integral :
    ∀ (c : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞), Measurable c →
    ∀ E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), MeasurableSet E →
    (∫⁻ b in E, c b * lineNorm F ζ hζ U R P H f b ∂sphericalMeasure F ζ hζ R P U) =
    ∑ i : Fin (H.atlas U).componentCount, (H.disintegration U).componentWeight i *
      ∫⁻ x in (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i)) ⁻¹' E,
        c (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i) x) *
          componentLineNorm F ζ hζ U R P H f i x
        ∂KPFiniteCuspAtlas.quotientVolume F
          (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
          ((H.atlas U).cuspAtlas i).fundamentalDomain

  cusp_integral : ∀ (Y : ℝ) (hY : AdmissibleCutoff (H.atlas U) Y),
    (∫⁻ b in cuspEnds (H.atlas U) Y, lineNorm F ζ hζ U R P H f b
      ∂sphericalMeasure F ζ hζ R P U) =
    (H.disintegration U).beta Set.univ *
      ∫⁻ r : Set.Ioi Y, ∫⁻ ω, ∫⁻ x,
        lineNorm F ζ hζ U R P H f ((H.disintegration U).chart Y hY (x,r))
        ∂(H.disintegration U).unipotent ω ∂probability (H.atlas U) (H.disintegration U).beta
        ∂Measure.comap (Subtype.val : Set.Ioi Y → ℝ) radialMeasure

  cutoff_cusp_integral : ∀ (Y : ℝ) (hY : AdmissibleCutoff (H.atlas U) Y)
      (c : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞), Measurable c →
    ∀ E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), MeasurableSet E →
    (∫⁻ b in cuspEnds (H.atlas U) Y ∩ E,
      c b * lineNorm F ζ hζ U R P H f b ∂sphericalMeasure F ζ hζ R P U) =
    (H.disintegration U).beta Set.univ *
      ∫⁻ r : Set.Ioi Y, ∫⁻ ω, ∫⁻ x,
        E.indicator (fun b => c b * lineNorm F ζ hζ U R P H f b)
          ((H.disintegration U).chart Y hY (x,r))
        ∂(H.disintegration U).unipotent ω ∂probability (H.atlas U) (H.disintegration U).beta
        ∂Measure.comap (Subtype.val : Set.Ioi Y → ℝ) radialMeasure

  chart_coefficient : ∀ (Y : ℝ) (hY : AdmissibleCutoff (H.atlas U) Y)
      (j : CuspIndex (H.atlas U)) (p : KPCuspCharts.Cross F) (r : Set.Ioi Y),
    lineNorm F ζ hζ U R P H f ((H.disintegration U).chart Y hY (⟨j, Quotient.mk _ p⟩,r)) =
    ENNReal.ofReal (‖cuspCoefficient F ζ hζ U R P H (S F ζ hζ U R P H f) j.1 j.2
      ((p.1, p.2 + sectionShape F H.totallyComplex (H.disintegration U).radial.slot
        ⟨r.val, lt_trans hY.1 r.property⟩), logHeight (F := F) r.val)‖ ^ 2)

  cutoff_section_integral : ∀ (Y : ℝ) (hY : AdmissibleCutoff (H.atlas U) Y)
      (c : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞), Measurable c →
    (∫⁻ b in cuspEnds (H.atlas U) Y, c b * lineNorm F ζ hζ U R P H f b
      ∂sphericalMeasure F ζ hζ R P U) =
    ∫⁻ r : Set.Ioi Y, ∑ j : CuspIndex (H.atlas U),
      ((H.disintegration U).componentWeight j.1 /
        ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
        ∫⁻ x, c ((H.disintegration U).chart Y hY (⟨j,x⟩,r)) *
          lineNorm F ζ hζ U R P H f ((H.disintegration U).chart Y hY (⟨j,x⟩,r))
          ∂(Geometry (H.atlas U) j).sectionMeasure
      ∂Measure.comap (Subtype.val : Set.Ioi Y → ℝ) radialMeasure

  lp_norm : ∀ hf : MemLp f.val 2 (coveredMeasure F ζ hζ R U),
    ‖hf.toLp f.val‖ ^ 2 =
      (∫⁻ b, lineNorm F ζ hζ U R P H f b ∂sphericalMeasure F ζ hζ R P U).toReal

end DedekindZetaZeroFree.KPContSectorFixedLineNormIntegrals

namespace DedekindZetaZeroFree

open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra
open KPContSectorSmoothFramesSupport KPContSectorFixedPushforwardSupport
open KPContSectorFiniteOrbitIntegral KPContSectorFixedLineNormIntegrals
open KPContSectorQuotientRelationsComparison
open KPMsFixedHaarDisintegration

private theorem fixedLine_sigma_integral {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, OpensMeasurableSpace (X i)]
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : (Σ i, X i) ≃ₜ Y) (μ : Measure Y) (w : ι → ℝ≥0∞) (ν : ∀ i, Measure (X i))
    (hm : ∀ i, μ.restrict (Set.range (fun x : X i => e ⟨i,x⟩)) =
      w i • Measure.map (fun x : X i => e ⟨i,x⟩) (ν i))
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y ∂μ) = ∑ i, w i * ∫⁻ x, g (e ⟨i,x⟩) ∂ν i := by
  classical
  let s : ι → Set Y := fun i => Set.range (fun x : X i => e ⟨i,x⟩)
  have hs : ∀ i, MeasurableSet (s i) := by
    intro i
    have heq : s i = e '' Set.range (@Sigma.mk ι X i) := by
      exact Set.range_comp e (@Sigma.mk ι X i)
    rw [heq]
    exact (e.isOpenMap _ isOpen_range_sigmaMk).measurableSet
  have hd : Pairwise (fun i j => Disjoint (s i) (s j)) := by
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨x, rfl⟩ ⟨z, he⟩
    have h := congrArg Sigma.fst (e.injective he)
    exact hij h.symm
  have hu : (⋃ i, s i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨⟨i,x⟩, rfl⟩ := e.surjective y
    exact Set.mem_iUnion.mpr ⟨i, x, rfl⟩
  have hμ : μ = Measure.sum (fun i => μ.restrict (s i)) := by
    rw [← Measure.restrict_iUnion hd hs, hu, Measure.restrict_univ]
  rw [hμ, lintegral_sum_measure, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  have hmi : Measurable (fun x : X i => e ⟨i,x⟩) :=
    (e.continuous.comp continuous_sigmaMk).measurable
  rw [hm i, lintegral_smul_measure, lintegral_map hg hmi]
  rfl

theorem kp_cont_sector_fixed_line_norm_integrals
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (f : KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ U)
    (hf : Measurable f.val) :
    KPContSectorFixedLineNormIntegrals.NormIdentities F ζ hζ U R P H f := by
  classical
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  let ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞ :=
    fun v => ENNReal.ofReal (‖f.val v‖ ^ 2)
  have hψ : Measurable ψ :=
    ENNReal.measurable_ofReal.comp (hf.norm.pow_const 2)
  have hqm : Measurable (q F ζ hζ U) := (q_continuous F ζ hζ U).measurable
  have hpull : ∀ v : CoveredSpherical F ζ hζ U,
      lineNorm F ζ hζ U R P H f (q F ζ hζ U v) = ENNReal.ofReal (‖f.val v‖ ^ 2) := by
    intro v
    simp only [lineNorm, sectionNorm_pullback F ζ hζ U R P H f v]
  have havg : ∀ v : CoveredSpherical F ζ hζ U,
      centralAverage F ζ hζ U ψ v = ENNReal.ofReal (‖f.val v‖ ^ 2) := by
    intro v
    have hsum : (∑ ε : rootsOfUnity 3 F, ψ (z F ζ hζ U ε v)) = 3 * ψ v := by
      refine Quotient.inductionOn v ?_
      intro p
      obtain ⟨x, c⟩ := p
      have hterm : ∀ ε : rootsOfUnity 3 F,
          ψ (z F ζ hζ U ε (Quotient.mk _ (x, c))) = ψ (Quotient.mk _ (x, c)) := by
        intro ε
        have hε : f.val (Quotient.mk (coveredRelation F ζ hζ U)
              (x, KPCuspGenuineMonodromy.central F ζ hζ ε * c)) =
            (chi F ζ hζ ε : ℂ) * f.val (Quotient.mk (coveredRelation F ζ hζ U) (x, c)) := by
          have h := f.property ε (Quotient.mk (coveredRelation F ζ hζ U) (x, c))
          simpa only [z_mk] using h
        show ENNReal.ofReal (‖f.val (z F ζ hζ U ε
              (Quotient.mk (coveredRelation F ζ hζ U) (x, c)))‖ ^ 2) =
            ENNReal.ofReal (‖f.val (Quotient.mk (coveredRelation F ζ hζ U) (x, c))‖ ^ 2)
        rw [z_mk, hε, norm_mul]
        rw [show ‖((chi F ζ hζ) ε : ℂ)‖ = 1 by
          rw [chi_coe F ζ hζ ε]; exact chi_norm F ζ hζ ε]
        rw [one_mul]
      rw [Finset.sum_congr rfl (fun ε _ => hterm ε), Finset.sum_const, Finset.card_univ,
        ← Nat.card_eq_fintype_card, card_cubic_center F ζ hζ]
      simp
    simp only [centralAverage]
    rw [hsum, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  have hdesc : borelDescent F ζ hζ U ψ hψ = lineNorm F ζ hζ U R P H f := by
    funext b
    obtain ⟨v, rfl⟩ := q_surjective F ζ hζ U b
    rw [borelDescent_q F ζ hζ U ψ hψ v, havg v, hpull v]
  have hcpl : ∀ (i : Fin (H.atlas U).componentCount)
      (x : KPCuspSiegel.OrbitQuotient F
        (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))),
      lineNorm F ζ hζ U R P H f
        (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i) x) =
        componentLineNorm F ζ hζ U R P H f i x := by
    intro i x
    refine Quotient.inductionOn x ?_
    intro y
    simp only [lineNorm, componentLineNorm, sectionNorm]
    rw [← (H.atlas U).components_formula i (Quotient.mk _ y)]
    rw [show (H.atlas U).components.symm ((H.atlas U).components ⟨i, Quotient.mk _ y⟩) =
        ⟨i, Quotient.mk _ y⟩ from Equiv.symm_apply_apply _ _]
  have hcompNorm : ∀ i : Fin (H.atlas U).componentCount,
      Measurable (componentNorm F ζ hζ U R P H (S F ζ hζ U R P H f) i) := by
    intro i
    rw [measurable_from_quotient]
    show Measurable (fun x : SymmetricSpace F => ‖(S F ζ hζ U R P H f i).val x‖)
    have h1 : Measurable (fun x : SymmetricSpace F => (S F ζ hζ U R P H f i).val x) := by
      have h2 : (fun x : SymmetricSpace F => (S F ζ hζ U R P H f i).val x) =
          fun x => f.val (Quotient.mk (coveredRelation F ζ hζ U)
            (x, (H.atlas U).representative i)) := by
        funext x; rw [S_apply]
      rw [h2]
      refine hf.comp ?_
      exact (continuous_quotient_mk'.comp
        (continuous_id.prodMk continuous_const)).measurable
    exact h1.norm
  have hdecomp (g : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞) (hg : Measurable g)
      (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hE : MeasurableSet E) :
      (∫⁻ b in E, g b ∂sphericalMeasure F ζ hζ R P U) =
      ∑ i : Fin (H.atlas U).componentCount, (H.disintegration U).componentWeight i *
        ∫⁻ x in (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i)) ⁻¹' E,
          g (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i) x)
          ∂KPFiniteCuspAtlas.quotientVolume F
            (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
            ((H.atlas U).cuspAtlas i).fundamentalDomain := by
    rw [← lintegral_indicator hE]
    letI : ∀ i : Fin (H.atlas U).componentCount,
        OpensMeasurableSpace (KPCuspSiegel.OrbitQuotient F
          (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))) :=
      fun i => ⟨MeasurableSpace.generateFrom_le (fun s hs =>
        measurableSet_quotient.mpr
          ((show IsOpen s from hs).preimage continuous_quotient_mk').measurableSet)⟩
    have hmaps : ∀ i, KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i) =
        fun x => (H.atlas U).components ⟨i,x⟩ := by
      intro i; funext x; exact ((H.atlas U).components_formula i x).symm
    have hm := fun i => (H.disintegration U).component_measure i
    simp only [hmaps] at hm ⊢
    rw [fixedLine_sigma_integral (H.atlas U).components _ _ _ hm _ (hg.indicator hE)]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    have hmi : Measurable (fun x => (H.atlas U).components ⟨i,x⟩) :=
      ((H.atlas U).components.continuous.comp continuous_sigmaMk).measurable
    rw [← lintegral_indicator (hE.preimage hmi)]
    apply lintegral_congr
    intro x
    by_cases hx : (H.atlas U).components ⟨i,x⟩ ∈ E <;> simp [hx]
  have hln : Measurable (lineNorm F ζ hζ U R P H f) := by
    rw [← hdesc]; exact borelDescent_measurable F ζ hζ U ψ hψ
  refine
    { fiber_norm := fun v w h => ?_
      pullback := hpull
      borel := ?_
      unique := fun n hn => ?_
      component := fun i x => ?_
      component_pullback := hcpl
      component_borel := fun i => ?_
      restricted_pushforward := fun E hE => ?_
      cutoff_pushforward := fun c hc E hE => ?_
      component_integral := fun E hE => ?_
      cutoff_component_integral := fun c hc E hE => ?_
      cusp_integral := fun Y hY => ?_
      cutoff_cusp_integral := fun Y hY c hc E hE => ?_
      chart_coefficient := fun Y hY j p r => ?_
      cutoff_section_integral := fun Y hY c hc => ?_
      lp_norm := fun hf2 => ?_ }
  · have hab : ENNReal.ofReal (‖f.val v‖ ^ 2) = ENNReal.ofReal (‖f.val w‖ ^ 2) := by
      rw [← hpull v, h, hpull w]
    exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)).mp hab
  · rw [← hdesc]; exact borelDescent_measurable F ζ hζ U ψ hψ
  · funext b
    obtain ⟨v, rfl⟩ := q_surjective F ζ hζ U b
    rw [hn v, hpull v]
  · simp only [lineNorm, sectionNorm_component F ζ hζ U R P H (S F ζ hζ U R P H f) i x]
  · exact ENNReal.measurable_ofReal.comp ((hcompNorm i).pow_const 2)
  · have hmeas : MeasurableSet ((q F ζ hζ U) ⁻¹' E) := hE.preimage hqm
    rw [← lintegral_indicator hmeas ψ, ← lintegral_indicator hE (lineNorm F ζ hζ U R P H f)]
    rw [← hdesc]
    exact lintegral_indicator_borelDescent F ζ hζ R P U ψ hψ E hE
  · have hmeas : MeasurableSet ((q F ζ hζ U) ⁻¹' E) := hE.preimage hqm
    have hFmeas : Measurable (fun b => E.indicator
        (fun b => c b * lineNorm F ζ hζ U R P H f b) b) :=
      (hc.mul (by rw [← hdesc]; exact borelDescent_measurable F ζ hζ U ψ hψ)).indicator hE
    have h1 : (∫⁻ b, E.indicator (fun b => c b * lineNorm F ζ hζ U R P H f b) b
          ∂sphericalMeasure F ζ hζ R P U) =
        ∫⁻ v, (q F ζ hζ U ⁻¹' E).indicator
            (fun v => c (q F ζ hζ U v) * ψ v) v ∂coveredMeasure F ζ hζ R U := by
      rw [← map_q_coveredMeasure F ζ hζ R P U, lintegral_map hFmeas hqm]
      apply lintegral_congr
      intro v
      by_cases hv : q F ζ hζ U v ∈ E
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (Set.mem_preimage.mpr hv)]
        exact congrArg (fun t => c (q F ζ hζ U v) * t) (hpull v)
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (by
          simpa only [Set.mem_preimage] using hv)]
    rw [← lintegral_indicator hmeas (fun v => c (q F ζ hζ U v) * ψ v),
      ← lintegral_indicator hE (fun b => c b * lineNorm F ζ hζ U R P H f b)]
    exact h1.symm
  · rw [hdecomp _ hln E hE]
    apply Finset.sum_congr rfl
    intro i hi
    simp_rw [hcpl i]
  · rw [hdecomp (fun b => c b * lineNorm F ζ hζ U R P H f b) (hc.mul hln) E hE]
    apply Finset.sum_congr rfl
    intro i hi
    simp_rw [hcpl i]
  · exact (H.disintegration U).cusp_integral Y hY (lineNorm F ζ hζ U R P H f) (by
      rw [← hdesc]; exact borelDescent_measurable F ζ hζ U ψ hψ)
  · have hφ : Measurable (E.indicator (fun b => c b * lineNorm F ζ hζ U R P H f b)) :=
      (hc.mul (by rw [← hdesc]; exact borelDescent_measurable F ζ hζ U ψ hψ)).indicator hE
    have hD := (H.disintegration U).cusp_integral Y hY
      (E.indicator (fun b => c b * lineNorm F ζ hζ U R P H f b)) hφ
    have hstep : (∫⁻ b in cuspEnds (H.atlas U) Y ∩ E,
          c b * lineNorm F ζ hζ U R P H f b ∂sphericalMeasure F ζ hζ R P U)
        = ∫⁻ b in cuspEnds (H.atlas U) Y,
            E.indicator (fun b => c b * lineNorm F ζ hζ U R P H f b) b
          ∂sphericalMeasure F ζ hζ R P U := by
      rw [show cuspEnds (H.atlas U) Y ∩ E = E ∩ cuspEnds (H.atlas U) Y from Set.inter_comm _ _,
        ← setLIntegral_indicator hE]
    exact hstep.trans hD
  · rw [(H.disintegration U).chart_formula Y hY j p r, hcpl j.1]
    simp only [componentLineNorm]
    have h1 : componentNorm F ζ hζ U R P H (S F ζ hζ U R P H f) j.1
        (KPCuspSiegel.projection F
          (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative j.1))
          (((H.atlas U).cuspAtlas j.1).representative j.2 •
            KPCuspCharts.toArch F
              ((p.1, p.2 + sectionShape F H.totallyComplex
                (H.disintegration U).radial.slot ⟨r.val, lt_trans hY.1 r.property⟩),
                logHeight (F := F) r.val))) =
        ‖cuspCoefficient F ζ hζ U R P H (S F ζ hζ U R P H f) j.1 j.2
          ((p.1, p.2 + sectionShape F H.totallyComplex
            (H.disintegration U).radial.slot ⟨r.val, lt_trans hY.1 r.property⟩),
            logHeight (F := F) r.val)‖ := by
      rw [show KPCuspSiegel.projection F
          (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative j.1)) _ =
          Quotient.mk _ _ from rfl]
      rw [componentNorm, Quotient.lift_mk]
      rw [show (S F ζ hζ U R P H f j.1).val _ =
          ((cuspCoefficient F ζ hζ U R P H (S F ζ hζ U R P H f) j.1 j.2
            ((p.1, p.2 + sectionShape F H.totallyComplex
              (H.disintegration U).radial.slot ⟨r.val, lt_trans hY.1 r.property⟩),
              logHeight (F := F) r.val)) : ℂ) from ?_]
      · rfl
      · rw [S_apply, ← J_apply]
        exact (cusp_restriction_commutes F ζ hζ U R P H f j.1 j.2 _ _).symm
    rw [h1]
  · let D := H.disintegration U
    have hφ : Measurable (fun b => c b * lineNorm F ζ hζ U R P H f b) := hc.mul hln
    rw [D.cusp_integral Y hY _ hφ]
    rw [← lintegral_const_mul' (D.beta Set.univ) _ D.finite_beta.measure_univ_lt_top.ne]
    apply lintegral_congr
    intro r
    rw [probability, lintegral_smul_measure]
    change D.beta Set.univ * ((D.beta Set.univ)⁻¹ * _) = _
    rw [← mul_assoc, ENNReal.mul_inv_cancel D.positive_beta D.finite_beta.measure_univ_lt_top.ne,
      one_mul]
    exact (D.section_disintegration
      (fun x => c (D.chart Y hY (x,r)) * lineNorm F ζ hζ U R P H f (D.chart Y hY (x,r)))
      (hφ.comp ((D.measurable_chart Y hY).comp
        (measurable_id.prodMk measurable_const)))).symm
  · rw [Lp.norm_toLp f.val hf2,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
        hf2.aestronglyMeasurable]
    have hlm : Measurable (lineNorm F ζ hζ U R P H f) := by
      rw [← hdesc]; exact borelDescent_measurable F ζ hζ U ψ hψ
    have hkey : (∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U) =
        ∫⁻ b, lineNorm F ζ hζ U R P H f b
          ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U := by
      rw [← map_q_coveredMeasure F ζ hζ R P U, lintegral_map hlm hqm]
      apply lintegral_congr
      intro v
      exact (hpull v).symm
    have hinner : (∫⁻ v, ‖f.val v‖ₑ ^ (ENNReal.toReal 2)
          ∂coveredMeasure F ζ hζ R U) =
        ∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U := by
      apply lintegral_congr
      intro v
      rw [show ‖f.val v‖ₑ = ENNReal.ofReal ‖f.val v‖ by simp, ENNReal.toReal_ofNat,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f.val v)) (by norm_num),
        show (‖f.val v‖ : ℝ) ^ (2 : ℝ) = ‖f.val v‖ ^ 2 from Real.rpow_two _]
    rw [hinner, hkey]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt ENNReal.toReal_nonneg]

end DedekindZetaZeroFree

end

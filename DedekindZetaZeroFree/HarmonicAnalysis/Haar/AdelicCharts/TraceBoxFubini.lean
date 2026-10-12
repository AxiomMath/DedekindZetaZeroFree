module

public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SelectedJacquetImage

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ENNReal
open MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox
open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPLocalStoneVonNeumann
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P₀ : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
variable (C₀ : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P₀)
variable (E : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
variable (φ : ∀ q : E, compactPicture (C₀.canonical q.val).borel (C₀.polarization q.val) (C₀.canonical q.val).iwasawa .plus)
variable (k : ∀ q : E, (C₀.canonical q.val).iwasawa.compact.toOpenSubgroup)
variable (t : ∀ q : E, actualTorus F ζ hζ q.val)

def finiteIntegrand (s : ℂ) (q : E) (x : LocalField F q.val) : ℂ :=
  ((compactTrivialization (C₀.canonical q.val).borel (C₀.polarization q.val) (C₀.canonical q.val).iwasawa .plus s (φ q)).val
    ((C₀.canonical q.val).borel.liftedW⁻¹ * ((C₀.canonical q.val).borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q.val) * k q)).val (t q)

private theorem unit_integer_mass (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q)
      ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1 := by
  have he : (valuation (LocalField F q)).integer = (q.adicCompletionIntegers F).toSubring := by
    let : (Valued.v : Valuation (LocalField F q) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    ext x
    change valuation (LocalField F q) x ≤ 1 ↔ Valued.v x ≤ 1
    exact (ValuativeRel.isEquiv (valuation (LocalField F q)) (Valued.v)).le_one_iff_le_one
  rw [he]
  exact Measure.addHaarMeasure_self (K₀ := finiteCompletionIntegersPositiveCompacts F q)

theorem finite_integrand_integrable (s : ℂ) (hs : -(1 : ℝ)/6 < s.re) (q : E) :
    Integrable (finiteIntegrand F ζ hζ P₀ C₀ E φ k t s q) (localNormalizedHaar F q.val) := by
  let μ := Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val)
  have hi : Integrable (finiteIntegrand F ζ hζ P₀ C₀ E φ k t s q) μ :=
    KPRankOneShellRepair.actualCanonicalContinued_integrable F q.val ζ hζ (C₀.canonical q.val) (C₀.polarization q.val) μ
      (unit_integer_mass F q.val) .plus s
      (by simpa [KPRankOneShellContinuation.convergenceHalfPlane, neg_div] using hs)
      (compactTrivialization (C₀.canonical q.val).borel (C₀.polarization q.val) (C₀.canonical q.val).iwasawa .plus s (φ q)) (k q) (t q)
  exact hi.smul_measure ENNReal.ofReal_ne_top

theorem finite_box_fubini (s : ℂ) (hs : -(1 : ℝ)/6 < s.re) :
    Integrable (fun a : ∀ q : E, LocalField F q.val =>
      ∏ q : E, finiteIntegrand F ζ hζ P₀ C₀ E φ k t s q (a q))
      (Measure.pi (fun q : E => localNormalizedHaar F q.val)) ∧
    (∫ a : ∀ q : E, LocalField F q.val,
      ∏ q : E, finiteIntegrand F ζ hζ P₀ C₀ E φ k t s q (a q)
        ∂Measure.pi (fun q : E => localNormalizedHaar F q.val)) =
      ∏ q : E, ∫ x : LocalField F q.val,
        finiteIntegrand F ζ hζ P₀ C₀ E φ k t s q x ∂localNormalizedHaar F q.val := by
  constructor
  · exact Integrable.fintype_prod_dep (finite_integrand_integrable F ζ hζ P₀ C₀ E φ k t s hs)
  · exact integral_fintype_prod_eq_prod _

def finiteCylinder (s : ℂ) (a : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) : ℂ :=
  ∏ q : E, finiteIntegrand F ζ hζ P₀ C₀ E φ k t s q (a q.val)

theorem finiteCylinder_chartMap (s : ℂ) (a : KPAdditiveHaar.Chart F E) :
    finiteCylinder F ζ hζ P₀ C₀ E φ k t s (KPAdditiveHaar.chartMap F E a) =
      ∏ q : E, finiteIntegrand F ζ hζ P₀ C₀ E φ k t s q (a.1 q) := by
  simp only [finiteCylinder]
  apply Finset.prod_congr rfl
  intro q _
  congr 1
  change (if h : q.val ∈ E then a.1 ⟨q.val, h⟩ else _) = a.1 q
  rw [dif_pos q.property]

theorem finite_adelic_chart_integrable
    (hE : localDifferentSupport F ⊆ (E : Set _)) (s : ℂ) (hs : -(1 : ℝ)/6 < s.re) :
    Integrable (finiteCylinder F ζ hζ P₀ C₀ E φ k t s)
      ((KPAdditiveHaar.finiteMeasure F).restrict (Set.range (KPAdditiveHaar.chartMap F E))) := by
  letI : ∀ v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ E},
      IsProbabilityMeasure (KPAdditiveHaar.integerProbabilityMeasure F v.val) :=
    fun v => KPAdditiveHaar.integerProbabilityMeasure_isProbabilityMeasure F v.val
  rw [KPAdditiveHaar.finiteMeasure_chart F E hE,
    (KPAdditiveHaar.chartMap_isOpenEmbedding F E).measurableEmbedding.integrable_map_iff]
  have he : finiteCylinder F ζ hζ P₀ C₀ E φ k t s ∘ KPAdditiveHaar.chartMap F E =
      (fun a : KPAdditiveHaar.Chart F E =>
        (∏ q : E, finiteIntegrand F ζ hζ P₀ C₀ E φ k t s q (a.1 q)) * (1 : ℂ)) := by
    funext a
    simp only [Function.comp_apply, finiteCylinder_chartMap, mul_one]
  rw [he]
  exact (finite_box_fubini F ζ hζ P₀ C₀ E φ k t s hs).1.mul_prod (integrable_const (1 : ℂ))

theorem finite_adelic_chart_integral
    (hE : localDifferentSupport F ⊆ (E : Set _)) (s : ℂ) :
    (∫ a : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F,
      finiteCylinder F ζ hζ P₀ C₀ E φ k t s a
        ∂(KPAdditiveHaar.finiteMeasure F).restrict (Set.range (KPAdditiveHaar.chartMap F E))) =
      ∏ q : E, ∫ x : LocalField F q.val,
        finiteIntegrand F ζ hζ P₀ C₀ E φ k t s q x ∂localNormalizedHaar F q.val := by
  letI : ∀ v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ E},
      IsProbabilityMeasure (KPAdditiveHaar.integerProbabilityMeasure F v.val) :=
    fun v => KPAdditiveHaar.integerProbabilityMeasure_isProbabilityMeasure F v.val
  rw [KPAdditiveHaar.finiteMeasure_chart F E hE,
    (KPAdditiveHaar.chartMap_isOpenEmbedding F E).measurableEmbedding.integral_map]
  have he : (fun a : KPAdditiveHaar.Chart F E =>
      finiteCylinder F ζ hζ P₀ C₀ E φ k t s (KPAdditiveHaar.chartMap F E a)) =
      (fun a => (∏ q : E, finiteIntegrand F ζ hζ P₀ C₀ E φ k t s q (a.1 q)) * (1 : ℂ)) := by
    funext a
    simp only [finiteCylinder_chartMap, mul_one]
  rw [he]
  change (∫ a, (∏ q : E, finiteIntegrand F ζ hζ P₀ C₀ E φ k t s q (a.1 q)) * (1 : ℂ)
    ∂(Measure.pi (fun q : E => localNormalizedHaar F q.val)).prod
      (Measure.infinitePi (fun v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ E} =>
        KPAdditiveHaar.integerProbabilityMeasure F v.val))) = _
  rw [integral_prod_mul
    (fun a : ∀ q : E, LocalField F q.val => ∏ q : E, finiteIntegrand F ζ hζ P₀ C₀ E φ k t s q (a q))
    (fun _ : ∀ v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ E},
      v.val.adicCompletionIntegers F => (1 : ℂ)),
    integral_const]
  simpa using integral_fintype_prod_eq_prod
    (fun q : E => finiteIntegrand F ζ hζ P₀ C₀ E φ k t s q)

def complexIntegrand (s : ℂ) (x : ℂ) : ℂ :=
  KPComplexIntertwinerParameterMajorant.forwardSection s
    KPComplexStandardIntertwinerGerm.compactSpherical
      (KPCplxCharacterHaar.weyl * KPCplxCharacterHaar.upperUnipotent x * 1)

theorem complex_integrand_integrable (s : ℂ)
    (hs : s ∈ KPComplexStandardIntertwinerGerm.halfPlane) :
    Integrable (complexIntegrand s) ((2 : ℝ≥0∞) • KPCplxCharacterHaar.euclideanArea) := by
  have hi := KPComplexStandardIntertwinerGerm.haarIntegral_integrable (1 : ℂˣ) s hs
    KPComplexStandardIntertwinerGerm.compactSpherical 1
  unfold KPCplxCharacterHaar.characterHaar at hi
  have hpos : 0 < KPCplxCharacterHaar.characterScale (1 : ℂˣ) / (2 * Real.pi) :=
    div_pos (KPCplxCharacterHaar.characterScale_pos 1) (by positivity)
  exact ((integrable_smul_measure (ENNReal.ofReal_pos.mpr hpos).ne'
    ENNReal.ofReal_ne_top).mp hi).smul_measure (by norm_num)

def archCylinder (s : ℂ) (a : NumberField.InfiniteAdeleRing F) : ℂ :=
  TateTensorProfile.archTensor F (fun _ => complexIntegrand s)
    (PoissonArch.infiniteAdeleToSpace F a)

include ζ hζ in

theorem arch_cylinder_integrable (s : ℂ)
    (hs : s ∈ KPComplexStandardIntertwinerGerm.halfPlane) :
    Integrable (archCylinder F s) (KPAdditiveHaar.archMeasure F) := by
  letI := primitive12_totallyComplex F ζ hζ
  have hi : Integrable (complexIntegrand s) (volume : Measure ℂ) :=
    (integrable_smul_measure (μ := (volume : Measure ℂ)) (f := complexIntegrand s)
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mp
      (complex_integrand_integrable s hs)
  have he : MeasurableEmbedding ((PoissonArch.infiniteAdeleToSpace F).symm :
      PoissonArch.Space F → NumberField.InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).symm.toHomeomorph.measurableEmbedding
  rw [KPAdditiveHaar.archMeasure, he.integrable_map_iff]
  have hf : archCylinder F s ∘ (PoissonArch.infiniteAdeleToSpace F).symm =
      TateTensorProfile.archTensor F (fun _ => complexIntegrand s) := by
    funext a
    simp only [Function.comp_apply, archCylinder, ContinuousLinearEquiv.apply_symm_apply]
  rw [hf]
  exact TateTensorProfile.archTensor_integrable_of_factors F (fun _ => complexIntegrand s) (fun _ => hi)

include ζ hζ in

theorem arch_cylinder_integral (s : ℂ) :
    (∫ a, archCylinder F s a ∂KPAdditiveHaar.archMeasure F) =
      ∏ w : {w : NumberField.InfinitePlace F // w.IsComplex},
        ∫ x : ℂ, complexIntegrand s x ∂((2 : ℝ≥0∞) • KPCplxCharacterHaar.euclideanArea) := by
  letI := primitive12_totallyComplex F ζ hζ
  have he : MeasurableEmbedding ((PoissonArch.infiniteAdeleToSpace F).symm :
      PoissonArch.Space F → NumberField.InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).symm.toHomeomorph.measurableEmbedding
  rw [KPAdditiveHaar.archMeasure, he.integral_map]
  simp only [archCylinder, ContinuousLinearEquiv.apply_symm_apply]
  rw [TateTensorProfile.archTensor_integral]
  simp only [integral_smul_measure, ENNReal.toReal_ofNat, RCLike.real_smul_eq_coe_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  congr 1
  simp [PoissonArch.haarScalar, NumberField.InfinitePlace.nrComplexPlaces]

def adelicCylinder (s : ℂ) (a : A F) : ℂ :=
  archCylinder F s a.1 * finiteCylinder F ζ hζ P₀ C₀ E φ k t s a.2

def adelicBox : Set (A F) :=
  {a | a.2 ∈ Set.range (KPAdditiveHaar.chartMap F E)}

 theorem finite_measure_sigmaFinite : SigmaFinite (KPAdditiveHaar.finiteMeasure F) := by
  letI := KPAdditiveHaar.finiteMeasure_isAddHaarMeasure F
  infer_instance

 theorem arch_measure_sigmaFinite : SigmaFinite (KPAdditiveHaar.archMeasure F) := by
  letI := KPAdditiveHaar.archMeasure_isAddHaarMeasure F
  letI : SecondCountableTopology (NumberField.InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.secondCountableTopology
  infer_instance

 theorem adelic_measure_box :
    (KPAdditiveHaar.adelicMeasure F).restrict (adelicBox F E) =
      @Measure.map (NumberField.InfiniteAdeleRing F ×
        IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) (A F) inferInstance inferInstance
        (fun a => a)
        ((KPAdditiveHaar.archMeasure F).prod
          ((KPAdditiveHaar.finiteMeasure F).restrict (Set.range (KPAdditiveHaar.chartMap F E)))) := by
  letI := finite_measure_sigmaFinite F
  letI := arch_measure_sigmaFinite F
  let e : (NumberField.InfiniteAdeleRing F ×
      IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ≃ₜ A F := Homeomorph.refl _
  have he : @MeasurableEmbedding (NumberField.InfiniteAdeleRing F ×
      IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) (A F) inferInstance inferInstance
      (fun a => a) := e.measurableEmbedding
  rw [KPAdditiveHaar.adelicMeasure, he.restrict_map]
  have hpre : (fun a : NumberField.InfiniteAdeleRing F ×
      IsDedekindDomain.FiniteAdeleRing (𝓞 F) F => (a : A F)) ⁻¹' adelicBox F E =
      Set.univ ×ˢ Set.range (KPAdditiveHaar.chartMap F E) := by
    ext a
    exact (and_iff_right (Set.mem_univ a.1)).symm
  rw [hpre, ← Measure.prod_restrict, Measure.restrict_univ]

theorem adelic_box_integrable
    (hE : localDifferentSupport F ⊆ (E : Set _)) (s : ℂ) (hs : (1 : ℝ)/3 < s.re) :
    Integrable (adelicCylinder F ζ hζ P₀ C₀ E φ k t s)
      ((KPAdditiveHaar.adelicMeasure F).restrict (adelicBox F E)) := by
  letI := finite_measure_sigmaFinite F
  letI := arch_measure_sigmaFinite F
  let e : (NumberField.InfiniteAdeleRing F ×
      IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ≃ₜ A F := Homeomorph.refl _
  have he : @MeasurableEmbedding (NumberField.InfiniteAdeleRing F ×
      IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) (A F) inferInstance inferInstance
      (fun a => a) := e.measurableEmbedding
  rw [adelic_measure_box F E, he.integrable_map_iff]
  exact (arch_cylinder_integrable F ζ hζ s (by
    change -(1 / 6 : ℝ) < s.re
    linarith)).mul_prod
    (finite_adelic_chart_integrable F ζ hζ P₀ C₀ E φ k t hE s (by linarith))

theorem adelic_box_integral
    (hE : localDifferentSupport F ⊆ (E : Set _)) (s : ℂ) :
    (∫ a : A F, adelicCylinder F ζ hζ P₀ C₀ E φ k t s a
      ∂(KPAdditiveHaar.adelicMeasure F).restrict (adelicBox F E)) =
      (∏ w : {w : NumberField.InfinitePlace F // w.IsComplex},
        ∫ x : ℂ, complexIntegrand s x ∂((2 : ℝ≥0∞) • KPCplxCharacterHaar.euclideanArea)) *
      (∏ q : E, ∫ x : LocalField F q.val,
        finiteIntegrand F ζ hζ P₀ C₀ E φ k t s q x ∂localNormalizedHaar F q.val) := by
  letI := finite_measure_sigmaFinite F
  letI := arch_measure_sigmaFinite F
  let e : (NumberField.InfiniteAdeleRing F ×
      IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ≃ₜ A F := Homeomorph.refl _
  have he : @MeasurableEmbedding (NumberField.InfiniteAdeleRing F ×
      IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) (A F) inferInstance inferInstance
      (fun a => a) := e.measurableEmbedding
  rw [adelic_measure_box F E, he.integral_map]
  change (∫ a : NumberField.InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F,
    archCylinder F s a.1 * finiteCylinder F ζ hζ P₀ C₀ E φ k t s a.2 ∂_) = _
  rw [integral_prod_mul (archCylinder F s) (finiteCylinder F ζ hζ P₀ C₀ E φ k t s),
    arch_cylinder_integral F ζ hζ, finite_adelic_chart_integral F ζ hζ P₀ C₀ E φ k t hE]

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox

end

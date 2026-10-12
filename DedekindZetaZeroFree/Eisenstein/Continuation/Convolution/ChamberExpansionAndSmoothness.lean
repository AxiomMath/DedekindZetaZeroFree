module

public import DedekindZetaZeroFree.Metaplectic.Torus.IwasawaDoubleAveraging
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Convolution.ArchimedeanRegularity
public import DedekindZetaZeroFree.Eisenstein.Induction.Convolution.EntireFiniteDimensionalExpansion

@[expose] public section

section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ConvolutionSpan.ActualSourceStage.SmoothStage
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance smoothTopGroup : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
local instance smoothBorel (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance smoothBorelSpace (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩
 def rawIwasawa (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) :
    KPGlobalTorusBorelNormTwistTransport.IwasawaData F ζ hζ where
  K := K
  compact := hK.1
  decomposition := hK.2.1
  overlap := KPLiteralChamber.compact_overlap F ζ hζ K hK.1

lemma weight_left_chart_smooth
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) (s : ℂ) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => Complex.exp (s * alpha F ζ hζ K hK
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  exact KPGlobalTorusBorelNormTwistTransport.IwasawaTransport.DoubleAverage.genuine_weight_smooth
    F ζ hζ (rawIwasawa F ζ hζ K hK) s g

lemma weight_right_chart_smooth
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) (s : ℂ) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => Complex.exp (s * alpha F ζ hζ K hK
        (g * KPGlobalResidualConstruction.archChart F ζ hζ x)))
      (KPGlobalResidualConstruction.archDomain F) := by
  apply contDiffOn_of_locally_contDiffOn
  intro x₀ hx₀
  obtain ⟨O, q, hO, hxO, hq, hqO, heq⟩ :=
    KPLiteralChamber.literal_right_to_left_chart_local_transition F ζ hζ g x₀ hx₀
  refine ⟨O, hO, hxO, ?_⟩
  have hc := (weight_left_chart_smooth F ζ hζ K hK s
      (g * KPGlobalResidualConstruction.archChart F ζ hζ x₀)).comp hq hqO
  exact (hc.congr (fun x hx => congrArg
    (fun t => Complex.exp (s * alpha F ζ hζ K hK t)) (heq x hx))).mono
    Set.inter_subset_right

lemma translated_smooth
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (a : G F ζ hζ) (s : ℂ) :
    Smooth F ζ hζ (rightAction F ζ hζ a (f.val s)) := by
  obtain ⟨U, hU⟩ := CommonLevel.flat_uniform_level F ζ hζ K hK f
  obtain ⟨V, hV⟩ := compact_uniform_conjugated_finite_level F ζ hζ
    {a} isCompact_singleton U
  refine ⟨(f.property.1 s).1.1.comp (continuous_id.mul continuous_const),
    ?_, ⟨V, ?_⟩⟩
  · intro g
    exact ArchRegularity.right_translate_arch_slice_smooth F ζ hζ (f.val s)
      (f.property.1 s).1 g a
  · intro g u hu
    have hc := hV a (Set.mem_singleton a) u hu
    have he : (g * u) * a = (g * a) * (a⁻¹ * u * a) := by group
    change f.val s ((g * u) * a) = f.val s (g * a)
    rw [he, hU s (g*a) _ hc]

lemma original_integral_arch_smooth
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsFiniteMeasure μ] (h : C(K, ℂ))
    (f : Flat F ζ hζ K) (a : G F ζ hζ) (s : ℂ) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => ∫ k : K, h k * f.val s
        ((g * KPGlobalResidualConstruction.archChart F ζ hζ x) * k.val * a) ∂μ)
      (KPGlobalResidualConstruction.archDomain F) := by
  have h := compact_convolution_arch_regular F ζ hζ K hK.1 μ h
    (rightAction F ζ hζ a (f.val s)) (translated_smooth F ζ hζ K hK f a s) g
  convert h using 1
  simp [compactConvolution, rightAction, mul_assoc]

lemma source_arch_smooth
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsFiniteMeasure μ] (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (s : ℂ) (h : C(K, ℂ)) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => source F ζ hζ K hK μ f a s h
        (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archDomain F) :=
  (weight_right_chart_smooth F ζ hζ K hK (-s) g).mul
    (original_integral_arch_smooth F ζ hζ K hK μ h f a s g)

lemma stage_arch_smooth
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsFiniteMeasure μ] (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (W : Submodule ℂ C(K, ℂ)) (v : Functions F ζ hζ)
    (hv : v ∈ ParameterStage.sourceStage F ζ hζ K hK μ f a W) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => v (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archDomain F) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨⟨s,h⟩,rfl⟩ := hv
      exact source_arch_smooth F ζ hζ K hK μ f a s h.val g
  | zero => exact contDiffOn_const
  | add v w _ _ hv hw => exact hv.add hw
  | smul c v _ hv => exact contDiffOn_const.mul hv

lemma flatten_smooth
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsFiniteMeasure μ] (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (W : Submodule ℂ C(K, ℂ)) (v : Functions F ζ hζ)
    (hv : v ∈ ParameterStage.sourceStage F ζ hζ K hK μ f a W) (s : ℂ) :
    Smooth F ζ hζ (ParameterStage.flatten F ζ hζ K hK v s) := by
  obtain ⟨J,hJ⟩ := ParameterStage.flatten_common_level F ζ hζ K hK μ f a W
  refine ⟨ParameterStage.flatten_continuous F ζ hζ K hK μ f a W v hv s,
    ?_, J, ?_⟩
  · intro g
    exact (weight_right_chart_smooth F ζ hζ K hK s g).mul
      (stage_arch_smooth F ζ hζ K hK μ f a W v hv g)
  · intro g j hj
    exact hJ s v hv g ⟨j,hj⟩

lemma representative_original_integral_flat_expansion
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (h : C(K, ℂ)) (hh : h ∈ TauCeti.representativeSubmodule ℂ K) :
    ∃ (n : ℕ) (b : Fin n → Flat F ζ hζ K) (c : Fin n → ℂ → ℂ),
      (∀ i, Differentiable ℂ (c i)) ∧
      ∀ s g, (∫ k : K, h k * f.val s (g * k.val * a) ∂μ) =
        ∑ i, c i s * (b i).val s g := by
  obtain ⟨W,J,hW,hhW,hS,hcontains,hi,hcont,hcov,hfixed⟩ :=
    ParameterStage.actual_finite_parameter_stage F ζ hζ K hK μ f a h hh
  let := hS
  obtain ⟨n,b,c,hc,he⟩ := ParameterStage.original_integral_finite_expansion
    F ζ hζ K hK μ f a W h hhW
  let B : Fin n → Flat F ζ hζ K := fun i =>
    ⟨ParameterStage.flatten F ζ hζ K hK (b i).val,
      (fun s => ⟨flatten_smooth F ζ hζ K hK μ f a W (b i).val (b i).property s,
        ParameterStage.flatten_covariance F ζ hζ K hK μ f a W (b i).val (b i).property s⟩),
      ParameterStage.flatten_full_fiber F ζ hζ K hK (b i).val,
      by
        rw [ParameterStage.flatten_zero]
        exact ⟨ParameterStage.sourceStage F ζ hζ K hK μ f a W, hS, (b i).property, hi⟩⟩
  exact ⟨n,B,c,hc,he⟩

end DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ConvolutionSpan.ActualSourceStage.SmoothStage

end

end

section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ConvolutionSpan.ChamberExchange
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance exchangeTopGroup : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
local instance exchangeBorel (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance exchangeBorelSpace (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩
local instance fieldCountable : Countable F :=
  (Module.finBasis ℚ F).repr.injective.countable
local instance rationalQuotientCountable : Countable (KPChamberBruhatTwoCells.RationalQuotient F) :=
  ((Equiv.ofBijective _ (KPChamberBruhatTwoCells.cellIndex_bijective F)).symm.injective).countable

lemma chamber_integral_norm_summable
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsProbabilityMeasure μ] (h : C(K, ℂ))
    (f : Flat F ζ hζ K) (a g : G F ζ hζ) (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) :
    Summable (fun c : KPChamberBruhatTwoCells.RationalQuotient F =>
      ∫ k : K, ‖h k * f.val s ((rationalLift F ζ hζ (Quotient.out c) * g) * k.val * a)‖ ∂μ) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.1
  let C : Set (G F ζ hζ) := (fun k : K => g * k.val * a) '' Set.univ
  have hC : IsCompact C := isCompact_univ.image
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  obtain ⟨b,hb,hbound⟩ := KPLiteralChamber.chamber_scalar_compact_majorants
    F ζ hζ K hK f {s} isCompact_singleton (by simpa using hs) C hC
  apply Summable.of_nonneg_of_le (fun c => integral_nonneg (fun k => norm_nonneg _)) _ (hb.mul_left ‖h‖)
  intro c
  have hbd (k : K) : ‖h k * f.val s ((rationalLift F ζ hζ (Quotient.out c) * g) * k.val * a)‖ ≤ ‖h‖ * b c := by
    rw [norm_mul]
    have hg : g * k.val * a ∈ C := ⟨k, Set.mem_univ _, rfl⟩
    have hf := hbound c s (Set.mem_singleton s) (g * k.val * a) hg
    simp only [mul_assoc] at hf ⊢
    exact mul_le_mul (h.norm_coe_le_norm k) hf (norm_nonneg _) (norm_nonneg _)
  have hi := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun k : K => ‖h k * f.val s ((rationalLift F ζ hζ (Quotient.out c) * g) * k.val * a)‖)
    (Filter.Eventually.of_forall (fun k => by simpa only [Real.norm_eq_abs, abs_norm] using hbd k))
  have hpos : 0 ≤ ∫ k : K, ‖h k * f.val s ((rationalLift F ζ hζ (Quotient.out c) * g) * k.val * a)‖ ∂μ :=
    integral_nonneg (fun k => norm_nonneg _)
  simpa only [probReal_univ, mul_one, Real.norm_eq_abs, abs_of_nonneg hpos] using hi

lemma chamber_summand_integrable
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsFiniteMeasure μ] (h : C(K, ℂ))
    (f : Flat F ζ hζ K) (a g : G F ζ hζ) (s : ℂ)
    (c : KPChamberBruhatTwoCells.RationalQuotient F) :
    Integrable (fun k : K => h k *
      f.val s ((rationalLift F ζ hζ (Quotient.out c) * g) * k.val * a)) μ :=
  ActualSourceStage.source_integrable F ζ hζ K hK μ f a s h
    (rationalLift F ζ hζ (Quotient.out c) * g)

lemma raw_chamber_compact_integral
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsProbabilityMeasure μ] (h : C(K, ℂ))
    (f : Flat F ζ hζ K) (a g : G F ζ hζ) (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) :
    (∫ k : K, h k * eisenstein F ζ hζ K f s (g * k.val * a) ∂μ) =
      ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
        ∫ k : K, h k *
          f.val s ((rationalLift F ζ hζ (Quotient.out c) * g) * k.val * a) ∂μ := by
  have he := integral_tsum_of_summable_integral_norm
    (chamber_summand_integrable F ζ hζ K hK μ h f a g s)
    (chamber_integral_norm_summable F ζ hζ K hK μ h f a g s hs)
  rw [he]
  apply integral_congr_ae
  filter_upwards with k
  simp only [eisenstein, mul_assoc, tsum_mul_left]

lemma representative_raw_chamber_expansion
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (h : C(K, ℂ)) (hh : h ∈ TauCeti.representativeSubmodule ℂ K) :
    ∃ (n : ℕ) (b : Fin n → Flat F ζ hζ K) (c : Fin n → ℂ → ℂ),
      (∀ i, Differentiable ℂ (c i)) ∧
      ∀ s, (1 : ℝ) / 3 < s.re → ∀ g,
        (∫ k : K, h k * eisenstein F ζ hζ K f s (g * k.val * a) ∂μ) =
          ∑ i, c i s * eisenstein F ζ hζ K (b i) s g := by
  obtain ⟨n,b,c,hc,he⟩ := ActualSourceStage.SmoothStage.representative_original_integral_flat_expansion
    F ζ hζ K hK μ f a h hh
  refine ⟨n,b,c,hc,?_⟩
  intro s hs g
  rw [raw_chamber_compact_integral F ζ hζ K hK μ h f a g s hs]
  simp_rw [he s]
  have hsum (i : Fin n) : Summable
      (fun q : KPChamberBruhatTwoCells.RationalQuotient F =>
        c i s * (b i).val s (rationalLift F ζ hζ (Quotient.out q) * g)) := by
    obtain ⟨B,hB,hbound⟩ := KPLiteralChamber.chamber_scalar_compact_majorants
      F ζ hζ K hK (b i) {s} isCompact_singleton (by simpa using hs) {g} isCompact_singleton
    exact (Summable.of_norm (Summable.of_nonneg_of_le (fun q => norm_nonneg _)
      (fun q => hbound q s (Set.mem_singleton s) g (Set.mem_singleton g)) hB)).mul_left _
  rw [Summable.tsum_finsetSum (fun i _ => hsum i)]
  simp only [eisenstein, tsum_mul_left]

end DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ConvolutionSpan.ChamberExchange

end

end

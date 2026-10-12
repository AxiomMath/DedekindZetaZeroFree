module

public import DedekindZetaZeroFree.Eisenstein.Residues.FlatSectionNondegeneracy
public import DedekindZetaZeroFree.Eisenstein.Residues.CompactProjectionPreimages
public import DedekindZetaZeroFree.Analysis.TopologicalVectorSpaces.FiniteDimensionalIntersections
public import DedekindZetaZeroFree.Eisenstein.Residues.HarishChandraCore.StagewiseDensity

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.ExactStageGeneration renaming compactConvolution_mem_typeStage → compactConvolution_mem_typeStage
open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming smooth_add → smooth_add
open _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum renaming smooth_smul → smooth_smul
open KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

 def flatResidueRange (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) :
    Submodule ℂ (Functions F ζ hζ) where
  carrier := {u | ∃ (f : Flat F ζ hζ K) (C : FlatScalarResidue F ζ hζ f), C.numerator 0 = u}
  zero_mem' := by
    let f := FiniteWhittakerProjectors.FlatFiniteSum.zero F ζ hζ K
    let C := Classical.choice (flatScalarResidue_nonempty F ζ hζ K hK f)
    refine ⟨f,C,?_⟩
    exact C.zero_of_zero_section hK rfl
  add_mem' := by
    rintro u v ⟨f,C,rfl⟩ ⟨h,D,rfl⟩
    let b : Bool → Flat F ζ hζ K := fun j => if j then h else f
    let c : ∀ j, FlatScalarResidue F ζ hζ (b j) := fun j => by cases j; exact C; exact D
    let z := FiniteWhittakerProjectors.FlatFiniteSum.sum F ζ hζ Finset.univ (fun _ => 1) b
    let E := Classical.choice (flatScalarResidue_nonempty F ζ hζ K hK z)
    refine ⟨z,E,?_⟩
    ext g
    rw [flat_sum_residue hK Finset.univ (fun _ => 1) b E c]
    simp only [Fintype.sum_bool,one_mul,Pi.add_apply]
    change D.numerator 0 g + C.numerator 0 g = _
    exact add_comm _ _
  smul_mem' := by
    rintro a u ⟨f,C,rfl⟩
    let b : Unit → Flat F ζ hζ K := fun _ => f
    let z := FiniteWhittakerProjectors.FlatFiniteSum.sum F ζ hζ Finset.univ (fun _ => a) b
    let E := Classical.choice (flatScalarResidue_nonempty F ζ hζ K hK z)
    refine ⟨z,E,?_⟩
    ext g
    rw [flat_sum_residue hK Finset.univ (fun _ => a) b E (fun _ => C)]
    simp

 def translatedFlatResidueSpan (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) :
    Submodule ℂ (Functions F ζ hζ) := Submodule.span ℂ
      {u | ∃ (f : Flat F ζ hζ K) (C : FlatScalarResidue F ζ hζ f) (a : G F ζ hζ),
        u = rightAction F ζ hζ a (C.numerator 0)}

 theorem projected_span_in_range {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (h : C(K,ℂ)) (hh : h ∈ TauCeti.representativeSubmodule ℂ K)
    (u : Functions F ζ hζ) (hu : u ∈ translatedFlatResidueSpan F ζ hζ K hK)
    (hreg : ∀ (f : Flat F ζ hζ K) (C : FlatScalarResidue F ζ hζ f), Continuous (C.numerator 0)) :
    compactConvolution F ζ hζ K μ h u ∈ flatResidueRange F ζ hζ K hK := by
  letI : IsTopologicalGroup (G F ζ hζ) := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK.1
  have hc : ∀ u ∈ translatedFlatResidueSpan F ζ hζ K hK, Continuous u := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨f,C,a,rfl⟩ := hu; exact (hreg f C).comp (continuous_mul_const a)
    | zero => exact continuous_const
    | add _ _ _ _ ih ih' => exact ih.add ih'
    | smul c _ _ ih => exact continuous_const.smul ih
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨f,C,a,rfl⟩ := hu
    obtain ⟨v,D,he⟩ := projected_flat_residue F ζ hζ hK f C a μ h hh
    exact ⟨v,D,funext he⟩
  | zero =>
    have hz : compactConvolution F ζ hζ K μ h (0 : Functions F ζ hζ) = 0 := by ext g; simp [compactConvolution]
    rw [hz]; exact Submodule.zero_mem _
  | add u v hu hv ih ih' =>
    have he : compactConvolution F ζ hζ K μ h (u+v) =
        compactConvolution F ζ hζ K μ h u + compactConvolution F ζ hζ K μ h v := by
      ext g
      simp only [compactConvolution,Pi.add_apply,mul_add]
      exact integral_add
        ((h.continuous.mul ((hc u hu).comp (continuous_const.mul continuous_subtype_val))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        ((h.continuous.mul ((hc v hv).comp (continuous_const.mul continuous_subtype_val))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    rw [he]; exact Submodule.add_mem _ ih ih'
  | smul c u hu ih =>
    have he : compactConvolution F ζ hζ K μ h (c • u) = c • compactConvolution F ζ hζ K μ h u := by
      ext g
      simp only [compactConvolution,Pi.smul_apply,smul_eq_mul]
      simp_rw [mul_left_comm (h _) c]
      exact integral_const_mul c _
    rw [he]; exact Submodule.smul_mem _ c ih

 theorem kfinite_mem_flat_range {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) (u : Functions F ζ hζ)
    (hu : u ∈ translatedFlatResidueSpan F ζ hζ K hK) (huc : Continuous u)
    (hk : KFinite F ζ hζ K u)
    (hreg : ∀ (f : Flat F ζ hζ K) (C : FlatScalarResidue F ζ hζ f), Continuous (C.numerator 0)) :
    u ∈ flatResidueRange F ζ hζ K hK := by
  obtain ⟨T,hT,huT,ht⟩ := hk
  letI := hT
  let τ : KPGlobalEisensteinData.CompactTypeStage ((rightAction F ζ hζ).comp K.subtype) :=
    ⟨T,inferInstance,ht⟩
  let W := T ⊓ flatResidueRange F ζ hζ K hK
  have hW : IsClosed (W : Set (Functions F ζ hζ)) :=
    KPLiteralTensor.KernelAndHCRange.CoreGeneration.finite_stage_intersection_closed T T _ le_rfl
  have hcl : u ∈ closure (W : Set (Functions F ζ hζ)) := by
    apply mem_closure_iff.mpr
    intro O hO huO
    obtain ⟨I,v,hv,hsub⟩ := isOpen_pi_iff.mp hO u huO
    have hballs : ∀ j : I, ∃ ε : ℝ, 0 < ε ∧ Metric.ball (u j.val) ε ⊆ v j.val := by
      intro j
      exact Metric.isOpen_iff.mp (hv j.val j.property).1 (u j.val) (hv j.val j.property).2
    choose ε hε hball using hballs
    have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ ∧ ∀ j : I, δ < ε j := by
      apply Filter.Eventually.and self_mem_nhdsWithin
      apply Filter.eventually_all.mpr
      intro j
      exact nhdsWithin_le_nhds (Iio_mem_nhds (hε j))
    obtain ⟨δ,hδ,hδsmall⟩ := hsmall.exists
    obtain ⟨μ,hμ,hμp,h,hh,happrox⟩ := representative_convolution_uniform_approximation
      F ζ hζ K hK.1 u huc (I : Set _) I.finite_toSet.isCompact δ hδ
    letI := hμ
    letI := hμp
    let z := compactConvolution F ζ hζ K μ h u
    refine ⟨z,hsub ?_,?_⟩
    · intro j hj
      apply hball ⟨j,hj⟩
      rw [Metric.mem_ball,dist_eq_norm]
      exact (happrox j hj).trans (hδsmall ⟨j,hj⟩)
    · exact ⟨compactConvolution_mem_typeStage F ζ hζ K hK.1 μ τ u huc huT h,
        projected_span_in_range F ζ hζ hK μ h hh u hu hreg⟩
  exact (hW.closure_eq ▸ hcl).2

end DedekindZetaZeroFree.RootDerivatives

end

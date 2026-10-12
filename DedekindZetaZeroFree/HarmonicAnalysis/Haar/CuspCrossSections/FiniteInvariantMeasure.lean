module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspCrossSections.ShapeNormalization
public import DedekindZetaZeroFree.Geometry.Cusps.FundamentalDomains.AffineLatticeAction

@[expose] public section

section

noncomputable section
open scoped Classical Matrix
open MeasureTheory

namespace DedekindZetaZeroFree.KPCuspChart.SectionConstruction

 def horizontalLinear {d : ℕ} (a : Fin d → ℂ) : (Fin d → ℂ) →ₗ[ℝ] (Fin d → ℂ) :=
  LinearMap.pi (fun i => ((LinearMap.mulLeft ℂ (a i)).restrictScalars ℝ).comp (LinearMap.proj i))
 lemma horizontal_det {d : ℕ} (a : Fin d → ℂ) :
    (horizontalLinear a).det = ∏ i, ‖a i‖ ^ 2 := by
  rw [horizontalLinear, LinearMap.det_pi]
  simp only [LinearMap.det_restrictScalars, LinearMap.det_mulLeft,
    Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
private lemma norm_product
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F) (u : E) :
    ∏ i, ‖embedding F ((u : Fˣ) : F) i‖ ^ 2 = 1 := by
  have hs := KPCuspLogShape.sum_logRatio_eq_zero F hF E hE u
  have hn (i : Fin (KPCuspLogShape.dimension F)) :
      0 < ‖embedding F ((u : Fˣ) : F) i‖ := by
    apply norm_pos_iff.mpr
    exact (map_ne_zero (KPCusp.complexPlace F i).embedding).mpr (Units.ne_zero _)
  have he (i : Fin (KPCuspLogShape.dimension F)) :
      Real.exp (KPCuspLogShape.logRatio F E (Additive.ofMul u) i) =
        ‖embedding F ((u : Fˣ) : F) i‖ := by
    simpa [KPCuspLogShape.logRatio, embedding, NumberField.InfinitePlace.norm_embedding_eq]
      using Real.exp_log (hn i)
  rw [Finset.prod_pow]
  have hp : ∏ i, ‖embedding F ((u : Fˣ) : F) i‖ = 1 := by
    calc
      _ = ∏ i, Real.exp (KPCuspLogShape.logRatio F E (Additive.ofMul u) i) :=
        Finset.prod_congr rfl (fun i _ => (he i).symm)
      _ = 1 := by rw [← Real.exp_sum, hs, Real.exp_zero]
  rw [hp, one_pow]
private lemma horizontal_invariant
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F) (u : E) (v : F) :
    Measure.map (fun x : Horizontal F => fun i => embedding F ((u : Fˣ) : F) i * x i + embedding F v i)
      volume = volume := by
  let a := embedding F ((u : Fˣ) : F)
  have hd : (horizontalLinear a).det = 1 := by
    rw [horizontal_det]
    exact norm_product F hF E hE u
  have hm : Measure.map (horizontalLinear a) volume = volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hd]; exact one_ne_zero), hd]
    simp
  have ht : (fun x : Horizontal F => fun i => embedding F ((u : Fˣ) : F) i * x i + embedding F v i) =
      (fun x : Horizontal F => x + embedding F v) ∘ horizontalLinear a := rfl
  rw [ht, ← Measure.map_map (by fun_prop) (horizontalLinear a).continuous_of_finiteDimensional.measurable,
    hm, map_add_right_eq_self]

theorem full_affine_measure_invariant
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D)
    (μ : Measure (Shape F)) [μ.IsAddHaarMeasure] (g : S) :
    Measure.map (G.crossAction g) (volume.prod μ) = volume.prod μ := by
  obtain ⟨A, hA, hu⟩ := D.upper g g.property
  let v := A 0 1 / A 1 1
  have he : (G.crossAction g : Cross F → Cross F) = Prod.map
      (fun x : Horizontal F => fun i => embedding F ((D.ratio g : Fˣ) : F) i * x i + embedding F v i)
      (fun b : Shape F => b + KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul (D.ratio g))) := by
    funext p
    exact G.crossAction_formula g A hA hu p
  rw [he, ← Measure.map_prod_map volume μ (by fun_prop) (by fun_prop),
    horizontal_invariant F hF D.E D.integralUnits (D.ratio g) v, map_add_right_eq_self]

end DedekindZetaZeroFree.KPCuspChart.SectionConstruction

end

end

section

noncomputable section
open scoped Classical Matrix Pointwise
open MeasureTheory

namespace DedekindZetaZeroFree.KPCuspChart.SectionConstruction

private theorem compact_lifts {H X : Type*} [Group H] [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] [MulAction H X] [ContinuousConstSMul H X]
    [CompactSpace (Quotient (MulAction.orbitRel H X))] :
    ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ g : H, g • x ∈ K := by
  classical
  have hq : IsOpenMap (Quotient.mk (MulAction.orbitRel H X)) :=
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  choose V hVopen hxV hVcomp using fun x : X => exists_isOpen_mem_isCompact_closure x
  have hcover : (Set.univ : Set (Quotient (MulAction.orbitRel H X))) ⊆
      ⋃ x, Quotient.mk (MulAction.orbitRel H X) '' V x := by
    intro y _
    obtain ⟨x, rfl⟩ := MulAction.isOpenQuotientMap_quotientMk.surjective y
    exact Set.mem_iUnion.2 ⟨x, x, hxV x, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _
    (fun x => hq _ (hVopen x)) hcover
  refine ⟨⋃ x ∈ t, closure (V x), t.isCompact_biUnion fun x _ => hVcomp x, ?_⟩
  intro x
  have hx : Quotient.mk (MulAction.orbitRel H X) x ∈
      ⋃ y ∈ t, Quotient.mk (MulAction.orbitRel H X) '' V y := ht (Set.mem_univ _)
  obtain ⟨y, hy⟩ := Set.mem_iUnion.1 hx
  obtain ⟨hyt, v, hvV, hvq⟩ := Set.mem_iUnion.1 hy
  have hrel : MulAction.orbitRel H X v x := Quotient.exact hvq
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  exact ⟨g, hg ▸ Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hyt, subset_closure hvV⟩⟩⟩

private theorem domain_le_cover {H X : Type*} [Group H] [MeasurableSpace X]
    [MulAction H X] [Countable H] [MeasurableConstSMul H X]
    (ν : Measure X) [SMulInvariantMeasure H X ν]
    (Ω K : Set X) (hΩ : IsFundamentalDomain H Ω ν)
    (hcover : ∀ x : X, ∃ g : H, g • x ∈ K) : ν Ω ≤ ν K := by
  have heq : (⋃ g : H, g • K ∩ Ω) = Ω := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun _ => Set.inter_subset_right
    · intro x hx
      obtain ⟨g, hg⟩ := hcover x
      exact Set.mem_iUnion.mpr ⟨g⁻¹, ⟨g • x, hg, inv_smul_smul g x⟩, hx⟩
  rw [← heq, hΩ.measure_eq_tsum K]
  exact measure_iUnion_le _

private theorem mass_upper_action (g : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hc : g 1 0 = 0) (u : ℂ) (hu : u ≠ 0) (ha : g 0 0 = u * g 1 1)
    (z : KPArch.H3) :
    KPArch.action g z = (u * z.1 + g 0 1 / g 1 1, z.2 + Real.log ‖u‖) := by
  have hd : g 1 1 ≠ 0 := by
    intro h
    apply g.det_ne_zero
    simp [Matrix.det_fin_two, hc, h]
  have hdR : ‖g 1 1‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  have huR : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  apply Prod.ext
  · simp only [KPArch.action, KPArch.actionDenominator, hc, zero_mul, zero_add,
      norm_zero, zero_pow (by norm_num : 2 ≠ 0), star_zero, mul_zero, add_zero]
    have hn : (‖g 1 1‖ ^ 2 : ℝ) = (g 1 1 * star (g 1 1) : ℂ) := by
      simpa [Complex.normSq_eq_norm_sq] using (Complex.mul_conj (g 1 1)).symm
    rw [hn, ha]
    have hds : star (g 1 1) ≠ 0 := star_ne_zero.mpr hd
    field_simp
  · exact KPCuspLogShape.upper_action_snd g hc u hu ha z

private theorem mass_actual_affine_action (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F))
    (hc : A 1 0 = 0) (p : Coordinates F) :
    KPCuspSiegel.action F (g : KPCuspArithmetic.PGL2 F) (toArch F p) =
      toArch F (affine F hF D.E D.integralUnits (D.ratio g) (A 0 1 / A 1 1) p) := by
  rw [← hA, KPCuspSiegel.action_mk]
  funext i
  let σ := (KPCusp.complexPlace F i).embedding
  have hi : (Matrix.GeneralLinearGroup.map σ A) 1 0 = 0 := by
    change σ (A 1 0) = 0
    simp [hc]
  have hu : σ ((D.ratio g : Fˣ) : F) ≠ 0 :=
    (map_ne_zero σ).mpr (Units.ne_zero _)
  have ha : (Matrix.GeneralLinearGroup.map σ A) 0 0 =
      σ ((D.ratio g : Fˣ) : F) * (Matrix.GeneralLinearGroup.map σ A) 1 1 := by
    change σ (A 0 0) = _
    rw [D.ratioFormula g A hA hc, map_mul]
    rfl
  change KPArch.action (Matrix.GeneralLinearGroup.map σ A) (toArch F p i) = _
  rw [mass_upper_action _ hi _ hu ha]
  apply Prod.ext
  · change σ ((D.ratio g : Fˣ) : F) * p.1.1 i + σ (A 0 1) / σ (A 1 1) =
      σ ((D.ratio g : Fˣ) : F) * p.1.1 i + σ (A 0 1 / A 1 1)
    rw [map_div₀]
  · change p.2 + (p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i + Real.log ‖σ _‖ =
      p.2 + ((p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i +
        Real.log ((KPCusp.complexPlace F i) ((D.ratio g : Fˣ) : F)))
    rw [NumberField.InfinitePlace.norm_embedding_eq]
    ring

private theorem mass_cross_orbit_relation
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) :
    letI := homeomorphAction G.crossAction
    crossRelation F S = MulAction.orbitRel S (Cross F) := by
  letI := homeomorphAction G.crossAction
  have hact (g : S) (p : Cross F) :
      (g : KPCuspArithmetic.PGL2 F) • toArch F (p, 0) =
        toArch F (G.crossAction g p, 0) := by
    obtain ⟨A, hA, hc⟩ := D.upper g g.property
    change KPCuspSiegel.action F (g : KPCuspArithmetic.PGL2 F) _ = _
    rw [mass_actual_affine_action F hF S D g A hA hc,
      G.crossAction_formula g A hA hc]
    rfl
  have hinj : Function.Injective (fun p : Cross F => toArch F (p, 0)) := by
    intro p q h
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst (congrFun h i)
    · apply Subtype.ext
      funext i
      have he := congrArg Prod.snd (congrFun h i)
      simpa only [toArch, zero_add] using he
  apply Setoid.ext
  intro p q
  change (∃ g : S, g • toArch F (q, 0) = toArch F (p, 0)) ↔
    (∃ g : S, G.crossAction g q = p)
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, hinj ((hact g q).symm.trans hg)⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, (hact g q).trans (congrArg (fun p => toArch F (p, 0)) hg)⟩

theorem actual_fundamental_domain_mass
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (hdisc : DiscreteTopology (translationLattice F D.L).toIntSubmodule)
    (hlattice : letI := hdisc; IsZLattice ℝ (translationLattice F D.L).toIntSubmodule)
    (G : GeometryData F hF S D)
    (μ : Measure (Shape F)) [μ.IsAddHaarMeasure]
    (hinv : ∀ g : S, Measure.map (G.crossAction g) (volume.prod μ) = volume.prod μ)
    (Ω : Set (Cross F)) (hΩmeas : MeasurableSet Ω)
    (hΩ : letI := homeomorphAction G.crossAction;
      IsFundamentalDomain S Ω (volume.prod μ)) :
    (volume.prod μ) Ω < ⊤ ∧ (volume.prod μ) Ω ≠ 0 := by
  letI := homeomorphAction G.crossAction
  letI : ContinuousConstSMul S (Cross F) := ⟨fun g => (G.crossAction g).continuous⟩
  letI : MeasurableConstSMul S (Cross F) := ⟨fun g => (G.crossAction g).continuous.measurable⟩
  letI : SMulInvariantMeasure S (Cross F) (volume.prod μ) := by
    constructor
    intro g s hs
    change (volume.prod μ) ((G.crossAction g) ⁻¹' s) = (volume.prod μ) s
    rw [← Measure.map_apply (G.crossAction g).continuous.measurable hs, hinv]
  letI : Countable F := (Module.finBasis ℚ F).repr.injective.countable
  letI : Encodable F := Encodable.ofCountable F
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  letI : Countable (KPCuspArithmetic.PGL2 F) := Matrix.ProjGenLinGroup.mk_surjective.countable
  letI : Countable S := inferInstance
  letI : CompactSpace (Quotient (MulAction.orbitRel S (Cross F))) := by
    rw [← mass_cross_orbit_relation F hF S D G]
    exact G.compact_cross
  obtain ⟨K, hK, hcover⟩ := compact_lifts (H := S) (X := Cross F)
  refine ⟨(domain_le_cover (volume.prod μ) Ω K hΩ hcover).trans_lt hK.measure_lt_top, ?_⟩
  apply hΩ.measure_ne_zero
  apply Measure.measure_univ_ne_zero.mp
  rw [← Set.univ_prod_univ, Measure.prod_prod]
  exact mul_ne_zero (Measure.measure_univ_ne_zero.mpr
    (NeZero.ne (volume : Measure (Horizontal F))))
    (Measure.measure_univ_ne_zero.mpr (NeZero.ne μ))

end DedekindZetaZeroFree.KPCuspChart.SectionConstruction

end

end

section
noncomputable section
open scoped Classical Matrix
open MeasureTheory
namespace DedekindZetaZeroFree.KPCuspChart

theorem sectionMeasure_univ
    (F : Type*) [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (μ : Measure (Shape F)) (Ω : Set (Cross F)) :
    Measure.map (Quotient.mk (crossRelation F S))
      ((volume.prod μ).restrict Ω) Set.univ = (volume.prod μ) Ω := by
  rw [Measure.map_apply measurable_quotient_mk'' MeasurableSet.univ]
  simp

theorem finite_sectionMeasure_iff
    (F : Type*) [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (μ : Measure (Shape F)) (Ω : Set (Cross F)) :
    IsFiniteMeasure (Measure.map (Quotient.mk (crossRelation F S))
      ((volume.prod μ).restrict Ω)) ↔ (volume.prod μ) Ω < ⊤ := by
  rw [isFiniteMeasure_iff, sectionMeasure_univ]

theorem normalized_finite_section
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (hdisc : DiscreteTopology (translationLattice F D.L).toIntSubmodule)
    (hlattice : letI := hdisc; IsZLattice ℝ (translationLattice F D.L).toIntSubmodule)
    (G : GeometryData F hF S D) :
    Nonempty (SectionData F hF S D G) := by
  obtain ⟨μ, hμ, harch⟩ := SectionConstruction.normalized_shape_haar F hF
  letI := hμ
  have hinv : ∀ g : S, Measure.map (G.crossAction g) (volume.prod μ) = volume.prod μ :=
    SectionConstruction.full_affine_measure_invariant F hF S D G μ
  obtain ⟨Ω, hΩmeas, hΩ⟩ :=
    SectionConstruction.actual_measurable_fundamental_domain F hF S D hdisc hlattice G μ
  obtain ⟨hfinite, hpositive⟩ :=
    SectionConstruction.actual_fundamental_domain_mass F hF S D hdisc hlattice G μ
      hinv Ω hΩmeas hΩ
  refine ⟨{
    shapeMeasure := μ
    haar_shapeMeasure := hμ
    archVolume_formula := harch
    measure_invariant := hinv
    fundamentalDomain := Ω
    measurable_fundamentalDomain := hΩmeas
    isFundamentalDomain := hΩ
    sectionMeasure := Measure.map (Quotient.mk (crossRelation F S))
      ((volume.prod μ).restrict Ω)
    sectionMeasure_formula := rfl
    finite_sectionMeasure := (finite_sectionMeasure_iff F S μ Ω).mpr hfinite
    positive_sectionMeasure := ?_
  }⟩
  rw [sectionMeasure_univ]
  exact hpositive

end DedekindZetaZeroFree.KPCuspChart

end

end

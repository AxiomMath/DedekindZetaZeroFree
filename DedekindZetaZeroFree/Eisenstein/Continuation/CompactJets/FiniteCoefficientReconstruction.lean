module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.ChartCoefficientAveraging

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

section Cut
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (S : Set X) (hS : MeasurableSet S)
 def cutLinear : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := ((Lp.memLp f).indicator hS.nullMeasurableSet).toLp (S.indicator f)
  map_add' f g := by
    have he : S.indicator ((f+g : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ]
        S.indicator ((f : X → ℂ) + (g : X → ℂ)) := (Lp.coeFn_add f g).indicator
    have ht := (((Lp.memLp (f+g)).indicator hS.nullMeasurableSet).toLp_congr
      (((Lp.memLp f).indicator hS.nullMeasurableSet).add ((Lp.memLp g).indicator hS.nullMeasurableSet))
      (he.trans (Filter.Eventually.of_forall (fun x => by by_cases hx : x ∈ S <;> simp [hx, Pi.add_apply]))))
    exact ht.trans (MemLp.toLp_add _ _)
  map_smul' c f := by
    have he : S.indicator ((c • f : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ]
        S.indicator (c • (f : X → ℂ)) := (Lp.coeFn_smul c f).indicator
    have ht := (((Lp.memLp (c • f)).indicator hS.nullMeasurableSet).toLp_congr
      (((Lp.memLp f).indicator hS.nullMeasurableSet).const_smul c)
      (he.trans (Filter.Eventually.of_forall (fun x => by by_cases hx : x ∈ S <;> simp [hx, Pi.smul_apply, smul_eq_mul]))))
    exact ht.trans (MemLp.toLp_const_smul c _)
include hS in
 lemma cut_bound (f : Lp ℂ 2 μ) : ‖cutLinear μ S hS f‖ ≤ 1 * ‖f‖ := by
  change ‖((Lp.memLp f).indicator hS.nullMeasurableSet).toLp _‖ ≤ _
  rw [Lp.norm_toLp, one_mul, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_lt_top f).ne (eLpNorm_indicator_le f hS.nullMeasurableSet)
 def cutLp : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := (cutLinear μ S hS).mkContinuous 1 (cut_bound μ S hS)
private lemma cutLp_ae (f : Lp ℂ 2 μ) : (cutLp μ S hS f : X → ℂ) =ᵐ[μ] S.indicator (f : X → ℂ) := by
  change (((Lp.memLp f).indicator hS.nullMeasurableSet).toLp (S.indicator (f : X → ℂ)) : X → ℂ) =ᵐ[μ] _
  exact @MemLp.coeFn_toLp X ℂ _ 2 μ _ (S.indicator (f : X → ℂ)) ((Lp.memLp f).indicator hS.nullMeasurableSet)

end Cut

 theorem finite_compact_lifts
    {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [TopologicalSpace Y] (K : Set Y) (hK : IsCompact K)
    (m : ℕ) (D : Fin m → Set X) (Q : Fin m → X → Y)
    (hD : ∀ i, IsOpen (D i)) (hQ : ∀ i, IsOpenMap (Q i))
    (hcov : K ⊆ ⋃ i, Q i '' D i) :
    ∃ C : Fin m → Set X, (∀ i, IsCompact (C i)) ∧
      (∀ i, C i ⊆ D i) ∧ K ⊆ ⋃ i, Q i '' C i := by
  have hlocal : ∀ y : K, ∃ i : Fin m, ∃ (C : Set X),
      IsCompact C ∧ C ⊆ D i ∧ y.val ∈ Q i '' interior C := by
    intro y
    obtain ⟨i, x, hx, hxy⟩ := Set.mem_iUnion.mp (hcov y.property)
    obtain ⟨C, hCn, hCD, hCc⟩ := local_compact_nhds ((hD i).mem_nhds hx)
    exact ⟨i, C, hCc, hCD, x, mem_interior_iff_mem_nhds.mpr hCn, hxy⟩
  choose idx C hCc hCD hCy using hlocal
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : K => Q (idx y) '' interior (C y))
    (fun y => hQ (idx y) _ isOpen_interior) (fun y hy =>
      Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hCy ⟨y, hy⟩⟩)
  refine ⟨fun i => ⋃ y ∈ t.filter (fun y => idx y = i), C y, ?_, ?_, ?_⟩
  · intro i
    exact (t.filter (fun y => idx y = i)).finite_toSet.isCompact_biUnion
      (fun y _ => hCc y)
  · intro i x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
    have he : idx y = i := (Finset.mem_filter.mp hy).2
    exact he ▸ hCD y hxy
  · intro y hy
    obtain ⟨p, hp, x, hx, hxy⟩ := Set.mem_iUnion₂.mp (ht hy)
    refine Set.mem_iUnion.mpr ⟨idx p, x, ?_, hxy⟩
    exact Set.mem_iUnion₂.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩,
      interior_subset hx⟩

open KPContSectorSmoothFramesSupport KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

 def labeledHomeomorph : M F ≃ₜ KPCuspGenuineMonodromy.SymmetricSpace F where
  toFun := labeledA (placeEquiv F ζ hζ)
  invFun := labeledAInv (placeEquiv F ζ hζ)
  left_inv x := by simp [labeledA, labeledAInv]
  right_inv x := by funext k; simp [labeledA, labeledAInv]
  continuous_toFun := by
    apply continuous_pi
    intro k
    exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
  continuous_invFun := by
    apply (CotangentLogCoframe.A (d F)).symm.continuous.comp
    exact continuous_pi (fun k => continuous_apply _)

private theorem chart_q_open (a : ActualChart (U := U) (H := H)) :
    IsOpenMap (q a) := by
  have he : KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component) =
      fun x => (H.atlas U).components ⟨a.component, x⟩ := by
    funext x
    exact ((H.atlas U).components_formula a.component x).symm
  have hc : IsOpenEmbedding (KPFiniteCuspAtlas.componentMap F ζ hζ U
      ((H.atlas U).representative a.component)) := by
    rw [he]
    exact (H.atlas U).components.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk
  have hp : IsOpenMap (KPCuspSiegel.projection F
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)) := by
    letI : ContinuousConstSMul (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)
        (KPCuspGenuineMonodromy.SymmetricSpace F) :=
      ⟨fun g => KPCuspSiegel.continuous_action F g.val⟩
    exact isOpenMap_quotient_mk'_mul
  exact hc.isOpenMap.comp (hp.comp (labeledHomeomorph (ζ := ζ) (hζ := hζ)).isOpenMap)

theorem finite_actual_compact_lifts
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K)
    (m : ℕ) (charts : Fin m → ActualChart (U := U) (H := H))
    (cover : K ⊆ ⋃ i, (charts i).baseDomain) :
    ∃ (C : Fin m → Set (M F)) (hC : ∀ i, IsCompact (C i)),
      (∀ i, C i ⊆ omega (charts i)) ∧ K ⊆ ⋃ i, q (charts i) '' C i := by
  have hc : K ⊆ ⋃ i, q (charts i) '' omega (charts i) := by
    intro y hy
    obtain ⟨i, x, hx⟩ := Set.mem_iUnion.mp (cover hy)
    refine Set.mem_iUnion.mpr ⟨i, labeledAInv (placeEquiv F ζ hζ) x.val, ?_, ?_⟩
    · change labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) x.val) ∈ (charts i).domain
      change (labeledHomeomorph (ζ := ζ) (hζ := hζ))
        ((labeledHomeomorph (ζ := ζ) (hζ := hζ)).symm x.val) ∈ (charts i).domain
      rw [Homeomorph.apply_symm_apply]
      exact x.property
    · change q (charts i) ((labeledHomeomorph (ζ := ζ) (hζ := hζ)).symm x.val) = y
      change KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative (charts i).component)
        (KPCuspSiegel.projection F _ ((labeledHomeomorph (ζ := ζ) (hζ := hζ))
          ((labeledHomeomorph (ζ := ζ) (hζ := hζ)).symm x.val))) = y
      rw [Homeomorph.apply_symm_apply]
      exact hx
  obtain ⟨C, hC, hD, hcov⟩ := finite_compact_lifts K hK m (fun i => omega (charts i))
    (fun i => q (charts i)) (fun i => (charts i).domain_open.preimage
      (labeledHomeomorph (ζ := ζ) (hζ := hζ)).continuous) (fun i => chart_q_open (charts i)) hc
  exact ⟨C, hC, hD, hcov⟩

private theorem gamma_continuous (a : ActualChart (U := U) (H := H))
    (g : Gamma a) : Continuous ((isotropyArrow a g).psi) := by
  have hA : Continuous (labeledA (placeEquiv F ζ hζ)) := by
    apply continuous_pi
    intro k
    exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
  have hAi : Continuous (labeledAInv (placeEquiv F ζ hζ)) := by
    apply (CotangentLogCoframe.A (d F)).symm.continuous.comp
    exact continuous_pi (fun k => continuous_apply _)
  have he : (isotropyArrow a g).psi = fun x => labeledAInv (placeEquiv F ζ hζ)
      ((g.val.1.val : KPCuspArithmetic.PGL2 F) • labeledA (placeEquiv F ζ hζ) x) := by
    funext x
    change coordinateMap (isotropyChart a) (isotropyChart a) g.val.1.val x = _
    simp [coordinateMap, isotropyChart, ChartKind.representative]
  rw [he]
  exact hAi.comp ((KPCuspSiegel.continuous_action F _).comp hA)

private theorem finite_invariant_compact_lift
    (a : ActualChart (U := U) (H := H)) (C : Set (M F)) (hC : IsCompact C)
    (hD : C ⊆ omega a) :
    ∃ D : Set (M F), IsCompact D ∧ D ⊆ omega a ∧ C ⊆ D ∧
      ∀ g : Gamma a, (isotropyArrow a g).psi '' D = D := by
  letI : Finite (Gamma a) := finite_Gamma a
  letI : MulAction (Gamma a) (M F) := gammaMulAction a
  let D := ⋃ g : Gamma a, (isotropyArrow a g).psi '' C
  have hone : ∀ x, (isotropyArrow a 1).psi x = x := (gammaMulAction a).one_smul
  have hmul : ∀ (g h : Gamma a) x, (isotropyArrow a (g*h)).psi x =
      (isotropyArrow a g).psi ((isotropyArrow a h).psi x) := (gammaMulAction a).mul_smul
  refine ⟨D, isCompact_iUnion (fun g => hC.image (gamma_continuous a g)), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨g, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    exact KPContActualCotangentMeasurableFamilies.isotropy_mem a g y (hD hy)
  · intro x hx
    refine Set.mem_iUnion.mpr ⟨1, x, hx, hone x⟩
  · intro g
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨h, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨g*h, z, hz, hmul g h z⟩
    · intro hx
      refine ⟨(isotropyArrow a g⁻¹).psi x, ?_, ?_⟩
      · obtain ⟨h, z, hz, rfl⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨g⁻¹*h, z, hz, hmul g⁻¹ h z⟩
      · rw [← hmul, mul_inv_cancel, hone]

theorem finite_actual_invariant_compact_lifts
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K)
    (m : ℕ) (charts : Fin m → ActualChart (U := U) (H := H))
    (cover : K ⊆ ⋃ i, (charts i).baseDomain) :
    ∃ (C : Fin m → Set (M F)) (hC : ∀ i, IsCompact (C i)),
      (∀ i, C i ⊆ omega (charts i)) ∧
      (∀ i (g : Gamma (charts i)), (isotropyArrow (charts i) g).psi '' C i = C i) ∧
      K ⊆ ⋃ i, q (charts i) '' C i := by
  obtain ⟨C, hC, hD, hcov⟩ := finite_actual_compact_lifts K hK m charts cover
  choose D hDc hDd hDC hDi using fun i => finite_invariant_compact_lift (charts i) (C i) (hC i) (hD i)
  refine ⟨D, hDc, hDd, hDi, ?_⟩
  intro y hy
  obtain ⟨i, x, hx, hxy⟩ := Set.mem_iUnion.mp (hcov hy)
  exact Set.mem_iUnion.mpr ⟨i, x, hDC i hx, hxy⟩

private lemma continuous_chartQ (a : ActualChart (U := U) (H := H)) : Continuous (q a) := by
  have he : KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component) =
      fun x => (H.atlas U).components ⟨a.component,x⟩ := by
    funext x; exact ((H.atlas U).components_formula a.component x).symm
  have hc : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)) := by
    rw [he]; exact (H.atlas U).components.continuous.comp continuous_sigmaMk
  have hA : Continuous (labeledA (placeEquiv F ζ hζ)) := by
    apply continuous_pi; intro k
    exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
  exact hc.comp (continuous_quotient_mk'.comp hA)

private lemma lp_finsetSum_ae {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {I : Type*} (t : Finset I) (f : I → Lp ℂ 2 μ) :
    (∑ i ∈ t, f i : Lp ℂ 2 μ) =ᵐ[μ] (fun x => ∑ i ∈ t, f i x) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 μ
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (Lp.coeFn_add _ _).trans ((Filter.EventuallyEq.refl _ _).add ih)

private lemma partition_sum {X : Type*} (m : ℕ) (A : Fin m → Set X) (u : X → ℂ) (x : X) :
    ∑ i : Fin m, (disjointed A i).indicator u x = (⋃ i, A i).indicator u x := by
  classical
  by_cases hx : x ∈ ⋃ i, A i
  · have hd : x ∈ ⋃ i, disjointed A i := by rwa [iUnion_disjointed]
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hd
    rw [Set.indicator_of_mem hx]
    rw [← Set.indicator_of_mem hi u]
    apply Finset.sum_eq_single i
    · intro j _ hji
      have hj : x ∉ disjointed A j := by
        intro hj
        exact Set.disjoint_left.mp (disjoint_disjointed A hji) hj hi
      simp [hj]
    · simp
  · rw [Set.indicator_of_notMem hx]
    apply Finset.sum_eq_zero
    intro i _
    have hn : x ∉ disjointed A i := fun h => hx (Set.mem_iUnion.mpr ⟨i, disjointed_subset A i h⟩)
    simp [hn]

theorem finite_compact_coefficient_reconstruction_source
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K)
    (m : ℕ) (charts : Fin m → ActualChart (U := U) (H := H))
    (cover : K ⊆ ⋃ i, (charts i).baseDomain) :
    ∃ (C : Fin m → Set (M F)) (hC : ∀ i, IsCompact (C i)),
      (∀ i, C i ⊆ omega (charts i)) ∧
      K ⊆ ⋃ i, q (charts i) '' C i ∧
      (letI : ∀ i, CompactSpace (C i) := fun i => isCompact_iff_compactSpace.mp (hC i)
       ∃ T : ((i : Fin m) → ContinuousMap (C i) ℂ) →L[ℂ]
         KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U,
       ∀ (v : Sections F ζ hζ U R P H),
         IsSmoothSections F ζ hζ U R P H v →
         tsupport (sectionNorm F ζ hζ U R P H v) ⊆ K →
       ∀ (f : (i : Fin m) → ContinuousMap (C i) ℂ),
         (∀ i (x : C i), f i x = (isotropyChart (charts i)).coefficient v x.val) →
       ∀ b : BorelL2Sections F ζ hζ U R P H, b.val = v →
         T f = (toSector F ζ hζ U R P H b :
           KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U)) := by
  obtain ⟨C,hC,hD,hI,hcov⟩ := finite_actual_invariant_compact_lifts K hK m charts cover
  letI : ∀ i, CompactSpace (C i) := fun i => isCompact_iff_compactSpace.mp (hC i)
  choose T hT0 hT using fun i => one_chart_compact_coefficient_averaging_source (charts i) (C i) (hC i) (hD i) (hI i)
  let A : Fin m → Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) := fun i => q (charts i) '' C i
  have hA : ∀ i, MeasurableSet (A i) := fun i => ((hC i).image (continuous_chartQ (charts i))).isClosed.measurableSet
  let S : Fin m → Set (CoveredSpherical F ζ hζ U) := fun i =>
    KPContSectorCoveredQuotientVocabulary.q F ζ hζ U ⁻¹' disjointed A i
  have hS : ∀ i, MeasurableSet (S i) := by
    intro i
    apply (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable
    rw [disjointed_eq_inter_compl]
    exact (hA i).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hA j).compl)
  let L : ((i : Fin m) → ContinuousMap (C i) ℂ) →L[ℂ] KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U :=
    ∑ i : Fin m, ((cutLp (coveredMeasure F ζ hζ R U) (S i) (hS i)).comp (T i)).comp (ContinuousLinearMap.proj i)
  refine ⟨C,hC,hD,hcov,L,?_⟩
  intro v hv hs f hf b hb
  have hi : ∀ i, (cutLp (coveredMeasure F ζ hζ R U) (S i) (hS i) (T i (f i)) : CoveredSpherical F ζ hζ U → ℂ) =ᵐ[
      coveredMeasure F ζ hζ R U] (S i).indicator (scalarRepresentative F ζ hζ U R P H v).val := by
    intro i
    have h1 := cutLp_ae (coveredMeasure F ζ hζ R U) (S i) (hS i) (T i (f i))
    have h2 := (hT i v (f i) (hf i) b hb).indicator (s := S i)
    refine h1.trans (h2.trans (Filter.Eventually.of_forall ?_))
    intro x
    by_cases hx : x ∈ S i
    · have ha : KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x ∈ A i := disjointed_subset A i hx
      simp [hx, ha, A]
    · simp [hx]
  apply Lp.ext
  have hsum := lp_finsetSum_ae (coveredMeasure F ζ hζ R U) Finset.univ
    (fun i => cutLp (coveredMeasure F ζ hζ R U) (S i) (hS i) (T i (f i)))
  have hmatch := Filter.eventually_all.mpr hi
  have hb' := MemLp.coeFn_toLp (representative_memLp F ζ hζ U R P H b)
  filter_upwards [hsum, hmatch, hb'] with x hsum hmatch hb'
  change (L f : CoveredSpherical F ζ hζ U → ℂ) x = _
  have hL : L f = ∑ i : Fin m, cutLp (coveredMeasure F ζ hζ R U) (S i) (hS i) (T i (f i)) := by simp [L]
  rw [hL, hsum]
  simp_rw [hmatch]

  have pp : ∑ i : Fin m, (S i).indicator (scalarRepresentative F ζ hζ U R P H v).val x =
      (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U ⁻¹' (⋃ i, A i)).indicator
        (scalarRepresentative F ζ hζ U R P H v).val x := by
    simpa only [S, Set.indicator, Set.mem_preimage] using
      partition_sum m A (fun _ => (scalarRepresentative F ζ hζ U R P H v).val x)
        (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x)
  rw [pp]
  change _ = ((representative_memLp F ζ hζ U R P H b).toLp _) x
  rw [hb']
  rw [hb]
  by_cases hx : KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x ∈ ⋃ i, A i
  · exact Set.indicator_of_mem (show x ∈ KPContSectorCoveredQuotientVocabulary.q F ζ hζ U ⁻¹' (⋃ i, A i) from hx)
      (scalarRepresentative F ζ hζ U R P H v).val
  · have hz : (scalarRepresentative F ζ hζ U R P H v).val x = 0 := by
      have hnorm := sectionNorm_pullback F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H v) x
      have hSv : KPContSectorScalarLineAlgebra.S F ζ hζ U R P H
          (scalarRepresentative F ζ hζ U R P H v) = v :=
        (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H).apply_symm_apply v
      rw [hSv] at hnorm
      apply norm_eq_zero.mp
      rw [← hnorm]
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      exact hx (hcov (hs hmem))
    simp [hx, hz]

end DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

end

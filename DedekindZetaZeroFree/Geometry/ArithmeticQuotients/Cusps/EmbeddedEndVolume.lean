module

public import DedekindZetaZeroFree.Geometry.Cusps.SiegelReduction.CoverFromFrameBounds

@[expose] public section

noncomputable section
open scoped Classical NumberField Pointwise
open MeasureTheory

namespace DedekindZetaZeroFree.KPFiniteAdelicCuspEnds

theorem fd_ae_unique {G X : Type*} [Group G] [Countable G]
    [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X]
    (μ : Measure X) [SMulInvariantMeasure G X μ]
    (s : Set X) (hs : IsFundamentalDomain G s μ) :
    ∀ᵐ x ∂μ, ∃! g : G, g • x ∈ s := by
  have hd : ∀ᵐ x ∂μ, ∀ a b : G, a ≠ b → ¬ (a • x ∈ s ∧ b • x ∈ s) := by
    apply (ae_all_iff).2
    intro a
    apply (ae_all_iff).2
    intro b
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall (by simp [hab])
    · have h := hs.aedisjoint (i := a⁻¹) (j := b⁻¹) (by simpa only [ne_eq, inv_inj] using hab)
      have he : μ ((a⁻¹ • s) ∩ (b⁻¹ • s)) = 0 := h
      have hz : ∀ᵐ x ∂μ, x ∉ ((a⁻¹ • s) ∩ (b⁻¹ • s)) := by
        exact ae_iff.mpr (by simpa using he)
      filter_upwards [hz] with x hx
      intro _
      simpa only [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem, inv_inv,
        Set.mem_setOf_eq] using hx
  filter_upwards [hs.ae_covers, hd] with x hx hd
  obtain ⟨a, ha⟩ := hx
  refine ⟨a, ha, ?_⟩
  intro b hb
  by_contra hba
  exact hd b a hba ⟨hb, ha⟩

theorem fd_ae_free {G X : Type*} [Group G] [Countable G]
    [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X]
    (μ : Measure X) [SMulInvariantMeasure G X μ]
    (s : Set X) (hs : IsFundamentalDomain G s μ) :
    ∀ᵐ x ∂μ, ∀ g : G, g • x = x → g = 1 := by
  filter_upwards [fd_ae_unique μ s hs] with x hx
  intro g hg
  obtain ⟨a, ha, hu⟩ := hx
  have h := hu (a * g) (by simpa only [mul_smul, hg] using ha)
  exact mul_left_cancel (h.trans (mul_one a).symm)

theorem glue_partial_fd {G X : Type*} [Group G] [Countable G]
    [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X]
    (μ : Measure X) [SMulInvariantMeasure G X μ]
    (A B E : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hE : MeasurableSet E) (hBE : B ⊆ E)
    (hinv : ∀ g : G, (fun x => g • x) ⁻¹' E = E)
    (hFD : IsFundamentalDomain G A μ)
    (hlocal : IsFundamentalDomain G B (μ.restrict E)) :
    IsFundamentalDomain G (B ∪ (A \ E)) μ := by
  have hmem (g : G) (x : X) : g • x ∈ E ↔ x ∈ E := by
    change x ∈ (fun x => g • x) ⁻¹' E ↔ x ∈ E
    rw [hinv]
  refine IsFundamentalDomain.mk'' (hB.union (hA.diff hE)).nullMeasurableSet ?_ ?_
    (fun g => (measurePreserving_smul g μ).quasiMeasurePreserving)
  · have hc : ∀ᵐ x ∂μ, x ∈ E → ∃ g : G, g • x ∈ B := by
      exact (ae_restrict_iff' hE).mp hlocal.ae_covers
    filter_upwards [hFD.ae_covers, hc] with x hx hc
    by_cases hxE : x ∈ E
    · obtain ⟨g, hg⟩ := hc hxE
      exact ⟨g, Or.inl hg⟩
    · obtain ⟨g, hg⟩ := hx
      exact ⟨g, Or.inr ⟨hg, (hmem g x).not.mpr hxE⟩⟩
  · intro g hg
    have hl := hlocal.aedisjoint (i := g) (j := 1) hg
    have hlzero : (μ.restrict E) ((g • B) ∩ B) = 0 := by
      change (μ.restrict E) ((g • B) ∩ (1 • B)) = 0 at hl
      simpa only [one_smul] using hl
    have hlzero' : μ ((g • B) ∩ B) = 0 := by
      rw [Measure.restrict_apply ((hB.const_smul g).inter hB)] at hlzero
      rwa [Set.inter_eq_left.mpr (Set.inter_subset_right.trans hBE)] at hlzero
    have hazero : μ ((g • A) ∩ A) = 0 := by
      have h := hFD.aedisjoint (i := g) (j := 1) hg
      change μ ((g • A) ∩ (1 • A)) = 0 at h
      simpa only [one_smul] using h
    apply measure_mono_null (t := ((g • B) ∩ B) ∪ ((g • A) ∩ A)) ?_
      (measure_union_null hlzero' hazero)
    rintro x ⟨hxg, hxs⟩
    obtain ⟨y, hy, rfl⟩ := hxg
    rcases hy with hy | hy <;> rcases hxs with hx | hx
    · exact Or.inl ⟨Set.smul_mem_smul_set hy, hx⟩
    · exact False.elim (hx.2 ((hmem g y).mpr (hBE hy)))
    · exact False.elim (hy.2 ((hmem g y).mp (hBE hx)))
    · exact Or.inr ⟨Set.smul_mem_smul_set hy.1, hx.1⟩

theorem partial_fd_quotient_measure {G X : Type*} [Group G] [Countable G]
    [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X]
    (μ : Measure X) [SMulInvariantMeasure G X μ]
    (A B E : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hE : MeasurableSet E) (hBE : B ⊆ E)
    (hinv : ∀ g : G, (fun x => g • x) ⁻¹' E = E)
    (hFD : IsFundamentalDomain G A μ)
    (hlocal : IsFundamentalDomain G B (μ.restrict E)) :
    Measure.map (Quotient.mk (MulAction.orbitRel G X)) (μ.restrict B) =
    (Measure.map (Quotient.mk (MulAction.orbitRel G X)) (μ.restrict A)).restrict
      ((Quotient.mk (MulAction.orbitRel G X)) '' E) := by
  let π := Quotient.mk (MulAction.orbitRel G X)
  have hpre : π ⁻¹' (π '' E) = E := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, he⟩
      have hrel := Quotient.exact he
      obtain ⟨g, hg⟩ := hrel
      have hm : g • x ∈ E := by
        change g • x = y at hg
        rw [hg]
        exact hy
      change x ∈ (fun x => g • x) ⁻¹' E at hm
      rwa [hinv] at hm
    · exact Set.subset_preimage_image _ _
  have hπE : MeasurableSet (π '' E) := by
    apply measurableSet_quotient.mpr
    change MeasurableSet (π ⁻¹' (π '' E))
    rwa [hpre]
  have heq := hFD.quotientMeasure_eq μ (glue_partial_fd μ A B E hA hB hE hBE hinv hFD hlocal)
  rw [heq]
  ext V hV
  rw [Measure.restrict_apply hV,
    measure_map_restrict_apply (meas_U := hV.inter hπE),
    measure_map_restrict_apply (meas_U := hV)]
  apply congrArg μ
  change π ⁻¹' V ∩ B = π ⁻¹' (V ∩ π '' E) ∩ (B ∪ A \ E)
  rw [Set.preimage_inter, hpre]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_diff]
  constructor
  · rintro ⟨hx, hb⟩; exact ⟨⟨hx, hBE hb⟩, Or.inl hb⟩
  · rintro ⟨⟨hx, he⟩, hb | ha⟩
    · exact ⟨hx, hb⟩
    · exact False.elim (ha.2 he)

theorem partial_fd_of_local_unique {G X : Type*} [Group G] [Countable G]
    [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X]
    (μ : Measure X) [SMulInvariantMeasure G X μ]
    (B U : Set X) (hB : MeasurableSet B) (hU : MeasurableSet U)
    (hunique : ∀ᵐ x ∂μ.restrict U, ∃! g : G, g • x ∈ B) :
    IsFundamentalDomain G B (μ.restrict (⋃ g : G, g • U)) := by
  let E := ⋃ g : G, g • U
  have hE : MeasurableSet E := .iUnion (fun g => hU.const_smul g)
  have hi (g : G) : (fun x : X => g • x) ⁻¹' E = E := by
    ext x
    simp only [E, Set.mem_preimage, Set.mem_iUnion, Set.mem_smul_set_iff_inv_smul_mem]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨g⁻¹ * a, by simpa only [mul_inv_rev, inv_inv, mul_smul] using ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨g * a, by simpa only [mul_inv_rev, mul_smul, inv_smul_smul] using ha⟩
  have hu : ∀ᵐ x ∂μ, x ∈ U → ∃! g : G, g • x ∈ B :=
    (ae_restrict_iff' hU).mp hunique
  have hall : ∀ᵐ x ∂μ, ∀ a : G, a⁻¹ • x ∈ U → ∃! g : G, g • (a⁻¹ • x) ∈ B := by
    apply ae_all_iff.mpr
    intro a
    exact (measurePreserving_smul a⁻¹ μ).quasiMeasurePreserving.ae hu
  have heuniq : ∀ᵐ x ∂μ.restrict E, ∃! g : G, g • x ∈ B := by
    apply (ae_restrict_iff' hE).mpr
    filter_upwards [hall] with x hx
    intro hxE
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hxE
    rw [Set.mem_smul_set_iff_inv_smul_mem] at ha
    obtain ⟨b, hb, hbu⟩ := hx a ha
    refine ⟨b * a⁻¹, by simpa only [mul_smul] using hb, ?_⟩
    intro c hc
    have hca := hbu (c * a) (by simpa only [mul_smul, smul_inv_smul] using hc)
    have hc' := congrArg (fun g : G => g * a⁻¹) hca
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using hc'
  letI : SMulInvariantMeasure G X (μ.restrict E) := by
    constructor
    intro g s hs
    have hp := (measurePreserving_smul g μ).restrict_preimage hE
    rw [hi] at hp
    rw [← Measure.map_apply hp.measurable hs, hp.map_eq]
  refine IsFundamentalDomain.mk'' (hB.nullMeasurableSet) (heuniq.mono (fun _ h => h.exists))
    ?_ (fun g => (measurePreserving_smul g (μ.restrict E)).quasiMeasurePreserving)
  intro g hg
  change (μ.restrict E) ((g • B) ∩ B) = 0
  have hz : ∀ᵐ x ∂μ.restrict E, x ∉ ((g • B) ∩ B) := by
    filter_upwards [heuniq] with x hx
    simp only [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem]
    rintro ⟨hxg, hxb⟩
    obtain ⟨a, ha, hu⟩ := hx
    have h1 := hu 1 (by simpa only [one_smul] using hxb)
    have hg' := hu g⁻¹ hxg
    exact hg (by simpa only [inv_eq_one] using hg'.trans h1.symm)
  simpa using ae_iff.mp hz

theorem chart_actual_cross_action
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S)
    (G : KPCuspCharts.ChartOutput F hF S D) (g : S) (p : KPCuspCharts.Coordinates F) :
    (g : KPCuspArithmetic.PGL2 F) • KPCuspCharts.toArch F p =
      KPCuspCharts.toArch F (G.crossAction g p.1, p.2) := by
  obtain ⟨A, hA, hc⟩ := D.upper g g.property
  change KPCuspSiegel.action F _ _ = _
  rw [G.actual_action g A hA hc, G.crossAction_formula g A hA hc]
  rfl

theorem arch_smul_measurePreserving
    (F : Type) [Field F] [NumberField F] (g : KPCuspArithmetic.PGL2 F) :
    MeasurePreserving (fun z : KPArch.Space (KPCuspLogShape.dimension F) => g • z)
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) := by
  refine ⟨(KPCuspCharts.projectiveHomeomorph F g).continuous.measurable, ?_⟩
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  have he : (fun z : KPArch.Space (KPCuspLogShape.dimension F) =>
      Matrix.ProjGenLinGroup.mk A • z) = KPCuspSiegel.glAction F A := by
    funext z
    exact KPCuspSiegel.action_mk F A z
  rw [he]
  exact KPArch.hyperbolicVolume_invariant _ _

theorem cusp_end_coordinate_volume
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (Γ S : Subgroup (KPCuspArithmetic.PGL2 F))
    (σ : KPCuspArithmetic.PGL2 F) (T : ℝ)
    (D : KPCuspCharts.ParabolicData F S)
    (G : KPCuspCharts.ChartOutput F hF S D)
    (f : KPCuspCharts.HighQuotient F S T → KPCuspSiegel.OrbitQuotient F Γ)
    (hf : ∀ (p : {p : KPCuspCharts.Coordinates F // T < p.2}),
      f (Quotient.mk _ p) =
        KPCuspSiegel.projection F Γ (σ • KPCuspCharts.toArch F p.val)) :
    Measure.map f
      (Measure.map (G.highPresentation T)
        (G.sectionMeasure.prod
          (Measure.comap (Subtype.val : Set.Ioi T → ℝ)
            (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))))) =
    Measure.map ((KPCuspSiegel.projection F Γ) ∘
      ((KPCuspCharts.projectiveHomeomorph F σ) ∘ (KPCuspCharts.toArchHomeomorph F
        G.positive_dimension)))
      ((((volume.prod G.shapeMeasure).prod
        (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))).restrict
          {p : KPCuspCharts.Coordinates F | p.1 ∈ G.fundamentalDomain}).restrict
            {p : KPCuspCharts.Coordinates F | T < p.2}) := by
  have hproj : Measurable (KPCuspSiegel.projection F Γ) := measurable_quotient_mk''
  have hcoord : Measurable (fun p : KPCuspCharts.Coordinates F =>
      KPCuspSiegel.projection F Γ (σ • KPCuspCharts.toArch F p)) :=
    hproj.comp ((KPCuspCharts.projectiveHomeomorph F σ).continuous.measurable.comp
      (KPCuspCharts.toArch_contDiff F).continuous.measurable)
  have hfm : Measurable f := measurable_from_quotient.mpr (by
    convert hcoord.comp measurable_subtype_coe using 1
    funext p
    exact hf p)
  rw [G.highVolume_formula T, Measure.map_map hfm measurable_quotient_mk'']
  have heq : f ∘ Quotient.mk (KPCuspCharts.highRelation F S T) =
      (fun p : KPCuspCharts.Coordinates F =>
        KPCuspSiegel.projection F Γ (σ • KPCuspCharts.toArch F p)) ∘ Subtype.val := by
    funext p
    exact hf p
  rw [heq, ← Measure.map_map hcoord measurable_subtype_coe]
  congr 1
  exact map_comap_subtype_coe (s := {p : KPCuspCharts.Coordinates F | T < p.2})
    (measurableSet_lt measurable_const measurable_snd) _

theorem cusp_end_arch_volume
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (Γ S : Subgroup (KPCuspArithmetic.PGL2 F))
    (σ : KPCuspArithmetic.PGL2 F) (T : ℝ)
    (D : KPCuspCharts.ParabolicData F S)
    (G : KPCuspCharts.ChartOutput F hF S D)
    (f : KPCuspCharts.HighQuotient F S T → KPCuspSiegel.OrbitQuotient F Γ)
    (hf : ∀ (p : {p : KPCuspCharts.Coordinates F // T < p.2}),
      f (Quotient.mk _ p) =
        KPCuspSiegel.projection F Γ (σ • KPCuspCharts.toArch F p.val)) :
    Measure.map f
      (Measure.map (G.highPresentation T)
        (G.sectionMeasure.prod
          (Measure.comap (Subtype.val : Set.Ioi T → ℝ)
            (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))))) =
    Measure.map (KPCuspSiegel.projection F Γ)
      ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict
        ((fun p : KPCuspCharts.Coordinates F => σ • KPCuspCharts.toArch F p) ''
          {p | p.1 ∈ G.fundamentalDomain ∧ T < p.2})) := by
  let e := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).trans
    (KPCuspCharts.projectiveHomeomorph F σ)
  let μ : Measure (KPCuspCharts.Coordinates F) := (volume.prod G.shapeMeasure).prod
    (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))
  have he : Measure.map e μ = KPArch.hyperbolicVolume (KPCuspLogShape.dimension F) := by
    change Measure.map ((KPCuspCharts.projectiveHomeomorph F σ) ∘
      (KPCuspCharts.toArchHomeomorph F G.positive_dimension)) μ = _
    rw [← Measure.map_map
      (KPCuspCharts.projectiveHomeomorph F σ).continuous.measurable
      (KPCuspCharts.toArchHomeomorph F G.positive_dimension).continuous.measurable]
    change Measure.map (KPCuspSiegel.action F σ)
      (Measure.map (KPCuspCharts.toArch F) μ) = _
    rw [G.archVolume_formula]
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective σ
    have ha : KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk A) =
        KPCuspSiegel.glAction F A := by
      funext z
      exact KPCuspSiegel.action_mk F A z
    rw [ha]
    exact KPArch.hyperbolicVolume_invariant _ _
  rw [cusp_end_coordinate_volume F hF Γ S σ T D G f hf]
  change Measure.map ((KPCuspSiegel.projection F Γ) ∘ e)
      ((μ.restrict {p | p.1 ∈ G.fundamentalDomain}).restrict {p | T < p.2}) =
    Measure.map (KPCuspSiegel.projection F Γ)
      ((KPArch.hyperbolicVolume _).restrict (e '' {p | p.1 ∈ G.fundamentalDomain ∧ T < p.2}))
  rw [← Measure.map_map (show Measurable (KPCuspSiegel.projection F Γ) from
    measurable_quotient_mk'') e.continuous.measurable]
  congr 1
  rw [Measure.restrict_restrict (measurableSet_lt measurable_const measurable_snd)]
  have hi : {p : KPCuspCharts.Coordinates F | T < p.2} ∩
      {p | p.1 ∈ G.fundamentalDomain} = {p | p.1 ∈ G.fundamentalDomain ∧ T < p.2} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_comm]
  rw [hi, ← he, e.measurableEmbedding.restrict_map,
    Set.preimage_image_eq _ e.injective]

section PartialDomain
open scoped Pointwise
variable {H X : Type*} [Group H] [MulAction H X] [MeasurableSpace X]
 [Countable H] [MeasurableConstSMul H X]
 {μ : Measure X} [SMulInvariantMeasure H X μ]

end PartialDomain

theorem embedded_cusp_end_volume
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q) (T : ℝ)
    (D : KPCuspCharts.ParabolicData F
      (KPCuspArithmetic.conjugatedStabilizer F Γ q σ))
    (G : KPCuspCharts.ChartOutput F hF _ D)
    (f : KPCuspCharts.HighQuotient F
      (KPCuspArithmetic.conjugatedStabilizer F Γ q σ) T →
        KPCuspSiegel.OrbitQuotient F Γ)
    (hf : ∀ (p : {p : KPCuspCharts.Coordinates F // T < p.2}),
      f (Quotient.mk _ p) =
        KPCuspSiegel.projection F Γ (σ • KPCuspCharts.toArch F p.val))
    (he : Topology.IsEmbedding f)
    (A : Set (KPArch.Space (KPCuspLogShape.dimension F)))
    (hA : MeasurableSet A)
    (hFD : IsFundamentalDomain Γ A
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))) :
    Measure.map f
      (Measure.map (G.highPresentation T)
        (G.sectionMeasure.prod
          (Measure.comap (Subtype.val : Set.Ioi T → ℝ)
            (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))))) =
    (Measure.map (KPCuspSiegel.projection F Γ)
      ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict A)).restrict
      (KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F σ T) := by
  let S := KPCuspArithmetic.conjugatedStabilizer F Γ q σ
  let e := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).trans
    (KPCuspCharts.projectiveHomeomorph F σ)
  let μ : Measure (KPCuspCharts.Coordinates F) := (volume.prod G.shapeMeasure).prod
    (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))
  let U := KPCuspSiegel.highCusp F σ T
  let C : Set (KPCuspCharts.Coordinates F) := {p | p.1 ∈ G.fundamentalDomain ∧ T < p.2}
  let B := e '' C
  have hC : MeasurableSet C :=
    (G.measurable_fundamentalDomain.preimage measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)
  have hB : MeasurableSet B := e.measurableEmbedding.measurableSet_image.mpr hC
  have hU : MeasurableSet U := (KPCuspSiegel.isOpen_highCusp F σ T).measurableSet
  have heμ : Measure.map e μ = KPArch.hyperbolicVolume (KPCuspLogShape.dimension F) := by
    change Measure.map ((KPCuspCharts.projectiveHomeomorph F σ) ∘
      (KPCuspCharts.toArchHomeomorph F G.positive_dimension)) μ = _
    rw [← Measure.map_map
      (KPCuspCharts.projectiveHomeomorph F σ).continuous.measurable
      (KPCuspCharts.toArchHomeomorph F G.positive_dimension).continuous.measurable]
    change Measure.map (fun z => σ • z) (Measure.map (KPCuspCharts.toArch F) μ) = _
    rw [G.archVolume_formula]
    exact (arch_smul_measurePreserving F σ).map_eq
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := by
    change Countable (Fin 2 → Fin 2 → F); infer_instance
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Function.Injective.countable Units.val_injective
  letI : Countable (KPCuspArithmetic.PGL2 F) :=
    Function.Surjective.countable Matrix.ProjGenLinGroup.mk_surjective
  letI : Countable S := inferInstance
  letI : Countable Γ := inferInstance
  letI := KPCuspCharts.homeomorphAction G.crossAction
  letI : MeasurableConstSMul S (KPCuspCharts.Cross F) := ⟨fun s => (G.crossAction s).measurable⟩
  letI : SMulInvariantMeasure S (KPCuspCharts.Cross F) (volume.prod G.shapeMeasure) := by
    constructor
    intro s V hV
    change (volume.prod G.shapeMeasure) ((G.crossAction s) ⁻¹' V) = _
    rw [← Measure.map_apply (G.crossAction s).measurable hV, G.measure_invariant]
  letI : SigmaFinite (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)) := by
    unfold KPCuspCharts.radialMeasure; infer_instance
  have hcross := fd_ae_unique (volume.prod G.shapeMeasure) G.fundamentalDomain G.isFundamentalDomain
  have hcoord : ∀ᵐ p ∂μ, ∃! s : S, G.crossAction s p.1 ∈ G.fundamentalDomain :=
    (Measure.quasiMeasurePreserving_fst (ν := KPCuspCharts.radialMeasure
      (KPCuspLogShape.dimension F))).ae hcross
  have harch : ∀ᵐ x ∂KPArch.hyperbolicVolume (KPCuspLogShape.dimension F),
      ∃! s : S, G.crossAction s (e.symm x).1 ∈ G.fundamentalDomain := by
    rw [← heμ]
    exact e.measurableEmbedding.ae_map_iff.mpr (by simpa using hcoord)
  let j : S → Γ := fun s => ⟨σ * (s : KPCuspArithmetic.PGL2 F) * σ⁻¹, by
    obtain ⟨a, ha, has⟩ := s.property
    have hs : σ⁻¹ * a * σ = (s : KPCuspArithmetic.PGL2 F) := by
      change σ⁻¹ * a * (σ⁻¹)⁻¹ = (s : KPCuspArithmetic.PGL2 F) at has
      simpa only [inv_inv] using has
    rw [← hs]
    have haΓ : a ∈ Γ := ha.1
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using haΓ⟩
  have jeq (s : S) : (j s : KPCuspArithmetic.PGL2 F) = σ * s * σ⁻¹ := rfl
  have hequiv (s : S) (p : KPCuspCharts.Coordinates F) :
      j s • e p = e (G.crossAction s p.1, p.2) := by
    change (σ * (s : KPCuspArithmetic.PGL2 F) * σ⁻¹) •
      (σ • KPCuspCharts.toArch F p) = σ • KPCuspCharts.toArch F _
    rw [mul_smul, mul_smul, inv_smul_smul, chart_actual_cross_action F hF S D G]
  have hhigh (p : KPCuspCharts.Coordinates F) : e p ∈ U ↔ T < p.2 := by
    change σ • KPCuspCharts.toArch F p ∈ KPCuspSiegel.highCusp F σ T ↔ _
    rw [KPCuspSiegel.highCusp]
    constructor
    · rintro ⟨z, hz, hez⟩
      have hz' : z = KPCuspCharts.toArch F p := by
        exact (MulAction.injective σ) hez
      rw [hz'] at hz
      change T < KPCuspLogShape.meanHeight _ (KPCuspCharts.toArch F p) at hz
      rwa [KPCuspCharts.toArch_meanHeight F G.positive_dimension] at hz
    · intro hp
      exact ⟨KPCuspCharts.toArch F p, by
        simpa only [Set.mem_setOf_eq, KPCuspCharts.toArch_meanHeight F G.positive_dimension] using hp, rfl⟩
  have hBU : B ⊆ U := by
    rintro x ⟨p, hp, rfl⟩
    exact (hhigh p).mpr hp.2
  letI : MeasurableConstSMul Γ (KPArch.Space (KPCuspLogShape.dimension F)) :=
    ⟨fun g => (arch_smul_measurePreserving F g).measurable⟩
  letI : SMulInvariantMeasure Γ (KPArch.Space (KPCuspLogShape.dimension F))
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) := by
    constructor
    intro g V hV
    exact (arch_smul_measurePreserving F g).measure_preimage hV.nullMeasurableSet
  have hlocal : ∀ᵐ x ∂(KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict U,
      ∃! g : Γ, g • x ∈ B := by
    apply (ae_restrict_iff' hU).mpr
    filter_upwards [harch, fd_ae_free _ A hFD] with x hx hfree
    intro hxU
    let p := e.symm x
    have hpx : e p = x := e.apply_symm_apply x
    have hp : T < p.2 := (hhigh p).mp (hpx.symm ▸ hxU)
    obtain ⟨s, hs, hsu⟩ := hx
    refine ⟨j s, ?_, ?_⟩
    · refine ⟨(G.crossAction s p.1, p.2), ⟨hs, hp⟩, ?_⟩
      rw [← hequiv, hpx]
    · intro g hg
      obtain ⟨r, hr, hrg⟩ := hg
      have hfr : f (Quotient.mk _ (⟨r, hr.2⟩ : {p : KPCuspCharts.Coordinates F // T < p.2})) =
          f (Quotient.mk _ (⟨p, hp⟩ : {p : KPCuspCharts.Coordinates F // T < p.2})) := by
        rw [hf, hf]
        change KPCuspSiegel.projection F Γ (e r) = KPCuspSiegel.projection F Γ (e p)
        rw [hrg, hpx]
        exact Quotient.sound (by exact ⟨g, rfl⟩)
      have hrel := Quotient.exact (he.injective hfr)
      obtain ⟨a, ha⟩ := hrel
      have hae : j a • e p = e r := by
        change (a : KPCuspArithmetic.PGL2 F) • KPCuspCharts.toArch F p =
          KPCuspCharts.toArch F r at ha
        change (σ * (a : KPCuspArithmetic.PGL2 F) * σ⁻¹) •
          (σ • KPCuspCharts.toArch F p) = σ • KPCuspCharts.toArch F r
        rw [mul_smul, mul_smul, inv_smul_smul, ha]
      have har : (G.crossAction a p.1, p.2) = r := e.injective ((hequiv a p).symm.trans hae)
      have has : a = s := hsu a (by rw [← har] at hr; exact hr.1)
      have hact : g • x = j s • x := hrg.symm.trans (by simpa only [hpx, has] using hae.symm)
      have hfix : ((j s)⁻¹ * g) • x = x := by rw [mul_smul, hact, inv_smul_smul]
      have h := hfree _ hfix
      exact (inv_mul_eq_one.mp h).symm
  let E := ⋃ g : Γ, g • U
  have hE : MeasurableSet E := .iUnion (fun g => hU.const_smul g)
  have hUE : U ⊆ E := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨1, by simpa only [one_smul] using hx⟩
  have hinv (g : Γ) : (fun x => g • x) ⁻¹' E = E := by
    ext x
    simp only [E, Set.mem_preimage, Set.mem_iUnion, Set.mem_smul_set_iff_inv_smul_mem]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨g⁻¹ * a, by simpa only [mul_inv_rev, inv_inv, mul_smul] using ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨g * a, by simpa only [mul_inv_rev, mul_smul, inv_smul_smul] using ha⟩
  have hlocalFD := partial_fd_of_local_unique
    (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) B U hB hU hlocal
  have hvol := partial_fd_quotient_measure
    (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) A B E hA hB hE
      (hBU.trans hUE) hinv hFD hlocalFD
  have himage : KPCuspSiegel.projection F Γ '' E = KPCuspSiegel.projection F Γ '' U := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y, hy, rfl⟩ := hg
      refine ⟨y, hy, ?_⟩
      exact Quotient.sound (by exact ⟨g⁻¹, inv_smul_smul g y⟩)
    · exact Set.image_mono hUE
  rw [cusp_end_arch_volume F hF Γ S σ T D G f hf]
  change Measure.map (KPCuspSiegel.projection F Γ)
    ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict B) = _
  change Measure.map (KPCuspSiegel.projection F Γ)
    ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict B) =
    (Measure.map (KPCuspSiegel.projection F Γ)
      ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict A)).restrict
        (KPCuspSiegel.projection F Γ '' E) at hvol
  rw [himage] at hvol
  exact hvol

end DedekindZetaZeroFree.KPFiniteAdelicCuspEnds

end

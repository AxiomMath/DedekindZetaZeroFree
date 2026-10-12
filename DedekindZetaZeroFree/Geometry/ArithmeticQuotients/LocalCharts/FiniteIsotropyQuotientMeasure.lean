module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.LineBundleLocalization

@[expose] public section

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Topology

namespace DedekindZetaZeroFree.CoreChartLocalizers.CutoffConstruction

private theorem coset_param_bijective {G : Type*} [Group G] (H : Subgroup G) :
 Function.Bijective (fun p : (G ⧸ H) × H => p.1.out * p.2.val) := by
 constructor
 · rintro ⟨q,h⟩ ⟨r,k⟩ he
   have hq : (q.out * h.val : G ⧸ H) = q := by
     rw [← Quotient.out_eq' q]; exact QuotientGroup.eq.mpr (by simpa using h.property)
   have hr : (r.out * k.val : G ⧸ H) = r := by
     rw [← Quotient.out_eq' r]; exact QuotientGroup.eq.mpr (by simpa using k.property)
   have hqr : q = r := hq.symm.trans ((congrArg (fun g : G => (g : G ⧸ H)) he).trans hr)
   subst r
   have hhk : h = k := Subtype.ext (mul_left_cancel he)
   subst k; rfl
 · intro g
   let q : G ⧸ H := g
   have hg : q.out⁻¹ * g ∈ H := QuotientGroup.eq.mp (Quotient.out_eq' q)
   exact ⟨(q, ⟨q.out⁻¹ * g,hg⟩), by simp⟩

private theorem local_measure_card {G X : Type*} [Group G] [Countable G]
 [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X]
 (μ : Measure X) [SMulInvariantMeasure G X μ]
 (H : Subgroup G) [Fintype H] (D T : Set X)
 (hD : MeasurableSet D) (hT : MeasurableSet T)
 (hFD : IsFundamentalDomain G D μ)
 (hinv : ∀ h : H, (h.val : G) • T = T)
 (hsep : ∀ g : G, ∀ x ∈ T, g • x ∈ T → g ∈ H) :
 μ T = (Fintype.card H : ℝ≥0∞) * μ ((⋃ g : G, g • T) ∩ D) := by
 letI : Countable (G ⧸ H) := Function.Surjective.countable Quotient.mk''_surjective
 let e : (G ⧸ H) × H ≃ G := Equiv.ofBijective _ (coset_param_bijective H)
 have he (q : G ⧸ H) (h : H) : e (q,h) = q.out * h.val := rfl
 have hi : (⋃ g : G, g • T) = ⋃ q : G ⧸ H, q.out • T := by
   apply Set.Subset.antisymm
   · intro x hx
     obtain ⟨g,hg⟩ := Set.mem_iUnion.mp hx
     obtain ⟨⟨q,h⟩,rfl⟩ := e.surjective g
     rw [he, mul_smul, hinv] at hg
     exact Set.mem_iUnion.mpr ⟨q,hg⟩
   · exact Set.iUnion_subset fun q => Set.subset_iUnion (fun g : G => g • T) q.out
 have hd : Pairwise (Function.onFun Disjoint (fun q : G ⧸ H => q.out • T ∩ D)) := by
   intro q r hqr
   apply Set.disjoint_left.mpr
   rintro x ⟨hx,_⟩ ⟨hy,_⟩
   obtain ⟨a,ha,heqa⟩ := hx
   obtain ⟨b,hb,heqb⟩ := hy
   change q.out • a = x at heqa
   change r.out • b = x at heqb
   have hab : (r.out⁻¹ * q.out) • a = b := by
     rw [mul_smul, heqa, ← heqb, inv_smul_smul]
   have hmem := hsep (r.out⁻¹ * q.out) a ha (hab ▸ hb)
   have heq : r = q := by
     rw [← Quotient.out_eq' r, ← Quotient.out_eq' q]
     exact QuotientGroup.eq.mpr hmem
   exact hqr heq.symm
 calc
  μ T = ∑' g : G, μ (g • T ∩ D) := hFD.measure_eq_tsum T
  _ = ∑' p : (G ⧸ H) × H, μ (e p • T ∩ D) := (e.tsum_eq _).symm
  _ = ∑' q : G ⧸ H, ∑' h : H, μ (q.out • T ∩ D) := by
    rw [ENNReal.tsum_prod']; congr 1; ext q; congr 1; ext h
    rw [he, mul_smul, hinv]
  _ = (Fintype.card H : ℝ≥0∞) * ∑' q : G ⧸ H, μ (q.out • T ∩ D) := by
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ENNReal.tsum_mul_left]
  _ = (Fintype.card H : ℝ≥0∞) * μ ((⋃ g : G, g • T) ∩ D) := by
    rw [hi, Set.iUnion_inter, measure_iUnion hd (fun q => (hT.const_smul q.out).inter hD)]

private theorem local_quotient_card {G X : Type*} [Group G] [Countable G]
 [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X]
 (μ : Measure X) [SMulInvariantMeasure G X μ]
 (H : Subgroup G) [Fintype H] (D S : Set X)
 (hD : MeasurableSet D) (hS : MeasurableSet S)
 (hFD : IsFundamentalDomain G D μ)
 (hinv : ∀ h : H, (h.val : G) • S = S)
 (hsep : ∀ g : G, ∀ x ∈ S, g • x ∈ S → g ∈ H) :
 Measure.map (Quotient.mk (MulAction.orbitRel G X))
   ((Fintype.card H : ℝ≥0∞)⁻¹ • μ.restrict S) =
 (Measure.map (Quotient.mk (MulAction.orbitRel G X)) (μ.restrict D)).restrict
   ((Quotient.mk (MulAction.orbitRel G X)) '' S) := by
 let π := Quotient.mk (MulAction.orbitRel G X)
 have hp : Measurable π := measurable_quotient_mk''
 have hpre : π ⁻¹' (π '' S) = ⋃ g : G, g • S := by
   ext x; constructor
   · rintro ⟨y,hy,he⟩
     obtain ⟨g,hg⟩ := Quotient.exact he
     change g • x = y at hg
     exact Set.mem_iUnion.mpr ⟨g⁻¹, y,hy, by simp [← hg]⟩
   · intro hx
     obtain ⟨g,y,hy,he⟩ := Set.mem_iUnion.mp hx
     refine ⟨y,hy,Quotient.sound ?_⟩
     exact ⟨g⁻¹, by change g⁻¹ • x = y; simpa only [← he, inv_smul_smul]⟩
 have hπS : MeasurableSet (π '' S) := by
   apply measurableSet_quotient.mpr
   rw [hpre]; exact .iUnion (fun g => hS.const_smul g)
 ext V hV
 rw [Measure.map_smul _ hp.aemeasurable, Measure.smul_apply,
   Measure.map_apply hp hV, Measure.restrict_apply (hp hV),
   Measure.restrict_apply hV, Measure.map_apply hp (hV.inter hπS),
   Measure.restrict_apply (hp (hV.inter hπS))]
 change (Fintype.card H : ℝ≥0∞)⁻¹ * μ (π ⁻¹' V ∩ S) = _
 have he : π ⁻¹' (V ∩ π '' S) = ⋃ g : G, g • (π ⁻¹' V ∩ S) := by
   rw [Set.preimage_inter, hpre]
   ext x; simp only [Set.mem_inter_iff, Set.mem_iUnion]
   constructor
   · rintro ⟨hx,g,y,hy,he⟩
     refine ⟨g,y,⟨?_,hy⟩,he⟩
     change π y ∈ V
     have hq : π y = π x := Quotient.sound ⟨g⁻¹, by change g⁻¹ • x = y; simpa only [← he, inv_smul_smul]⟩
     rwa [hq]
   · rintro ⟨g,y,⟨hy,hS⟩,he⟩
     refine ⟨?_,g,y,hS,he⟩
     change π x ∈ V
     have hq : π y = π x := Quotient.sound ⟨g⁻¹, by change g⁻¹ • x = y; simpa only [← he, inv_smul_smul]⟩
     rwa [← hq]
 rw [he]
 have hTinv (h : H) : (h.val : G) • (π ⁻¹' V ∩ S) = π ⁻¹' V ∩ S := by
   rw [Set.smul_set_inter, hinv]
   congr 1
   ext x; constructor
   · rintro ⟨y,hy,he⟩
     change π x ∈ V
     have hq : π y = π x := Quotient.sound ⟨h.val⁻¹, by change h.val⁻¹ • x = y; simpa only [← he, inv_smul_smul]⟩
     rwa [← hq]
   · intro hx
     refine ⟨h.val⁻¹ • x,?_,by simp⟩
     change π (h.val⁻¹ • x) ∈ V
     have hq : π x = π (h.val⁻¹ • x) := Quotient.sound ⟨h.val, by change h.val • (h.val⁻¹ • x) = x; simp⟩
     rwa [← hq]
 rw [local_measure_card μ H D (π ⁻¹' V ∩ S) hD ((hp hV).inter hS) hFD hTinv
   (fun g x hx hg => hsep g x hx.2 hg.2)]
 rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
   (by simp), one_mul]

theorem finite_isotropy_quotient_measure {G X : Type*} [Group G] [Countable G]
 [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X]
 (μ : Measure X) [SMulInvariantMeasure G X μ]
 (H : Subgroup G) [Fintype H] (D S : Set X)
 (hD : MeasurableSet D) (hS : MeasurableSet S)
 (hFD : IsFundamentalDomain G D μ)
 (hinv : ∀ h : H, (h.val : G) • S = S)
 (hsep : ∀ g : G, ∀ x ∈ S, g • x ∈ S → g ∈ H) :
 Measure.map (Quotient.mk (MulAction.orbitRel G X))
   ((Fintype.card H : ℝ≥0∞)⁻¹ • μ.restrict S) =
 (Measure.map (Quotient.mk (MulAction.orbitRel G X)) (μ.restrict D)).restrict
   ((Quotient.mk (MulAction.orbitRel G X)) '' S) := by
  exact local_quotient_card μ H D S hD hS hFD hinv hsep

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

theorem chart_quotient_measure (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : Chart F ζ hζ hF U A) :
    Measure.map (C.toBase F ζ hζ hF U)
      ((Fintype.card (C.G F ζ hζ hF U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball 0 C.radius)).withDensity
          (fun x => ENNReal.ofReal (C.weight x))) =
      (quotientMeasure F ζ hζ hF U A).restrict (C.O F ζ hζ hF U) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := by
    change Countable (Fin 2 → Fin 2 → F); infer_instance
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Function.Injective.countable Units.val_injective
  letI : Countable (KPCuspArithmetic.PGL2 F) :=
    Function.Surjective.countable Matrix.ProjGenLinGroup.mk_surjective
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component)
  let μ := KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)
  let S := C.coordinates '' Metric.ball 0 C.radius
  let j := KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component)
  let π := KPCuspSiegel.projection F Γ
  have hct : Topology.IsOpenEmbedding j := by
    have hj : j = A.components ∘ Sigma.mk C.component := by
      funext x; exact (A.components_formula C.component x).symm
    rw [hj]; exact A.components.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk
  letI : OpensMeasurableSpace (KPCuspSiegel.OrbitQuotient F Γ) := ⟨by
    exact MeasurableSpace.generateFrom_le (fun s hs =>
      measurableSet_quotient.mpr ((hs.preimage (show Continuous π from continuous_quotient_mk')).measurableSet))⟩
  letI : BorelSpace (X F ζ hζ U) := ⟨rfl⟩
  have hjm : Measurable (j : _ → X F ζ hζ U) := hct.continuous.measurable
  have hπm : Measurable π := measurable_quotient_mk''
  have hS : IsOpen S := by
    let f := Set.restrict C.extendedDomain C.coordinates
    have hf : IsOpenEmbedding f := ⟨C.coordinates_embedding, by
      change IsOpen (Set.range (C.extendedDomain.domRestrict C.coordinates))
      rw [Set.range_domRestrict]; exact C.coordinates_open⟩
    have hball : Metric.ball (0 : E C.n) C.radius ⊆ C.extendedDomain :=
      Set.Subset.trans subset_closure C.closed_ball_in_extension
    have hi : S = f '' (Subtype.val ⁻¹' Metric.ball 0 C.radius) := by
      ext z; constructor
      · rintro ⟨x,hx,rfl⟩; exact ⟨⟨x,hball hx⟩,hx,rfl⟩
      · rintro ⟨x,hx,rfl⟩; exact ⟨x.val,hx,rfl⟩
    rw [hi]; exact hf.isOpenMap _ (Metric.isOpen_ball.preimage continuous_subtype_val)
  have hball : Metric.ball (0 : E C.n) C.radius ⊆ C.extendedDomain :=
    Set.Subset.trans subset_closure C.closed_ball_in_extension
  letI : MeasurableConstSMul Γ (KPFiniteCuspAtlas.SymmetricSpace F) :=
    ⟨fun g => (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F g.val).measurable⟩
  letI : ContinuousConstSMul Γ (KPFiniteCuspAtlas.SymmetricSpace F) :=
    ⟨fun g => (KPCuspCharts.projectiveHomeomorph F g.val).continuous⟩
  letI : SMulInvariantMeasure Γ (KPFiniteCuspAtlas.SymmetricSpace F) μ := by
    constructor; intro g s hs
    have hp := KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F g.val
    change (KPArch.hyperbolicVolume _) ((fun z => g.val • z) ⁻¹' s) = _
    rw [← Measure.map_apply hp.measurable hs, hp.map_eq]
  have hSinv (g : C.G F ζ hζ hF U) : (g.val : Γ) • S = S := by
    have hgball (x : E C.n) : C.orthogonal g x ∈ Metric.ball 0 C.radius ↔ x ∈ Metric.ball 0 C.radius := by
      simp only [Metric.mem_ball, dist_zero_right, (C.orthogonal g).norm_map]
    apply Set.Subset.antisymm
    · rintro z ⟨y,⟨x,hx,rfl⟩,he⟩
      exact ⟨C.orthogonal g x, (hgball x).mpr hx, (C.equivariance g x (hball hx)).trans he⟩
    · rintro z ⟨x,hx,rfl⟩
      refine ⟨C.coordinates (C.orthogonal g⁻¹ x), ⟨C.orthogonal g⁻¹ x,?_,rfl⟩,?_⟩
      · simpa only [Metric.mem_ball, dist_zero_right, (C.orthogonal g⁻¹).norm_map] using hx
      · change (g.val.val : KPCuspArithmetic.PGL2 F) • C.coordinates (C.orthogonal g⁻¹ x) = _
        rw [← C.equivariance g _ (hball (by simpa only [Metric.mem_ball, dist_zero_right,
            (C.orthogonal g⁻¹).norm_map] using hx))]
        rw [map_inv]
        change C.coordinates ((C.orthogonal g) ((C.orthogonal g).symm x)) = _
        rw [LinearIsometryEquiv.apply_symm_apply]
  have hsep (g : Γ) (z : KPFiniteCuspAtlas.SymmetricSpace F) (hz : z ∈ S)
     (hg : g • z ∈ S) : g ∈ C.G F ζ hζ hF U := by
    obtain ⟨x,hx,rfl⟩ := hz
    obtain ⟨y,hy,he⟩ := hg
    exact C.separated g x y (hball hx) (hball hy) he.symm
  have hl := local_quotient_card μ (C.G F ζ hζ hF U)
    (A.cuspAtlas C.component).fundamentalDomain S
    (A.cuspAtlas C.component).measurable_fundamentalDomain hS.measurableSet
    (A.cuspAtlas C.component).isFundamentalDomain hSinv hsep
  have hπopen : IsOpen (π '' S) := isOpenMap_quotient_mk'_mul S hS
  have hO : IsOpen (C.O F ζ hζ hF U) := by
    change IsOpen ((j ∘ π ∘ C.coordinates) '' Metric.ball 0 C.radius)
    rw [Set.image_comp, Set.image_comp]; exact hct.isOpenMap _ hπopen
  let ν := (volume.restrict (Metric.ball (0 : E C.n) C.radius)).withDensity
    (fun x => ENNReal.ofReal (C.weight x))
  have hcoord : AEMeasurable C.coordinates ν :=
    (C.smooth_coordinates.continuousOn.mono hball).aemeasurable Metric.isOpen_ball.measurableSet
      |>.mono_ac (withDensity_absolutelyContinuous _ _)
  have hb : C.toBase F ζ hζ hF U = j ∘ π ∘ C.coordinates := rfl
  have hcomp : AEMeasurable (j ∘ π ∘ C.coordinates) ν :=
    ((hjm.comp hπm).aemeasurable).comp_aemeasurable hcoord
  rw [hb, Measure.map_smul _ hcomp]
  rw [← Function.comp_assoc]
  rw [← AEMeasurable.map_map_of_aemeasurable (hjm.comp hπm).aemeasurable hcoord,
    C.coordinate_volume, ← Measure.map_map hjm hπm,
    ← Measure.map_smul _ hjm.aemeasurable,
    ← Measure.map_smul _ hπm.aemeasurable]
  change Measure.map j (Measure.map π ((Fintype.card (C.G F ζ hζ hF U) : ℝ≥0∞)⁻¹ • μ.restrict S)) = _
  change Measure.map π ((Fintype.card (C.G F ζ hζ hF U) : ℝ≥0∞)⁻¹ • μ.restrict S) =
    (KPFiniteCuspAtlas.quotientVolume F Γ (A.cuspAtlas C.component).fundamentalDomain).restrict (π '' S) at hl
  rw [hl]
  have hOeq : C.O F ζ hζ hF U = j '' (π '' S) := by
    change (j ∘ π ∘ C.coordinates) '' Metric.ball 0 C.radius = _
    rw [Set.image_comp, Set.image_comp]
  have hpre : j ⁻¹' C.O F ζ hζ hF U = π '' S := by
    rw [hOeq, Set.preimage_image_eq _ hct.injective]
  have hjall (i : Fin A.componentCount) : Measurable
     (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) : _ → X F ζ hζ U) := by
    apply measurable_from_quotient.mpr
    have hi : KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) =
        A.components ∘ Sigma.mk i := by
      funext x; exact (A.components_formula i x).symm
    rw [hi]
    exact ((A.components.continuous.comp continuous_sigmaMk).comp continuous_quotient_mk').measurable
  ext V hV
  rw [Measure.map_apply hjm hV, Measure.restrict_apply (hjm hV),
    Measure.restrict_apply hV]
  unfold quotientMeasure
  rw [Measure.finsetSum_apply]
  rw [Finset.sum_eq_single C.component]
  · rw [Measure.map_apply hjm (hV.inter hO.measurableSet),
      Set.preimage_inter, hpre]
  · intro i hi hne
    rw [Measure.map_apply (hjall i) (hV.inter hO.measurableSet)]
    have hempty : (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i)) ⁻¹' (V ∩ C.O F ζ hζ hF U) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨y,hy,he⟩ := hx.2
      have h := A.components.injective (a₁ := ⟨C.component,π (C.coordinates y)⟩) (a₂ := ⟨i,x⟩)
        (by rw [A.components_formula, A.components_formula]; exact he)
      exact hne (congrArg Sigma.fst h).symm
    rw [hempty, measure_empty]
  · simp

end DedekindZetaZeroFree.CoreChartLocalizers.CutoffConstruction

end

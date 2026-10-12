module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LocalPGLCoverModules

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPJacquetClosedCellBump

open scoped NumberField NNReal Classical
open NumberField IsDedekindDomain
open KPLocalSmoothRepresentation

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)

variable (hm : KPLocalChartTopology.MatrixChartDepth F w m)

variable {E : Type*} [AddCommGroup E] [Module ℂ E]
  (τB : Representation ℂ (Borel F ζ hζ w) E)

def inducingRepresentation : Representation ℂ (Borel F ζ hζ w) E :=
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  normalizedSectionRepresentation (Borel F ζ hζ w) τB (dB F ζ hζ w)

def inducedRepresentation :
    Representation ℂ (FiniteCover F ζ hζ w) (Induced F ζ hζ w m τB) :=
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  smoothIndRepresentation (Borel F ζ hζ w) τB (dB F ζ hζ w)

def ev1 : Induced F ζ hζ w m τB →ₗ[ℂ] E where
  toFun f := f.val.val 1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

include hm

private theorem projection_continuous :
    letI := finiteCoverTopology F ζ hζ w m
    Continuous (projection F ζ hζ w) := by
  letI := finiteCoverTopology F ζ hζ w m
  have ho : Continuous (ordinaryPGLMap F w) := by
    apply (QuotientGroup.isQuotientMap_mk (KPPGLLocalCover.scalarSubgroup F (Sum.inr w))).continuous_iff.mpr
    change Continuous (Matrix.ProjGenLinGroup.mk (n := Fin 2) (R := KPRankOneInduction.LocalField F w))
    exact (QuotientGroup.isQuotientMap_mk _).continuous
  exact ho.comp (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.2.1.continuous

theorem inducingRepresentation_smooth (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (hτB : letI := finiteCoverTopology F ζ hζ w m; SmoothRepresentation τB) :
    letI := finiteCoverTopology F ζ hζ w m
    SmoothRepresentation (inducingRepresentation F ζ hζ w τB) := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  have hd := KPRankOneInduction.dB_locallyConstant F w (projection F ζ hζ w)
    (projection_continuous F ζ hζ w m hm)
  let D : OpenSubgroup (Borel F ζ hζ w) := ⟨(dB F ζ hζ w).ker, hd.isOpen_fiber 1⟩
  intro e
  obtain ⟨J, hJ⟩ := hτB e
  refine ⟨J ⊓ D, ?_⟩
  intro b hb
  have hbD : dB F ζ hζ w b = 1 := hb.2
  change (((dB F ζ hζ w b : ℝ≥0) : ℝ) : ℂ) • τB b e = e
  rw [hbD, hJ b hb.1]
  simp

theorem ev1_borel (b : Borel F ζ hζ w) (f : Induced F ζ hζ w m τB) :
    ev1 F ζ hζ w m τB
      (inducedRepresentation F ζ hζ w m hm τB b.val f) =
    inducingRepresentation F ζ hζ w τB b (ev1 F ζ hζ w m τB f) := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  change f.val.val (1 * b.val) = inducingRepresentation F ζ hζ w τB b (f.val.val 1)
  simpa [inducingRepresentation] using f.val.property b 1

theorem ev1_smooth_borel (hτB : letI := finiteCoverTopology F ζ hζ w m; SmoothRepresentation τB) :
    letI := finiteCoverTopology F ζ hζ w m
    SmoothRepresentation
      (G := FiniteCover F ζ hζ w) (V := Induced F ζ hζ w m τB)
      (inducedRepresentation F ζ hζ w m hm τB) ∧
    SmoothRepresentation (inducingRepresentation F ζ hζ w τB) := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  exact ⟨smoothIndRepresentation_smooth _ _ _,
    inducingRepresentation_smooth F ζ hζ w m hm τB hm hτB⟩

private theorem exists_compact_open_in (U : Set (FiniteCover F ζ hζ w))
    (hU : letI := finiteCoverTopology F ζ hζ w m; U ∈ nhds 1) :
    letI := finiteCoverTopology F ζ hζ w m
    ∃ L : compactOpenLevel F ζ hζ w m, (L.toOpenSubgroup : Set _) ⊆ U := by
  letI := KPLocalChartTopology.translatedTopology F ζ hζ w m
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPLocalChartTopology.finite_topological_group F ζ hζ w m hm).2.2
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  obtain ⟨s, hs, hi, hp⟩ := KPDeepRawSplitting.raw_section_splitting F ζ hζ w m
    (fun g hg h hh => KPDeepRawSplitting.sigmaTwo_eq_one_on_Gamma F ζ hζ w m hm.2 g h hg hh)
  have heq : (s : _ → KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr w)) =
      KPLocalChartTopology.translatedChart F ζ hζ w m 1 := by
    funext k
    simpa [KPLocalChartTopology.translatedChart] using hs k
  have ho : Topology.IsOpenEmbedding s := heq ▸
    KPLocalChartTopology.translatedChart_isOpenEmbedding F ζ hζ w m hm 1
  let q := KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr w)
  have hq : Continuous q := (QuotientGroup.isQuotientMap_mk _).continuous
  have hpre : (q ∘ s) ⁻¹' U ∈ nhds (1 : KPLocalCube.Gamma F w m) := by
    have ht := (hq.comp ho.continuous).continuousAt (x := (1 : KPLocalCube.Gamma F w m))
    exact ht.preimage_mem_nhds (by simpa using hU)
  rw [nhds_subtype] at hpre
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hpre
  obtain ⟨r, hr, hrV⟩ := (KPLocalCube.Gamma_nhds_basis F w m hm.1).mem_iff.mp hV
  have hsub : KPLocalCube.Gamma F w r ≤ KPLocalCube.Gamma F w m := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨g, ?_, rfl⟩
    apply (KPLocalCube.mem_integerCongruence_iff F w m g).mpr
    intro i j
    exact Ideal.pow_le_pow_right hr ((KPLocalCube.mem_integerCongruence_iff F w r g).mp hg i j)
  let i : KPLocalCube.Gamma F w r →* KPLocalCube.Gamma F w m := Subgroup.inclusion hsub
  let t := s.comp i
  have ht : Continuous t := ho.continuous.comp (continuous_subtype_val.subtype_mk _)
  have htrange : Set.range t = s '' {k : KPLocalCube.Gamma F w m | k.val ∈ KPLocalCube.Gamma F w r} := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨i k, k.property, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k.val, hk⟩, rfl⟩
  have hto : IsOpen (Set.range t) := by
    rw [htrange]
    exact ho.isOpenMap _ ((KPLocalCube.Gamma_compact_open F w r (hm.1.trans hr)).2.preimage continuous_subtype_val)
  let Lgroup := (q.comp t).range
  have hLrange : (Lgroup : Set (FiniteCover F ζ hζ w)) = q '' Set.range t := by
    ext x
    simp [Lgroup, MonoidHom.mem_range, Set.mem_image, Function.comp_def]
  have hLo : IsOpen (Lgroup : Set (FiniteCover F ζ hζ w)) := by
    rw [hLrange]
    exact QuotientGroup.isOpenMap_coe _ hto
  have hLc : IsCompact (Lgroup : Set (FiniteCover F ζ hζ w)) := by
    letI : CompactSpace (KPLocalCube.Gamma F w r) :=
      isCompact_iff_compactSpace.mp (KPLocalCube.Gamma_compact_open F w r (hm.1.trans hr)).1
    exact isCompact_range (hq.comp ht)
  refine ⟨⟨⟨Lgroup, hLo⟩, hLc⟩, ?_⟩
  rintro x ⟨k, rfl⟩
  exact hVU (hrV k.property)

theorem exists_bump_level (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (hτB : letI := finiteCoverTopology F ζ hζ w m; SmoothRepresentation τB) (e : E) :
    letI := finiteCoverTopology F ζ hζ w m
    ∃ L : compactOpenLevel F ζ hζ w m,
      ∀ b : Borel F ζ hζ w, b.val ∈ L.toOpenSubgroup →
        inducingRepresentation F ζ hζ w τB b e = e := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  obtain ⟨J, hJ⟩ := inducingRepresentation_smooth F ζ hζ w m hm τB hm hτB e
  have hJn : (J : Set (Borel F ζ hζ w)) ∈ nhds (1 : Borel F ζ hζ w) := J.mem_nhds_one
  rw [nhds_subtype] at hJn
  obtain ⟨U, hU, hUJ⟩ := Filter.mem_comap.mp hJn
  obtain ⟨L, hLU⟩ := exists_compact_open_in F ζ hζ w m hm U hU
  exact ⟨L, fun b hb => hJ b (hUJ (hLU hb))⟩

def InBorelLevel (L : compactOpenLevel F ζ hζ w m)
    (g : FiniteCover F ζ hζ w) : Prop :=
  letI := finiteCoverTopology F ζ hζ w m
  ∃ b : Borel F ζ hζ w, ∃ l : L.toOpenSubgroup, g = b.val * l.val

def bumpFunction (e : E) (L : compactOpenLevel F ζ hζ w m)
    (g : FiniteCover F ζ hζ w) : E :=
  if hg : InBorelLevel F ζ hζ w m L g then
    inducingRepresentation F ζ hζ w τB (Classical.choose hg) e
  else 0

variable (e : E) (L : compactOpenLevel F ζ hζ w m)
  (hL : letI := finiteCoverTopology F ζ hζ w m; ∀ b : Borel F ζ hζ w, b.val ∈ L.toOpenSubgroup →
    inducingRepresentation F ζ hζ w τB b e = e)

include hL

theorem bump_well_defined (b b' : Borel F ζ hζ w)
    (l l' : letI := finiteCoverTopology F ζ hζ w m; L.toOpenSubgroup) (h : b.val * l.val = b'.val * l'.val) :
    inducingRepresentation F ζ hζ w τB b e =
      inducingRepresentation F ζ hζ w τB b' e := by
  letI := finiteCoverTopology F ζ hζ w m
  let c : Borel F ζ hζ w := b'⁻¹ * b
  have hc : c.val ∈ L.toOpenSubgroup := by
    have heq : c.val = l'.val * l.val⁻¹ := by
      change b'.val⁻¹ * b.val = l'.val * l.val⁻¹
      calc
        _ = b'.val⁻¹ * (b.val * l.val) * l.val⁻¹ := by group
        _ = l'.val * l.val⁻¹ := by rw [h]; group
    rw [heq]
    exact L.toOpenSubgroup.mul_mem l'.property (L.toOpenSubgroup.inv_mem l.property)
  have hb : b = b' * c := by dsimp [c]; group
  rw [hb, map_mul, Module.End.mul_apply, hL c hc]

theorem bumpFunction_on (b : Borel F ζ hζ w) (l : letI := finiteCoverTopology F ζ hζ w m; L.toOpenSubgroup) :
    bumpFunction F ζ hζ w m τB e L (b.val * l.val) =
      inducingRepresentation F ζ hζ w τB b e := by
  letI := finiteCoverTopology F ζ hζ w m
  have hg : InBorelLevel F ζ hζ w m L (b.val * l.val) := ⟨b, l, rfl⟩
  rw [bumpFunction, dif_pos hg]
  obtain ⟨l', hl'⟩ := Classical.choose_spec hg
  exact bump_well_defined F ζ hζ w m hm τB e L hL _ b l' l hl'.symm

theorem bumpFunction_off (g : FiniteCover F ζ hζ w)
    (hg : ¬ InBorelLevel F ζ hζ w m L g) :
    bumpFunction F ζ hζ w m τB e L g = 0 := by
  exact dif_neg hg

theorem bumpFunction_right_fixed (g : FiniteCover F ζ hζ w)
    (l : letI := finiteCoverTopology F ζ hζ w m; L.toOpenSubgroup) :
    bumpFunction F ζ hζ w m τB e L (g * l.val) =
      bumpFunction F ζ hζ w m τB e L g := by
  letI := finiteCoverTopology F ζ hζ w m
  by_cases hg : InBorelLevel F ζ hζ w m L g
  · obtain ⟨b, k, rfl⟩ := hg
    have heq : b.val * k.val * l.val = b.val * (k * l).val := mul_assoc _ _ _
    rw [heq, bumpFunction_on F ζ hζ w m hm τB e L hL,
      bumpFunction_on F ζ hζ w m hm τB e L hL]
  · have hgl : ¬ InBorelLevel F ζ hζ w m L (g * l.val) := by
      rintro ⟨b, k, hk⟩
      apply hg
      refine ⟨b, k * l⁻¹, ?_⟩
      calc
        g = (g * l.val) * l.val⁻¹ := by group
        _ = b.val * (k * l⁻¹).val := by rw [hk]; exact mul_assoc _ _ _
    rw [bumpFunction_off F ζ hζ w m hm τB e L hL _ hgl,
      bumpFunction_off F ζ hζ w m hm τB e L hL _ hg]

theorem bumpFunction_covariance (b : Borel F ζ hζ w)
    (g : FiniteCover F ζ hζ w) :
    bumpFunction F ζ hζ w m τB e L (b.val * g) =
      inducingRepresentation F ζ hζ w τB b
        (bumpFunction F ζ hζ w m τB e L g) := by
  letI := finiteCoverTopology F ζ hζ w m
  by_cases hg : InBorelLevel F ζ hζ w m L g
  · obtain ⟨c, l, rfl⟩ := hg
    have heq : b.val * (c.val * l.val) = (b * c).val * l.val := (mul_assoc _ _ _).symm
    rw [heq, bumpFunction_on F ζ hζ w m hm τB e L hL,
      bumpFunction_on F ζ hζ w m hm τB e L hL,
      map_mul, Module.End.mul_apply]
  · have hbg : ¬ InBorelLevel F ζ hζ w m L (b.val * g) := by
      rintro ⟨c, l, hc⟩
      apply hg
      refine ⟨b⁻¹ * c, l, ?_⟩
      calc
        g = b.val⁻¹ * (b.val * g) := by group
        _ = (b⁻¹ * c).val * l.val := by rw [hc]; exact (mul_assoc _ _ _).symm
    rw [bumpFunction_off F ζ hζ w m hm τB e L hL _ hbg,
      bumpFunction_off F ζ hζ w m hm τB e L hL _ hg, map_zero]

def bumpSection (hm : KPLocalChartTopology.MatrixChartDepth F w m) (e : E) (L : compactOpenLevel F ζ hζ w m)
    (hL : letI := finiteCoverTopology F ζ hζ w m
      ∀ b : Borel F ζ hζ w, b.val ∈ L.toOpenSubgroup →
        inducingRepresentation F ζ hζ w τB b e = e) :
    Induced F ζ hζ w m τB :=
  ⟨⟨bumpFunction F ζ hζ w m τB e L, by
    letI := finiteCoverTopology F ζ hζ w m
    letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
    exact bumpFunction_covariance F ζ hζ w m hm τB e L hL⟩, by
    letI := finiteCoverTopology F ζ hζ w m
    letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
    apply Submodule.subset_span
    refine ⟨L.toOpenSubgroup, ?_⟩
    intro l hl
    apply Subtype.ext
    funext g
    exact bumpFunction_right_fixed F ζ hζ w m hm τB e L hL g ⟨l, hl⟩⟩

theorem ev1_bumpSection :
    ev1 F ζ hζ w m τB (bumpSection F ζ hζ w m τB hm e L hL) = e := by
  letI := finiteCoverTopology F ζ hζ w m
  change bumpFunction F ζ hζ w m τB e L 1 = e
  simpa using bumpFunction_on F ζ hζ w m hm τB e L hL 1 1

omit hL

theorem ev1_surjective (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (hτB : letI := finiteCoverTopology F ζ hζ w m; SmoothRepresentation τB) :
    Function.Surjective (ev1 F ζ hζ w m τB) := by
  intro e
  obtain ⟨L, hL⟩ := exists_bump_level F ζ hζ w m hm τB hm hτB e
  exact ⟨bumpSection F ζ hζ w m τB hm e L hL,
    ev1_bumpSection F ζ hζ w m hm τB e L hL⟩

omit hL hm in

theorem upperRoot_mem_borel (x : Multiplicative (KPRankOneInduction.LocalField F w)) :
    upperRoot F ζ hζ w x ∈ Borel F ζ hζ w := by
  change projection F ζ hζ w (upperRoot F ζ hζ w x) ∈ KPRankOneInduction.upperBorel F w
  have hn : projection F ζ hζ w (upperRoot F ζ hζ w x) =
      KPRankOneInduction.upperRootElement F w (Multiplicative.toAdd x) := by
    change Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n _ _) =
      Matrix.ProjGenLinGroup.mk (KPRankOneInduction.upperRootMatrix F w _)
    rfl
  rw [hn]
  exact KPRankOneInduction.upperRootElement_mem F w _

def torusInBorel (h : Torus F ζ hζ w) : Borel F ζ hζ w :=
  ⟨h.val, by
    letI := finiteCoverTopology F ζ hζ w m
    letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
    exact KPRankOneInduction.coveredTorus_le_Borel F w
      (projection F ζ hζ w) h.property⟩

def rootInBorel (x : Multiplicative (KPRankOneInduction.LocalField F w)) :
    Borel F ζ hζ w :=
  ⟨upperRoot F ζ hζ w x, upperRoot_mem_borel F ζ hζ w x⟩

section TorusInduction

omit hL

variable (q : Borel F ζ hζ w →* Torus F ζ hζ w)
  (τ : Representation ℂ (Torus F ζ hζ w) E)

theorem inflatedRepresentation_smooth
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (hqContinuous : letI := finiteCoverTopology F ζ hζ w m; Continuous q)
    (hτ : letI := finiteCoverTopology F ζ hζ w m; SmoothRepresentation τ) :
    letI := finiteCoverTopology F ζ hζ w m
    SmoothRepresentation (inflatedRepresentation F ζ hζ w q τ) := by
  letI := finiteCoverTopology F ζ hζ w m
  intro e
  obtain ⟨J, hJ⟩ := hτ e
  exact ⟨J.comap q hqContinuous, fun b hb => hJ (q b) hb⟩

theorem ev1_upperRoot
    (hqN : ∀ x, q (rootInBorel F ζ hζ w x) = 1)
    (x : Multiplicative (KPRankOneInduction.LocalField F w))
    (f : PrincipalSeries F ζ hζ w m q τ) :
    ev1 F ζ hζ w m (inflatedRepresentation F ζ hζ w q τ)
      (inducedRepresentation F ζ hζ w m hm
        (inflatedRepresentation F ζ hζ w q τ) (upperRoot F ζ hζ w x) f) =
      ev1 F ζ hζ w m (inflatedRepresentation F ζ hζ w q τ) f := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  have hev := ev1_borel F ζ hζ w m hm (inflatedRepresentation F ζ hζ w q τ)
    (rootInBorel F ζ hζ w x) f
  dsimp only [rootInBorel] at hev
  rw [hev]
  have hn : projection F ζ hζ w (upperRoot F ζ hζ w x) =
      KPRankOneInduction.upperRootElement F w (Multiplicative.toAdd x) := by
    change Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n _ _) =
      Matrix.ProjGenLinGroup.mk (KPRankOneInduction.upperRootMatrix F w _)
    rfl
  have hd := KPRankOneInduction.deltaB_upperRoot F w (projection F ζ hζ w)
    (Multiplicative.toAdd x) (rootInBorel F ζ hζ w x) hn
  change (((dB F ζ hζ w (rootInBorel F ζ hζ w x) : ℝ≥0) : ℝ) : ℂ) •
    τ (q (rootInBorel F ζ hζ w x)) _ = _
  rw [hqN]
  unfold KPLocalSmoothRepresentation.dB KPRankOneInduction.dB
  rw [KPRankOneInduction.halfModulus_eq, hd]
  simp

theorem ev1_torus
    (hqH : ∀ h, q (torusInBorel F ζ hζ w m hm h) = h)
    (h : Torus F ζ hζ w) (f : PrincipalSeries F ζ hζ w m q τ) :
    ev1 F ζ hζ w m (inflatedRepresentation F ζ hζ w q τ)
      (inducedRepresentation F ζ hζ w m hm
        (inflatedRepresentation F ζ hζ w q τ) h.val f) =
      (Real.sqrt ((deltaB F ζ hζ w (torusInBorel F ζ hζ w m hm h) : ℝ≥0) : ℝ) : ℂ) •
        τ h (ev1 F ζ hζ w m (inflatedRepresentation F ζ hζ w q τ) f) := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  have hev := ev1_borel F ζ hζ w m hm (inflatedRepresentation F ζ hζ w q τ)
    (torusInBorel F ζ hζ w m hm h) f
  dsimp only [torusInBorel] at hev
  rw [hev]
  change (((dB F ζ hζ w (torusInBorel F ζ hζ w m hm h) : ℝ≥0) : ℝ) : ℂ) •
      τ (q (torusInBorel F ζ hζ w m hm h)) _ = _
  rw [hqH]
  unfold KPLocalSmoothRepresentation.dB KPRankOneInduction.dB
  rw [KPRankOneInduction.halfModulus_eq]

end TorusInduction

end DedekindZetaZeroFree.KPJacquetClosedCellBump

end

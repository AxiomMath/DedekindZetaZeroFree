module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.LineBundleLocalization

@[expose] public section

noncomputable section
open scoped Classical Pointwise
open MeasureTheory Set
namespace DedekindZetaZeroFree.CoreChartLocalizers

private theorem finite_orbit_compact {G Y : Type*} [Group G] [MulAction G Y]
    [TopologicalSpace Y] [ProperlyDiscontinuousSMul G Y]
    (x : Y) {K : Set Y} (hK : IsCompact K) :
    {y | y ∈ K ∧ ∃ g : G, g • x = y}.Finite := by
  have h := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
    (Γ := G) (K := {x}) (L := K) isCompact_singleton hK
  apply (h.image (fun g : G => g • x)).subset
  rintro y ⟨hy, g, rfl⟩
  exact ⟨g, ⟨g • x, ⟨x, by simp, rfl⟩, hy⟩, rfl⟩

theorem measurable_exact_transversal {G Y : Type*} [Group G] [Countable G]
    [MulAction G Y] [TopologicalSpace Y] [T2Space Y] [SigmaCompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [StandardBorelSpace Y]
    [ContinuousConstSMul G Y] [ProperlyDiscontinuousSMul G Y] :
    ∃ S : Set Y, MeasurableSet S ∧ ∀ x : Y, ∃! y : Y, y ∈ S ∧ ∃ g : G, g • x = y := by
  obtain ⟨e, he⟩ := exists_measurableEmbedding_real Y
  let K := compactCovering Y
  have hK (n) : MeasurableSet (K n) := (isCompact_compactCovering Y n).isClosed.measurableSet
  let P (n : ℕ) (x : Y) := x ∈ K n ∧
    (∀ j < n, ∀ g : G, g • x ∉ K j) ∧
    (∀ g : G, g • x ∈ K n → e x ≤ e (g • x))
  let S := {x | ∃ n, P n x}
  have hP (n) : MeasurableSet {x | P n x} := by
    apply (hK n).inter
    apply MeasurableSet.inter
    · change MeasurableSet {x | ∀ j < n, ∀ g : G, g • x ∉ K j}
      have heq : {x | ∀ j < n, ∀ g : G, g • x ∉ K j} =
          ⋂ j : ℕ, ⋂ (_ : j < n), ⋂ g : G, ((fun x => g • x) ⁻¹' K j)ᶜ := by
        ext x; simp
      rw [heq]
      exact MeasurableSet.iInter fun j : ℕ => MeasurableSet.iInter fun _ : j < n =>
        MeasurableSet.iInter fun g : G => ((hK j).preimage (measurable_const_smul g)).compl
    · change MeasurableSet {x | ∀ g : G, g • x ∈ K n → e x ≤ e (g • x)}
      have heq : {x | ∀ g : G, g • x ∈ K n → e x ≤ e (g • x)} =
          ⋂ g : G, (((fun x => g • x) ⁻¹' K n)ᶜ ∪ {x | e x ≤ e (g • x)}) := by
        ext x; simp [imp_iff_not_or]
      rw [heq]
      exact MeasurableSet.iInter fun g : G =>
        ((hK n).preimage (measurable_const_smul g)).compl.union
          (measurableSet_le he.measurable (he.measurable.comp (measurable_const_smul g)))
  refine ⟨S, by simpa [S, setOf_exists] using MeasurableSet.iUnion hP, ?_⟩
  intro x
  have hx : ∃ n, ∃ g : G, g • x ∈ K n := by
    obtain ⟨n, hn⟩ := mem_iUnion.mp (show x ∈ ⋃ n, K n by rw [iUnion_compactCovering]; trivial)
    exact ⟨n, 1, by simpa using hn⟩
  let n := Nat.find hx
  let T := {y | y ∈ K n ∧ ∃ g : G, g • x = y}
  have hT : T.Finite := finite_orbit_compact x (isCompact_compactCovering Y n)
  have hTne : T.Nonempty := by
    obtain ⟨g, hg⟩ := Nat.find_spec hx
    exact ⟨g • x, hg, g, rfl⟩
  obtain ⟨y, hy, hmin⟩ := Set.exists_min_image T e hT hTne
  have hyP : P n y := by
    refine ⟨hy.1, ?_, ?_⟩
    · intro j hj g hg
      apply Nat.find_min hx hj
      obtain ⟨a, ha⟩ := hy.2
      exact ⟨g * a, by simpa [mul_smul, ha] using hg⟩
    · intro g hg
      apply hmin
      refine ⟨hg, ?_⟩
      obtain ⟨a, ha⟩ := hy.2
      exact ⟨g * a, by simp [mul_smul, ha]⟩
  refine ⟨y, ⟨⟨n, hyP⟩, hy.2⟩, ?_⟩
  rintro z ⟨⟨m, hm⟩, b, hb⟩
  obtain ⟨a, ha⟩ := hy.2
  have hmy : m = n := by
    apply le_antisymm
    · by_contra! h
      apply hm.2.1 n h (a * b⁻¹)
      simpa [mul_smul, ← hb, ← ha] using hy.1
    · exact Nat.find_min' hx ⟨b, hb ▸ hm.1⟩
  subst m
  apply he.injective
  apply le_antisymm
  · have h := hm.2.2 (a * b⁻¹)
    simpa [mul_smul, ← hb, ← ha] using h (by simpa [mul_smul, ← hb, ← ha] using hy.1)
  · have h := hyP.2.2 (b * a⁻¹)
    simpa [mul_smul, ← hb, ← ha] using h (by simpa [mul_smul, ← hb, ← ha] using hm.1)

private theorem selector_of_transversal {G Y : Type*} [Group G] [Countable G]
    [MulAction G Y] [MeasurableSpace Y] [MeasurableConstSMul G Y]
    (S : Set Y) (hS : MeasurableSet S)
    (huniq : ∀ x : Y, ∃! y : Y, y ∈ S ∧ ∃ g : G, g • x = y) :
    ∃ r : Y → Y, Measurable r ∧ (∀ x, r x ∈ S ∧ ∃ g : G, g • x = r x) ∧
      (∀ g : G, ∀ x, r (g • x) = r x) := by
  obtain ⟨r, hr, heq⟩ := exists_measurable_piecewise
    (fun g : G => (fun x => g • x) ⁻¹' S)
    (fun g => hS.preimage (measurable_const_smul g))
    (fun g x => g • x) (fun g => measurable_const_smul g) (by
      intro g h _ x hx
      obtain ⟨y, hy, hu⟩ := huniq x
      exact (hu _ ⟨hx.1, g, rfl⟩).trans (hu _ ⟨hx.2, h, rfl⟩).symm)
  have hs (x) : r x ∈ S ∧ ∃ g : G, g • x = r x := by
    obtain ⟨y, hy, _⟩ := huniq x
    obtain ⟨g, hg⟩ := hy.2
    have hrx := heq g (show x ∈ (fun x => g • x) ⁻¹' S by simpa [hg] using hy.1)
    exact ⟨by rw [hrx]; simpa [hg] using hy.1, g, hrx.symm⟩
  refine ⟨r, hr, hs, ?_⟩
  intro g x
  obtain ⟨a, ha⟩ := (hs (g • x)).2
  obtain ⟨y, hy, hu⟩ := huniq x
  exact (hu _ ⟨(hs (g • x)).1, a * g, by simpa [mul_smul] using ha⟩).trans
    (hu _ (hs x)).symm

private theorem prioritize_domain {G Y : Type*} [Group G] [Countable G]
    [MulAction G Y] [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] [ContinuousConstSMul G Y]
    (S D : Set Y) (hS : MeasurableSet S) (hD : MeasurableSet D)
    (huniq : ∀ x : Y, ∃! y : Y, y ∈ S ∧ ∃ g : G, g • x = y) :
    ∃ T : Set Y, MeasurableSet T ∧
      (∀ x : Y, ∃! y : Y, y ∈ T ∧ ∃ g : G, g • x = y) ∧
      (∀ x, (∃! g : G, g • x ∈ D) → ∀ y ∈ T, (∃ g : G, g • x = y) → y ∈ D) := by
  let C := D ∩ {x | ∀ g : G, g • x ∈ D → g • x = x}
  have hC : MeasurableSet C := by
    have heq : {x | ∀ g : G, g • x ∈ D → g • x = x} =
        ⋂ g : G, (((fun x => g • x) ⁻¹' D)ᶜ ∪ {x | g • x = x}) := by
      ext x; simp [imp_iff_not_or]
    exact hD.inter (heq ▸ (MeasurableSet.iInter fun g =>
      (hD.preimage (measurable_const_smul g)).compl.union
        (isClosed_eq (continuous_const_smul g) continuous_id).measurableSet))
  let B := ⋃ g : G, (fun x => g • x) ⁻¹' C
  have hB : MeasurableSet B := MeasurableSet.iUnion fun g =>
    hC.preimage (measurable_const_smul g)
  have hBi (g : G) (x : Y) : g • x ∈ B ↔ x ∈ B := by
    simp only [B, mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨a, ha⟩; exact ⟨a * g, by simpa [mul_smul] using ha⟩
    · rintro ⟨a, ha⟩; exact ⟨a * g⁻¹, by simpa [mul_smul] using ha⟩
  have hCu (x y : Y) (hx : x ∈ C) (hy : y ∈ C)
      (h : ∃ g : G, g • x = y) : y = x := by
    obtain ⟨g, rfl⟩ := h
    exact hx.2 g hy.1
  let T := C ∪ (S \ B)
  have hTu (x y : Y) (hx : x ∈ T) (hy : y ∈ T)
      (h : ∃ g : G, g • x = y) : y = x := by
    obtain ⟨g, rfl⟩ := h
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hCu _ _ hx hy ⟨g, rfl⟩
    · exact False.elim (hy.2 ((hBi g x).mpr (mem_iUnion.mpr ⟨1, by simpa using hx⟩)))
    · exact False.elim (hx.2 (mem_iUnion.mpr ⟨g, hy⟩))
    · obtain ⟨z, hz, hu⟩ := huniq x
      exact (hu _ ⟨hy.1, g, rfl⟩).trans (hu _ ⟨hx.1, 1, one_smul _ _⟩).symm
  refine ⟨T, hC.union (hS.diff hB), ?_, ?_⟩
  · intro x
    have hex : ∃ y ∈ T, ∃ g : G, g • x = y := by
      by_cases hx : x ∈ B
      · obtain ⟨g, hg⟩ := mem_iUnion.mp hx
        exact ⟨g • x, Or.inl hg, g, rfl⟩
      · obtain ⟨y, hy, _⟩ := huniq x
        obtain ⟨g, hg⟩ := hy.2
        refine ⟨y, Or.inr ⟨hy.1, ?_⟩, g, hg⟩
        simpa [← hg, hBi] using hx
    obtain ⟨y, hy, a, ha⟩ := hex
    refine ⟨y, ⟨hy, a, ha⟩, ?_⟩
    rintro z ⟨hz, b, hb⟩
    apply hTu y z hy hz
    exact ⟨b * a⁻¹, by simp [← ha, ← hb, mul_smul]⟩
  · intro x hx y hy hxy
    obtain ⟨a, ha, hu⟩ := hx
    have hac : a • x ∈ C := by
      refine ⟨ha, ?_⟩
      intro g hg
      have he : g * a = a := hu _ (by simpa [mul_smul] using hg)
      simpa [← mul_smul, he]
    have hb : x ∈ B := mem_iUnion.mpr ⟨a, hac⟩
    obtain ⟨b, rfl⟩ := hxy
    rcases hy with hy | hy
    · exact hy.1
    · exact False.elim (hy.2 ((hBi b x).mpr hb))

theorem measurable_fundamental_domain_choice {G Y : Type*} [Group G] [Countable G]
    [MulAction G Y] [TopologicalSpace Y] [T2Space Y] [SigmaCompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [StandardBorelSpace Y]
    [ContinuousConstSMul G Y] [ProperlyDiscontinuousSMul G Y]
    (μ : Measure Y) [SMulInvariantMeasure G Y μ]
    (D : Set Y) (hD : MeasurableSet D) (hFD : IsFundamentalDomain G D μ) :
    ∃ r : Y → Y, Measurable r ∧
      (∀ x, ∃ g : G, g • x = r x) ∧
      (∀ g : G, ∀ x, r (g • x) = r x) ∧
      (∀ᵐ x ∂μ, r x ∈ D) ∧
      (∀ᵐ x ∂μ, ∀ g : G, g • r x = r x → g = 1) := by
  obtain ⟨S, hS, huniq⟩ := measurable_exact_transversal (G := G) (Y := Y)
  obtain ⟨T, hT, hTu, hTD⟩ := prioritize_domain S D hS hD huniq
  obtain ⟨r, hr, hs, hinv⟩ := selector_of_transversal T hT hTu
  refine ⟨r, hr, fun x => (hs x).2, hinv, ?_, ?_⟩
  · filter_upwards [KPFiniteAdelicCuspEnds.fd_ae_unique μ D hFD] with x hx
    exact hTD x hx (r x) (hs x).1 (hs x).2
  · filter_upwards [KPFiniteAdelicCuspEnds.fd_ae_free μ D hFD] with x hx
    intro g hg
    obtain ⟨a, ha⟩ := (hs x).2
    have he : (a⁻¹ * g * a) • x = x := by
      simpa only [mul_smul, ha, hg] using inv_smul_smul a x
    have h := hx _ he
    have := congrArg (fun b : G => a * b * a⁻¹) h
    simpa [mul_assoc] using this

theorem component_measurable_section (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
    (g : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (D : Set (KPFiniteCuspAtlas.SymmetricSpace F)) (hD : MeasurableSet D)
    (hFD : IsFundamentalDomain (KPCuspGenuineMonodromy.Component F ζ hζ U g) D
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))) :
    ∃ s : KPCuspSiegel.OrbitQuotient F (KPCuspGenuineMonodromy.Component F ζ hζ U g) →
        KPFiniteCuspAtlas.SymmetricSpace F,
      Measurable s ∧
      (∀ q, KPCuspSiegel.projection F _ (s q) = q) ∧
      (∀ᵐ q ∂KPFiniteCuspAtlas.quotientVolume F _ D, s q ∈ D) ∧
      (∀ᵐ q ∂KPFiniteCuspAtlas.quotientVolume F _ D,
        ∀ γ : KPCuspGenuineMonodromy.Component F ζ hζ U g,
          γ • s q = s q → γ = 1) := by
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U g
  let μ := KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)
  letI : Countable Γ := KPFiniteAdelicCuspEnds.arithmeticStabilizer_countable F _ _
  letI : ContinuousConstSMul Γ (KPFiniteCuspAtlas.SymmetricSpace F) :=
    KPFiniteAdelicCuspEnds.arithmeticStabilizer_continuousConstSMul F _ _
  letI : ProperlyDiscontinuousSMul Γ (KPFiniteCuspAtlas.SymmetricSpace F) :=
    KPFiniteAdelicCuspEnds.FundamentalDomainGeometry.arithmeticStabilizer_properlyDiscontinuous_of_compact
      F hF _ (KPCuspGenuineMonodromy.finiteBase_level_compact F ζ hζ U) _
  letI : SMulInvariantMeasure Γ (KPFiniteCuspAtlas.SymmetricSpace F) μ :=
    ⟨fun γ _ hs => (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F γ.val).measure_preimage hs.nullMeasurableSet⟩
  obtain ⟨r, hr, horbit, hinv, hmem, hfree⟩ := measurable_fundamental_domain_choice μ D hD hFD
  let s : KPCuspSiegel.OrbitQuotient F Γ → KPFiniteCuspAtlas.SymmetricSpace F :=
    Quotient.lift r (by
      intro x y h
      obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
      simpa [← hγ] using (hinv γ y))
  have hsq (x) : s (KPCuspSiegel.projection F Γ x) = r x := rfl
  have hsm : Measurable s := measurable_from_quotient.mpr hr
  refine ⟨s, hsm, ?_, ?_, ?_⟩
  · intro q
    induction q using Quotient.inductionOn with
    | h x =>
      obtain ⟨γ, hγ⟩ := horbit x
      apply Quotient.sound
      apply MulAction.orbitRel_apply.mpr
      exact MulAction.mem_orbit_iff.mpr ⟨γ, hγ⟩
  · apply (ae_map_iff (show AEMeasurable (KPCuspSiegel.projection F Γ) (μ.restrict D) from
        measurable_quotient_mk''.aemeasurable) (hD.preimage hsm)).mpr
    exact (ae_restrict_of_ae hmem)
  · have hp : MeasurableSet {q | ∀ γ : Γ, γ • s q = s q → γ = 1} := by
      have heq : {q | ∀ γ : Γ, γ • s q = s q → γ = 1} =
          ⋂ γ : Γ, ((s ⁻¹' {y | γ • y = y})ᶜ ∪ {q | γ = 1}) := by
        ext q; simp [imp_iff_not_or]
      rw [heq]
      exact MeasurableSet.iInter fun γ : Γ =>
        ((isClosed_eq (continuous_const_smul γ) continuous_id).measurableSet.preimage hsm).compl.union
          (MeasurableSet.const (γ = 1))
    apply (ae_map_iff (show AEMeasurable (KPCuspSiegel.projection F Γ) (μ.restrict D) from
        measurable_quotient_mk''.aemeasurable) hp).mpr
    exact ae_restrict_of_ae hfree

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

theorem full_base_measurable_section (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) :
    ∃ (c : X F ζ hζ U → Fin A.componentCount) (l : X F ζ hζ U → KPFiniteCuspAtlas.SymmetricSpace F),
      Measurable c ∧ Measurable l ∧
      (∀ x, KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative (c x))
        (KPCuspSiegel.projection F _ (l x)) = x) ∧
      (∀ᵐ x ∂quotientMeasure F ζ hζ hF U A, l x ∈ (A.cuspAtlas (c x)).fundamentalDomain) ∧
      (∀ᵐ x ∂quotientMeasure F ζ hζ hF U A, ∀ γ : KPCuspGenuineMonodromy.Component F ζ hζ U
        (A.representative (c x)), γ • l x = l x → γ = 1) := by
  letI : BorelSpace (X F ζ hζ U) := ⟨rfl⟩
  letI (i : Fin A.componentCount) : ContinuousConstSMul
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i)) (KPFiniteCuspAtlas.SymmetricSpace F) :=
    KPFiniteAdelicCuspEnds.arithmeticStabilizer_continuousConstSMul F _ _
  letI (i : Fin A.componentCount) : ProperlyDiscontinuousSMul
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i)) (KPFiniteCuspAtlas.SymmetricSpace F) :=
    KPFiniteAdelicCuspEnds.FundamentalDomainGeometry.arithmeticStabilizer_properlyDiscontinuous_of_compact
      F hF _ (KPCuspGenuineMonodromy.finiteBase_level_compact F ζ hζ U) _
  letI (i : Fin A.componentCount) : SecondCountableTopology (KPCuspSiegel.OrbitQuotient F
    (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))) :=
    ContinuousConstSMul.secondCountableTopology
  choose s hm hs hd hf using fun i : Fin A.componentCount =>
    component_measurable_section F ζ hζ hF U (A.representative i)
      (A.cuspAtlas i).fundamentalDomain (A.cuspAtlas i).measurable_fundamentalDomain
      (A.cuspAtlas i).isFundamentalDomain
  let c := fun x => (A.components.symm x).1
  let l := fun x => s (c x) (A.components.symm x).2
  letI : MeasurableSpace (Σ i : Fin A.componentCount, KPCuspSiegel.OrbitQuotient F
    (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))) := borel _
  letI : BorelSpace (Σ i : Fin A.componentCount, KPCuspSiegel.OrbitQuotient F
    (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))) := ⟨rfl⟩
  have hcm : Measurable c := ((continuous_sigma_iff.mpr (fun _ => continuous_const)).comp
    A.components.symm.continuous).measurable
  have hsm : Measurable (fun p : Σ i : Fin A.componentCount, KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i)) => s p.1 p.2) := by
    intro t ht
    have he : (fun p : Σ i : Fin A.componentCount, KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i)) => s p.1 p.2) ⁻¹' t =
        ⋃ i, Sigma.mk i '' ((s i) ⁻¹' t) := by
      ext ⟨i,q⟩
      constructor
      · intro h; exact mem_iUnion.mpr ⟨i, q, h, rfl⟩
      · intro h
        obtain ⟨j, z, hz, he⟩ := mem_iUnion.mp h
        cases he
        exact hz
    rw [he]
    exact MeasurableSet.iUnion fun i => Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding.measurableSet_image.mpr (hm i ht)
  have hlm : Measurable l := hsm.comp A.components.symm.continuous.measurable
  have hc (i) (q) : c (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) q) = i := by
    simp [c, ← A.components_formula]
  have hl (i) (q) : l (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) q) = s i q := by
    change s (A.components.symm (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) q)).1
      (A.components.symm (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) q)).2 = _
    rw [← A.components_formula, A.components.symm_apply_apply]
  refine ⟨c, l, hcm, hlm, ?_, ?_, ?_⟩
  · intro x
    rw [hs]
    exact (A.components_formula _ _).symm.trans (A.components.apply_symm_apply x)
  · unfold quotientMeasure
    apply ae_finsetSum_measure_iff.mpr
    intro i hi
    have hme : MeasurableEmbedding (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i)) := by
      have h := A.components.measurableEmbedding.comp
        ((Topology.IsOpenEmbedding.sigmaMk (i := i)).measurableEmbedding)
      simpa only [Function.comp_def, A.components_formula] using h
    apply hme.ae_map_iff.mpr
    filter_upwards [hd i] with q hq
    rw [hl, hc]
    exact hq
  · unfold quotientMeasure
    apply ae_finsetSum_measure_iff.mpr
    intro i hi
    have hme : MeasurableEmbedding (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i)) := by
      have h := A.components.measurableEmbedding.comp
        ((Topology.IsOpenEmbedding.sigmaMk (i := i)).measurableEmbedding)
      simpa only [Function.comp_def, A.components_formula] using h
    apply hme.ae_map_iff.mpr
    filter_upwards [hf i] with q hq
    rw [hl, hc]
    exact hq

theorem quotient_line_frame_injective (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (i : Fin A.componentCount) (z : KPFiniteCuspAtlas.SymmetricSpace F)
    (hz : ∀ γ : KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i),
      γ • z = z → γ = 1) :
    Function.Injective (fun a : V F ζ hζ U => (⟨i, Quotient.mk _ (z, a)⟩ : Line F ζ hζ hF U A)) := by
  intro a b h
  have he : (Quotient.mk _ (z,a) : KPCuspGenuineMonodromy.OrbifoldLine F ζ hζ U (A.representative i) (A.line i).rho) = Quotient.mk _ (z,b) := by
    exact eq_of_heq (Sigma.mk.inj h).2
  obtain ⟨γ, hg, ha⟩ := Quotient.exact he
  have hγ := hz γ hg.symm
  subst γ
  apply Subtype.ext
  simpa using ha.symm

theorem quotient_line_frame_surjective (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (i : Fin A.componentCount) (z : KPFiniteCuspAtlas.SymmetricSpace F)
    (l : Line F ζ hζ hF U A)
    (hl : lineBase F ζ hζ hF U A l = KPFiniteCuspAtlas.componentMap F ζ hζ U
      (A.representative i) (KPCuspSiegel.projection F _ z)) :
    ∃ a : V F ζ hζ U, (⟨i, Quotient.mk _ (z,a)⟩ : Line F ζ hζ hF U A) = l := by
  rcases l with ⟨j,l⟩
  induction l using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨w,b⟩
    change KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j)
      (KPCuspSiegel.projection F _ w) = _ at hl
    rw [← A.components_formula, ← A.components_formula] at hl
    have he := A.components.injective hl
    have hij := (Sigma.mk.inj he).1
    subst j
    have hq := eq_of_heq (Sigma.mk.inj he).2
    obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact hq))
    let a : V F ζ hζ U := (KPCuspGenuineMonodromy.chi F ζ hζ ((A.line i).rho γ)⁻¹ : ℂ) • b
    refine ⟨a, ?_⟩
    apply congrArg (Sigma.mk i)
    apply Quotient.sound
    refine ⟨γ, hγ.symm, ?_⟩
    change (b : ℂ) = _ * (_ * (b : ℂ))
    rw [← mul_assoc, ← Units.val_mul]
    simp

theorem component_quotientVolume_locallyFinite (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) (g : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (D : Set (KPFiniteCuspAtlas.SymmetricSpace F)) (hD : MeasurableSet D)
    (hFD : IsFundamentalDomain (KPCuspGenuineMonodromy.Component F ζ hζ U g) D
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))) :
    IsLocallyFiniteMeasure (KPFiniteCuspAtlas.quotientVolume F
      (KPCuspGenuineMonodromy.Component F ζ hζ U g) D) := by
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U g
  let μ := KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)
  let π := KPCuspSiegel.projection F Γ
  letI : Countable Γ := KPFiniteAdelicCuspEnds.arithmeticStabilizer_countable F _ _
  letI : ContinuousConstSMul Γ (KPFiniteCuspAtlas.SymmetricSpace F) :=
    KPFiniteAdelicCuspEnds.arithmeticStabilizer_continuousConstSMul F _ _
  letI : ProperlyDiscontinuousSMul Γ (KPFiniteCuspAtlas.SymmetricSpace F) :=
    KPFiniteAdelicCuspEnds.FundamentalDomainGeometry.arithmeticStabilizer_properlyDiscontinuous_of_compact
      F hF _ (KPCuspGenuineMonodromy.finiteBase_level_compact F ζ hζ U) _
  letI : SecondCountableTopology (KPCuspSiegel.OrbitQuotient F Γ) :=
    ContinuousConstSMul.secondCountableTopology
  letI : IsLocallyFiniteMeasure μ := IsLocallyFiniteMeasure.withDensity_ofReal (by
    unfold KPArch.volumeDensity KPArch.height
    simp_rw [← Real.exp_neg]
    fun_prop)
  letI : SMulInvariantMeasure Γ (KPFiniteCuspAtlas.SymmetricSpace F) μ :=
    ⟨fun γ _ hs => (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F γ.val).measure_preimage hs.nullMeasurableSet⟩
  refine ⟨?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨K,hK,hKnh⟩ := exists_compact_mem_nhds x
    have hπ : Continuous π := continuous_quotient_mk'
    have hKm : MeasurableSet (π '' K) := (hK.image hπ).isClosed.measurableSet
    refine ⟨π '' K, ?_, ?_⟩
    · rw [← (MulAction.isOpenQuotientMap_quotientMk (Γ := Γ)).map_nhds_eq x]
      exact Filter.mem_map.mpr (Filter.mem_of_superset hKnh (subset_preimage_image _ _))
    · change Measure.map π (μ.restrict D) (π '' K) < ⊤
      rw [Measure.map_apply hπ.measurable hKm, Measure.restrict_apply' hD]
      have he : π ⁻¹' (π '' K) = ⋃ γ : Γ, γ • K :=
        MulAction.quotient_preimage_image_eq_union_mul K
      rw [he, iUnion_inter]
      apply lt_of_le_of_lt (measure_iUnion_le _)
      rw [← hFD.measure_eq_tsum K]
      exact hK.measure_lt_top

theorem quotientMeasure_finiteOnCompacts (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) :
    IsFiniteMeasureOnCompacts (quotientMeasure F ζ hζ hF U A) := by
  letI : BorelSpace (X F ζ hζ U) := ⟨rfl⟩
  letI (i : Fin A.componentCount) : ContinuousConstSMul
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i)) (KPFiniteCuspAtlas.SymmetricSpace F) :=
    KPFiniteAdelicCuspEnds.arithmeticStabilizer_continuousConstSMul F _ _
  letI (i : Fin A.componentCount) : ProperlyDiscontinuousSMul
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i)) (KPFiniteCuspAtlas.SymmetricSpace F) :=
    KPFiniteAdelicCuspEnds.FundamentalDomainGeometry.arithmeticStabilizer_properlyDiscontinuous_of_compact
      F hF _ (KPCuspGenuineMonodromy.finiteBase_level_compact F ζ hζ U) _
  letI (i : Fin A.componentCount) : SecondCountableTopology (KPCuspSiegel.OrbitQuotient F
    (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))) :=
    ContinuousConstSMul.secondCountableTopology
  letI (i : Fin A.componentCount) : IsLocallyFiniteMeasure (KPFiniteCuspAtlas.quotientVolume F
    (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i)) (A.cuspAtlas i).fundamentalDomain) :=
    component_quotientVolume_locallyFinite F ζ hζ U hF _ _ (A.cuspAtlas i).measurable_fundamentalDomain (A.cuspAtlas i).isFundamentalDomain
  letI : MeasurableSpace (Σ i : Fin A.componentCount, KPCuspSiegel.OrbitQuotient F
    (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))) := borel _
  letI : BorelSpace (Σ i : Fin A.componentCount, KPCuspSiegel.OrbitQuotient F
    (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))) := ⟨rfl⟩
  letI : T2Space (X F ζ hζ U) := A.components.symm.isEmbedding.t2Space
  refine ⟨fun K hK => ?_⟩
  unfold quotientMeasure
  rw [Measure.finset_sum_apply]
  apply ENNReal.sum_lt_top.mpr
  intro i hi
  have he : Topology.IsClosedEmbedding (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i)) := by
    have he := A.components.isClosedEmbedding.comp (Topology.IsClosedEmbedding.sigmaMk (i := i))
    simpa only [Function.comp_def, A.components_formula] using he
  rw [Measure.map_apply he.continuous.measurable hK.isClosed.measurableSet]
  exact (he.isCompact_preimage hK).measure_lt_top

theorem smooth_section_norm_continuous (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (c : X F ζ hζ U → Fin A.componentCount)
    (l : X F ζ hζ U → KPFiniteCuspAtlas.SymmetricSpace F)
    (hc : Measurable c) (hl : Measurable l)
    (hbase : ∀ x, KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative (c x))
      (KPCuspSiegel.projection F _ (l x)) = x)
    (s : KPFiniteCuspAtlas.genuineScalars F ζ hζ U)
    (hs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z => s.val (z, A.representative i))) :
    Continuous (fun x => ‖s.val (l x, A.representative (c x))‖) := by
  let n (i : Fin A.componentCount) : KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i)) → ℝ :=
    Quotient.lift (fun z => ‖s.val (z,A.representative i)‖) (by
      intro z w h
      obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
      rw [← hγ, ← A.scalar_realization_formula]
      change ‖(A.scalar_realization s i).val ((γ : KPCuspArithmetic.PGL2 F) • w)‖ = _
      rw [(A.scalar_realization s i).property.2, norm_mul, (A.line i).unitary, one_mul]
      rw [A.scalar_realization_formula])
  have hn (i) : Continuous (n i) := (hs i).continuous.norm.quotient_lift _
  have he (x) : A.components.symm x = ⟨c x, KPCuspSiegel.projection F _ (l x)⟩ := by
    apply A.components.injective
    rw [A.components.apply_symm_apply, A.components_formula, hbase]
  have hcon : Continuous (fun x => n (A.components.symm x).1 (A.components.symm x).2) :=
    ((continuous_sigma_iff (f := fun p : Σ i : Fin A.componentCount, KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i)) => n p.1 p.2)).mpr hn).comp A.components.symm.continuous
  convert hcon using 1
  ext x
  rw [he]
  rfl

theorem measurable_realization (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) :
    Nonempty (Realization F ζ hζ hF U A) := by
  letI : BorelSpace (X F ζ hζ U) := ⟨rfl⟩
  obtain ⟨c,l,hc,hl,hbase,hdom,hfree⟩ := full_base_measurable_section F ζ hζ hF U A
  let R : KPFiniteCuspAtlas.genuineScalars F ζ hζ U →ₗ[ℂ] (X F ζ hζ U → V F ζ hζ U) :=
    { toFun := fun s x => ⟨s.val (l x,A.representative (c x)), by
        rw [← A.scalar_realization_formula]
        exact (A.scalar_realization s (c x)).property.1 (l x)⟩
      map_add' := by intro s t; ext x; rfl
      map_smul' := by intro a s; ext x; rfl }
  let frame := fun x (a : V F ζ hζ U) => (⟨c x, Quotient.mk _ (l x,a)⟩ : Line F ζ hζ hF U A)
  refine ⟨{
    component := c
    lift := l
    measurable_component := hc
    measurable_lift := hl
    lift_formula := hbase
    lift_in_domain := hdom
    free_ae := hfree
    representative := R
    section_formula := fun _ _ => rfl
    frame := frame
    frame_formula := fun _ _ => rfl
    frame_base := fun x a => hbase x
    frame_injective_ae := ?_
    frame_surjective_ae := ?_
    smooth_test_memLp := ?_ }⟩
  · filter_upwards [hfree] with x hx
    exact quotient_line_frame_injective F ζ hζ hF U A (c x) (l x) hx
  · exact Filter.Eventually.of_forall fun x b hb =>
      quotient_line_frame_surjective F ζ hζ hF U A (c x) (l x) b (hb.trans (hbase x).symm)
  · intro s hs hcompact
    letI : IsFiniteMeasureOnCompacts (quotientMeasure F ζ hζ hF U A) :=
      quotientMeasure_finiteOnCompacts F ζ hζ hF U A
    have hnm : Continuous (fun x => ‖R s x‖) :=
      smooth_section_norm_continuous F ζ hζ hF U A c l hc hl hbase s hs
    have hrm : Measurable (R s) := by
      apply Measurable.subtype_mk
      have hg : Measurable (fun p : KPFiniteCuspAtlas.SymmetricSpace F × Fin A.componentCount =>
        s.val (p.1, A.representative p.2)) :=
        measurable_from_prod_countable_left (fun i => (hs i).continuous.measurable)
      exact hg.comp (hl.prodMk hc)
    have hncompact : HasCompactSupport (fun x => ‖R s x‖) := by
      have he : tsupport (fun x => ‖R s x‖) = tsupport (R s) := by
        unfold tsupport
        congr 1
        ext x
        simp [Function.mem_support]
      rw [HasCompactSupport, he]
      exact hcompact
    have hnp : MemLp (fun x => ‖R s x‖) 2 (quotientMeasure F ζ hζ hF U A) :=
      hnm.memLp_of_hasCompactSupport hncompact
    exact (memLp_norm_iff hrm.aestronglyMeasurable).mp hnp

end DedekindZetaZeroFree.CoreChartLocalizers

end

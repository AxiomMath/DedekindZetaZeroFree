module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.EmbeddedEndVolume
public import DedekindZetaZeroFree.Adeles.Quotients.HyperbolicComponents.MeasurableFundamentalDomains
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.DisjointHighEnds
public import DedekindZetaZeroFree.Metaplectic.Cubic.Cusps.BoundedShapeFrequencyGap

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory

namespace DedekindZetaZeroFree.KPFiniteAdelicCuspEnds

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

structure ComponentEndData
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : CompactOpenLevel (KPCuspGenuineMonodromy.FiniteCover F ζ hζ)) (g : KPCuspGenuineMonodromy.FiniteCover F ζ hζ)
    (line : KPCuspGenuineMonodromy.LineOutput F ζ hζ U g)
    (ends : ∀ Γ : Subgroup (KPCuspArithmetic.PGL2 F),
      KPCuspArithmetic.PGL2 F → ℝ → Set (KPCuspSiegel.OrbitQuotient F Γ))
    (transport : ∀ (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
      (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F) (T : ℝ),
      KPCuspCharts.HighQuotient F (KPCuspArithmetic.conjugatedStabilizer F Γ q σ) T →
        KPCuspSiegel.OrbitQuotient F Γ)
    (volume : ∀ Γ : Subgroup (KPCuspArithmetic.PGL2 F),
      Set (KPCuspGenuineMonodromy.SymmetricSpace F) →
        Measure (KPCuspSiegel.OrbitQuotient F Γ)) where
  cuspCount : ℕ
  positive_cuspCount : 0 < cuspCount
  cusp : Fin cuspCount → KPCuspArithmetic.Cusp F
  representative : Fin cuspCount → KPCuspArithmetic.PGL2 F
  representative_formula : ∀ a, representative a • KPCuspArithmetic.infinity F = cusp a
  exhaustive : ∀ q : KPCuspArithmetic.Cusp F,
    ∃ (a : Fin cuspCount) (γ : KPCuspGenuineMonodromy.Component F ζ hζ U g),
      γ • cusp a = q
  inequivalent : ∀ (a b : Fin cuspCount), a ≠ b →
    ∀ γ : KPCuspGenuineMonodromy.Component F ζ hζ U g, γ • cusp a ≠ cusp b
  threshold : ℝ
  parabolic : ∀ a, KPCuspCharts.ParabolicData F
    (KPCuspArithmetic.conjugatedStabilizer F
      (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a))
  geometry : ∀ a, KPCuspCharts.ChartOutput F hF _ (parabolic a)
  monodromy : ∀ a, KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ)
    _ (parabolic a)
    (line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
      (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a)))
    (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)
  frequencies : ∀ a, KPCuspFrequencyGap.CuspOutput (ζ := ζ) (hζ := hζ)
    _ (parabolic a)
    (line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
      (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a)))
    (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U) (monodromy a)
  boundedShapes : Fin cuspCount → Set (KPCuspCharts.Shape F)
  compact_boundedShapes : ∀ a, IsCompact (boundedShapes a)
  shapes_cover : ∀ a (b : KPCuspCharts.Shape F), ∃ b' ∈ boundedShapes a,
    (QuotientAddGroup.mk b : KPCuspCharts.Base F hF
      (parabolic a).E (parabolic a).integralUnits) = QuotientAddGroup.mk b'

  frequencyGap : ℝ
  positive_frequencyGap : 0 < frequencyGap
  shortest_frequency : ∀ a (b : KPCuspCharts.Shape F), b ∈ boundedShapes a →
    ∀ ξ : KPCuspFrequencyGap.Frequency _ (parabolic a)
      (line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
        (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a))),
    (ξ : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F)) ≠ 0 →
      frequencyGap ≤ KPCuspFrequencyGap.shapeEnergy b ξ

  constant_rank : ∀ a, Module.finrank ℂ
    (KPCuspFrequencyGap.constantSections (ζ := ζ) (hζ := hζ) _ (parabolic a)
      (line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
        (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a)))
      (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)) ≤ 1
  constant_finite : ∀ a, FiniteDimensional ℂ
    (KPCuspFrequencyGap.constantSections (ζ := ζ) (hζ := hζ) _ (parabolic a)
      (line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
        (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a)))
      (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U))
  open_ends : ∀ a, IsOpen (ends
    (KPCuspGenuineMonodromy.Component F ζ hζ U g) (representative a) threshold)
  disjoint_ends : Pairwise fun a b : Fin cuspCount => Disjoint
    (ends (KPCuspGenuineMonodromy.Component F ζ hζ U g) (representative a) threshold)
    (ends (KPCuspGenuineMonodromy.Component F ζ hζ U g) (representative b) threshold)
  compact_core : IsCompact ((Set.univ :
    Set (KPCuspSiegel.OrbitQuotient F (KPCuspGenuineMonodromy.Component F ζ hζ U g))) \
      (⋃ a, ends (KPCuspGenuineMonodromy.Component F ζ hζ U g)
        (representative a) threshold))
  end_embedding : ∀ a, Topology.IsEmbedding (transport
    (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a) threshold)
  end_range : ∀ a, Set.range (transport
    (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a) threshold) =
      ends (KPCuspGenuineMonodromy.Component F ζ hζ U g) (representative a) threshold
  fundamentalDomain : Set (KPCuspGenuineMonodromy.SymmetricSpace F)
  measurable_fundamentalDomain : MeasurableSet fundamentalDomain
  isFundamentalDomain : IsFundamentalDomain
    (KPCuspGenuineMonodromy.Component F ζ hζ U g) fundamentalDomain
    (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))

  end_volume : ∀ a,
    Measure.map (transport (KPCuspGenuineMonodromy.Component F ζ hζ U g)
      (cusp a) (representative a) threshold)
      (Measure.map ((geometry a).highPresentation threshold)
        ((geometry a).sectionMeasure.prod
          (Measure.comap (Subtype.val : Set.Ioi threshold → ℝ)
            (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))))) =
    (volume (KPCuspGenuineMonodromy.Component F ζ hζ U g)
      fundamentalDomain).restrict
      (ends (KPCuspGenuineMonodromy.Component F ζ hζ U g) (representative a) threshold)

theorem component_transport_range
    (hd : 0 < KPCuspLogShape.dimension F)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (T : ℝ)
    (f : KPCuspCharts.HighQuotient F
      (KPCuspArithmetic.conjugatedStabilizer F Γ q σ) T →
        KPCuspSiegel.OrbitQuotient F Γ)
    (hf : ∀ (p : {p : KPCuspCharts.Coordinates F // T < p.2}),
      f (Quotient.mk _ p) =
        KPCuspSiegel.projection F Γ (σ • KPCuspCharts.toArch F p.val)) :
    Set.range f = KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F σ T := by
  let e := KPCuspCharts.highCoordinatesHomeomorph F hd σ T
  apply Set.ext
  intro y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective x
    rw [hf]
    exact ⟨(e p).val, (e p).property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    let p := e.symm ⟨z, hz⟩
    refine ⟨Quotient.mk _ p, ?_⟩
    rw [hf]
    exact congrArg (KPCuspSiegel.projection F Γ)
      (congrArg Subtype.val (e.apply_symm_apply ⟨z, hz⟩))

theorem component_transport_embedding
    (hd : 0 < KPCuspLogShape.dimension F)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (T : ℝ)
    (f : KPCuspCharts.HighQuotient F
      (KPCuspArithmetic.conjugatedStabilizer F Γ q σ) T →
        KPCuspSiegel.OrbitQuotient F Γ)
    (hf : ∀ (p : {p : KPCuspCharts.Coordinates F // T < p.2}),
      f (Quotient.mk _ p) =
        KPCuspSiegel.projection F Γ (σ • KPCuspCharts.toArch F p.val))
    (j : KPCuspSiegel.CuspQuotient F Γ q (KPCuspSiegel.highCusp F σ T) →
      KPCuspSiegel.OrbitQuotient F Γ)
    (hj : Topology.IsEmbedding j)
    (hjf : ∀ z : KPCuspSiegel.highCusp F σ T,
      j (Quotient.mk _ z) = KPCuspSiegel.projection F Γ z) :
    Topology.IsEmbedding f := by
  let e := KPCuspCharts.highCuspQuotientHomeomorph F hd Γ q σ T
  have he : f = j ∘ e := by
    funext x
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective x
    obtain ⟨z, hz, hez⟩ :=
      KPCuspCharts.highCuspQuotientHomeomorph_formula F hd Γ q σ T p
    change f (Quotient.mk _ p) = j (e (Quotient.mk _ p))
    rw [hf, hez, hjf, hz]
    rfl
  rw [he]
  exact hj.comp e.isEmbedding

theorem component_bounded_shapes
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : KPCuspCharts.ParabolicData F S) :
    ∃ B : Set (KPCuspCharts.Shape F), IsCompact B ∧
      ∀ b : KPCuspCharts.Shape F, ∃ b' ∈ B,
        (QuotientAddGroup.mk b : KPCuspCharts.Base F hF D.E D.integralUnits) =
          QuotientAddGroup.mk b' := by
  obtain ⟨_, _, _, _, _, e, _, he, hcover, _⟩ :=
    kp_cusp_log_unit_shape F hF D.E D.integralUnits D.unitIndex
  refine ⟨parallelepiped e, he, ?_⟩
  intro b
  obtain ⟨u, hu⟩ := hcover b
  refine ⟨b - KPCuspLogShape.logarithm F hF D.E D.integralUnits
    (Additive.ofMul u), hu, ?_⟩
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  simp only [sub_sub_cancel]
  exact ⟨Additive.ofMul u, rfl⟩

theorem component_common_frequency_gap
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    {ι : Type} [Finite ι]
    (S : ι → Subgroup (KPCuspArithmetic.PGL2 F))
    (D : ∀ a, KPCuspCharts.ParabolicData F (S a))
    (ρ : ∀ a, S a →* rootsOfUnity 3 F)
    (V : Submodule ℂ ℂ)
    (C : ∀ a, KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ)
      (S a) (D a) (ρ a) V)
    (O : ∀ a, KPCuspFrequencyGap.CuspOutput (ζ := ζ) (hζ := hζ)
      (S a) (D a) (ρ a) V (C a))
    (B : ι → Set (KPCuspCharts.Shape F)) (hB : ∀ a, IsCompact (B a)) :
    ∃ c : ℝ, 0 < c ∧ ∀ a (b : KPCuspCharts.Shape F), b ∈ B a →
      ∀ ξ : KPCuspFrequencyGap.Frequency (S a) (D a) (ρ a),
        (ξ : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F)) ≠ 0 →
          c ≤ KPCuspFrequencyGap.shapeEnergy b ξ := by
  classical
  choose c hc hgap using fun a => (O a).gap (B a) (hB a)
  obtain ⟨δ, hδ, hδc⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ a, δ ≤ c a := by
    have h : ∀ s : Finset ι, ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ s, δ ≤ c a := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨1, zero_lt_one, by simp⟩
      | @insert a s ha ih =>
        obtain ⟨δ, hδ, hδc⟩ := ih
        refine ⟨min (c a) δ, lt_min (hc a) hδ, ?_⟩
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (hδc b hb)
    letI := Fintype.ofFinite ι
    obtain ⟨δ, hδ, hδc⟩ := h Finset.univ
    exact ⟨δ, hδ, fun a => hδc a (Finset.mem_univ a)⟩
  exact ⟨δ, hδ, fun a b hb ξ hξ => (hδc a).trans (hgap a b hb ξ hξ).1⟩

theorem component_local_cusp_data
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : CompactOpenLevel (KPCuspGenuineMonodromy.FiniteCover F ζ hζ))
    (g : KPCuspGenuineMonodromy.FiniteCover F ζ hζ)
    (line : KPCuspGenuineMonodromy.LineOutput F ζ hζ U g)
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q) :
    let S := KPCuspArithmetic.conjugatedStabilizer F
      (KPCuspGenuineMonodromy.Component F ζ hζ U g) q σ
    let ρ := line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
      (KPCuspGenuineMonodromy.Component F ζ hζ U g) q σ)
    ∃ (D : KPCuspCharts.ParabolicData F S)
      (G : KPCuspCharts.ChartOutput F hF S D)
      (C : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ
        (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)),
      Nonempty (KPCuspFrequencyGap.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ
        (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U) C) := by
  obtain ⟨hc, ho⟩ := KPCuspMonodromy.projected_finite_level_compact_open F ζ hζ U
  obtain ⟨D, ⟨G⟩⟩ := KPCuspMonodromy.finite_adelic_cusp_charts F hF
    (U.toOpenSubgroup.toSubgroup.map (KPCuspGenuineMonodromy.finiteBase F ζ hζ)) hc ho
    (KPCuspGenuineMonodromy.finiteBase F ζ hζ g) q σ hσ
  obtain ⟨C⟩ := KPCuspGenuineMonodromy.cuspOutput_exists _ D _ hF G
    (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)
  exact ⟨D, G, C, KPCuspFrequencyGap.cusp_frequency_gap _ _ _ hF G _ C⟩

theorem component_open_end
    (F : Type) [Field F] [NumberField F]
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    IsOpen (KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F σ T) := by
  haveI : ContinuousConstSMul (KPCuspArithmetic.PGL2 F)
      (KPArch.Space (KPCuspLogShape.dimension F)) :=
    ⟨KPCuspSiegel.continuous_action F⟩
  haveI : ContinuousConstSMul Γ (KPArch.Space (KPCuspLogShape.dimension F)) :=
    ⟨fun γ => KPCuspSiegel.continuous_action F γ⟩
  apply MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  unfold KPCuspSiegel.highCusp
  apply (Homeomorph.smul σ).isOpenMap
  apply isOpen_lt continuous_const
  unfold KPCuspLogShape.meanHeight
  fun_prop

theorem component_ends_exist
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : CompactOpenLevel (KPCuspGenuineMonodromy.FiniteCover F ζ hζ))
    (g : KPCuspGenuineMonodromy.FiniteCover F ζ hζ)
    (line : KPCuspGenuineMonodromy.LineOutput F ζ hζ U g)
    (ends : ∀ Γ : Subgroup (KPCuspArithmetic.PGL2 F),
      KPCuspArithmetic.PGL2 F → ℝ → Set (KPCuspSiegel.OrbitQuotient F Γ))
    (transport : ∀ (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
      (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F) (T : ℝ),
      KPCuspCharts.HighQuotient F (KPCuspArithmetic.conjugatedStabilizer F Γ q σ) T →
        KPCuspSiegel.OrbitQuotient F Γ)
    (volume : ∀ Γ : Subgroup (KPCuspArithmetic.PGL2 F),
      Set (KPCuspGenuineMonodromy.SymmetricSpace F) →
        Measure (KPCuspSiegel.OrbitQuotient F Γ))
    (hends : ∀ Γ σ T, ends Γ σ T =
      KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F σ T)
    (htransport : ∀ Γ q σ T
      (p : {p : KPCuspCharts.Coordinates F // T < p.2}),
      transport Γ q σ T (Quotient.mk _ p) =
        KPCuspSiegel.projection F Γ (σ • KPCuspCharts.toArch F p.val))
    (hvolume : ∀ Γ A, volume Γ A =
      Measure.map (KPCuspSiegel.projection F Γ)
        ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict A)) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∃ D : ComponentEndData F ζ hζ hF U g line ends transport volume,
        D.threshold = T := by
  classical
  obtain ⟨hUc, hUo⟩ :=
    KPCuspMonodromy.projected_finite_level_compact_open F ζ hζ U
  obtain ⟨n, q, σ, T₀, hn, hσ, hexhaust, hinequiv, hhigh⟩ :=
    finite_adelic_component_reduction F hF
      (U.toOpenSubgroup.toSubgroup.map (KPCuspGenuineMonodromy.finiteBase F ζ hζ))
      hUc hUo (KPCuspGenuineMonodromy.finiteBase F ζ hζ g)
  obtain ⟨A, hA, hFD⟩ := finite_adelic_component_fundamental_domain F hF
    (U.toOpenSubgroup.toSubgroup.map (KPCuspGenuineMonodromy.finiteBase F ζ hζ))
    hUc hUo (KPCuspGenuineMonodromy.finiteBase F ζ hζ g)
  choose P G C hO using fun a : Fin n =>
    component_local_cusp_data F ζ hζ hF U g line (q a) (σ a) (hσ a)
  let O := fun a => Classical.choice (hO a)
  choose B hBc hBcover using fun a : Fin n => component_bounded_shapes F hF _ (P a)
  obtain ⟨δ, hδ, hgap⟩ := component_common_frequency_gap F ζ hζ
    (fun a => KPCuspArithmetic.conjugatedStabilizer F
      (KPCuspGenuineMonodromy.Component F ζ hζ U g) (q a) (σ a)) P
    (fun a => line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
      (KPCuspGenuineMonodromy.Component F ζ hζ U g) (q a) (σ a)))
    (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U) C O B hBc
  refine ⟨T₀, ?_⟩
  intro T hT
  obtain ⟨hdisjoint, hcompact, hj⟩ := hhigh T hT
  have hemb : ∀ a : Fin n, Topology.IsEmbedding
      (transport (KPCuspGenuineMonodromy.Component F ζ hζ U g) (q a) (σ a) T) := by
    intro a
    obtain ⟨j, hj, hjf⟩ := hj a
    exact component_transport_embedding F (G a).positive_dimension _ (q a) (σ a) T
      _ (htransport _ (q a) (σ a) T) j hj hjf
  refine ⟨{
    cuspCount := n
    positive_cuspCount := hn
    cusp := q
    representative := σ
    representative_formula := hσ
    exhaustive := hexhaust
    inequivalent := hinequiv
    threshold := T
    parabolic := P
    geometry := G
    monodromy := C
    frequencies := O
    boundedShapes := B
    compact_boundedShapes := hBc
    shapes_cover := hBcover
    frequencyGap := δ
    positive_frequencyGap := hδ
    shortest_frequency := hgap
    constant_rank := fun a => (O a).constantSystem.rank_le_one
    constant_finite := fun a => (O a).constantSystem.finiteDimensional
    open_ends := ?_
    disjoint_ends := ?_
    compact_core := ?_
    end_embedding := hemb
    end_range := ?_
    fundamentalDomain := A
    measurable_fundamentalDomain := hA
    isFundamentalDomain := hFD
    end_volume := ?_ }, rfl⟩
  · intro a
    rw [hends]
    exact component_open_end F _ (σ a) T
  · simpa only [hends] using hdisjoint
  · simpa only [hends] using hcompact
  · intro a
    rw [hends]
    exact component_transport_range F (G a).positive_dimension _ (q a) (σ a) T
      _ (htransport _ (q a) (σ a) T)
  · intro a
    rw [hvolume, hends]
    exact embedded_cusp_end_volume F hF _ (q a) (σ a) (hσ a) T
      (P a) (G a) _ (htransport _ (q a) (σ a) T) (hemb a) A hA hFD

end DedekindZetaZeroFree.KPFiniteAdelicCuspEnds

end

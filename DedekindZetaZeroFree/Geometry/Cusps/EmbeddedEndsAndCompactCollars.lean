module

public import DedekindZetaZeroFree.Geometry.Cusps.MeanHeightDescent
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.HausdorffTopology
public import DedekindZetaZeroFree.Eisenstein.Continuation.Cusps.CutoffSourceData

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPActualCollarBuffer

private theorem endSet_antitone
    (F : Type) [Field F] [NumberField F]
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (σ : KPCuspArithmetic.PGL2 F)
    {T₀ T : ℝ} (hT : T₀ ≤ T) :
    KPFiniteCuspAtlas.endSet F Γ σ T ⊆ KPFiniteCuspAtlas.endSet F Γ σ T₀ := by
  apply Set.image_mono
  apply Set.image_mono
  intro z hz
  exact lt_of_le_of_lt hT hz

theorem actual_end_charts_compact_collars
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (τ T : ℝ) (hτ : A.threshold ≤ τ) (hT : τ < T) :
    let I := Σ i : Fin A.componentCount, Fin (A.cuspAtlas i).cuspCount
    let L := fun (a : I) (z : KPCuspCharts.Coordinates F) =>
      Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
        (((A.cuspAtlas a.1).representative a.2 • KPCuspCharts.toArch F z),
          A.representative a.1)
    let E := fun a : I =>
      KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1) ''
        KPFiniteCuspAtlas.endSet F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
          ((A.cuspAtlas a.1).representative a.2) τ
    let t := fun (a : I) (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) =>
      if h : ∃ z : KPCuspCharts.Coordinates F, τ < z.2 ∧ L a z = x
      then (Classical.choose h).2 else 0
    let C := fun a : I =>
      KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1) ∘
        KPFiniteCuspAtlas.endMap F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
          ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2) τ
    (∀ a, IsOpen (E a)) ∧
    Pairwise (fun a b => Disjoint (E a) (E b)) ∧
    (∀ a, Topology.IsEmbedding (C a)) ∧
    (∀ a, Set.range (C a) = E a) ∧
    (∀ a, IsCompact (closure {x | x ∈ E a ∧ t a x ∈ Set.Icc T (T + 1)})) ∧
    (∀ a, closure {x | x ∈ E a ∧ t a x ∈ Set.Icc T (T + 1)} ⊆ interior (E a)) ∧
    IsCompact (KPCutoffSource.closedCollars E t T) := by
  classical
  obtain ⟨hLrange, hLval, -, -, -, -⟩ := actual_height_descent F ζ hζ hF U A τ hτ
  dsimp only
  letI : T2Space (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
    CoreChartLocalizers.quotient_hausdorff F ζ hζ hF U A
  let L : (Σ i : Fin A.componentCount, Fin (A.cuspAtlas i).cuspCount) →
      KPCuspCharts.Coordinates F → KPFiniteCuspAtlas.rawXU F ζ hζ U :=
    fun a z => Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
      (((A.cuspAtlas a.1).representative a.2 • KPCuspCharts.toArch F z), A.representative a.1)
  let E : (Σ i : Fin A.componentCount, Fin (A.cuspAtlas i).cuspCount) →
      Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
    fun a => KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1) ''
      KPFiniteCuspAtlas.endSet F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
        ((A.cuspAtlas a.1).representative a.2) τ
  let t : (Σ i : Fin A.componentCount, Fin (A.cuspAtlas i).cuspCount) →
      KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ :=
    fun a x => if h : ∃ z : KPCuspCharts.Coordinates F, τ < z.2 ∧ L a z = x
      then (Classical.choose h).2 else 0
  let C := fun a : (Σ i : Fin A.componentCount, Fin (A.cuspAtlas i).cuspCount) =>
      KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1) ∘
        KPFiniteCuspAtlas.endMap F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
          ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2) τ
  have hLrange' : ∀ a, L a '' {z : KPCuspCharts.Coordinates F | τ < z.2} = E a :=
    fun a => hLrange a
  have hLval' : ∀ a (z : KPCuspCharts.Coordinates F), τ < z.2 → t a (L a z) = z.2 :=
    fun a z hz => hLval a z hz
  have hopen : ∀ a, IsOpen (E a) := by
    intro a
    have hop : IsOpenMap
        (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1)) := by
      have he := A.components.isOpenMap.comp (isOpenMap_sigmaMk (i := a.1))
      simpa only [Function.comp_def, A.components_formula] using he
    exact hop _ (KPFiniteAdelicCuspEnds.component_open_end F _ _ τ)
  have hdisj : Pairwise (fun a b : (Σ i : Fin A.componentCount,
      Fin (A.cuspAtlas i).cuspCount) => Disjoint (E a) (E b)) := by
    intro a b hab
    refine Set.disjoint_left.mpr fun z hza hzb => ?_
    obtain ⟨x, hx, rfl⟩ := hza
    obtain ⟨y, hy, he⟩ := hzb
    have he' : A.components ⟨b.1, y⟩ = A.components ⟨a.1, x⟩ := by
      rw [A.components_formula, A.components_formula]
      exact he
    obtain ⟨hij, hyx⟩ := Sigma.mk.inj_iff.mp (A.components.injective he')
    rcases a with ⟨i, ai⟩
    rcases b with ⟨j, bj⟩
    simp only at hij
    subst j
    have hyx' : y = x := eq_of_heq hyx
    subst y
    have hne : ai ≠ bj := fun h => hab (by rw [h])
    have hd := (A.cuspAtlas i).disjoint_ends hne
    exact Set.disjoint_left.mp hd
      (endSet_antitone F _ _ (by rw [A.common_threshold]; exact hτ) hx)
      (endSet_antitone F _ _ (by rw [A.common_threshold]; exact hτ) hy)
  have hemb : ∀ a, Topology.IsEmbedding (C a) := by
    intro a
    have hcm : Topology.IsEmbedding
        (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1)) := by
      have he : KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1) =
          A.components ∘ Sigma.mk a.1 := by
        funext x
        exact (A.components_formula a.1 x).symm
      rw [he]
      exact A.components.isEmbedding.comp Topology.IsEmbedding.sigmaMk
    have hend : Topology.IsEmbedding (KPFiniteCuspAtlas.endMap F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
        ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2) τ) := by
      let G := (A.cuspAtlas a.1).geometry a.2
      let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1)
      let eT := KPFiniteCuspAtlas.endMap F Γ ((A.cuspAtlas a.1).cusp a.2)
        ((A.cuspAtlas a.1).representative a.2) τ
      let e₀ := KPFiniteCuspAtlas.endMap F Γ ((A.cuspAtlas a.1).cusp a.2)
        ((A.cuspAtlas a.1).representative a.2) (A.cuspAtlas a.1).threshold
      let inc : Set.Ioi τ → Set.Ioi (A.cuspAtlas a.1).threshold := fun s =>
        ⟨s.val, by
          change (A.cuspAtlas a.1).threshold < s.val
          rw [show (A.cuspAtlas a.1).threshold = A.threshold from A.common_threshold a.1]
          exact lt_of_le_of_lt hτ s.property⟩
      have hinc : Topology.IsEmbedding inc := by
        apply Topology.IsEmbedding.of_comp (continuous_subtype_val.subtype_mk _)
          continuous_subtype_val
        exact Topology.IsEmbedding.subtypeVal
      have heq : eT ∘ G.highPresentation τ =
          e₀ ∘ G.highPresentation (A.cuspAtlas a.1).threshold ∘ Prod.map id inc := by
        funext x
        rcases x with ⟨p, s⟩
        induction p using Quotient.inductionOn with
        | h p =>
          simp only [Function.comp_apply, Prod.map_apply, id_eq, G.highPresentation_formula]
          rfl
      have hcomp : Topology.IsEmbedding (eT ∘ G.highPresentation τ) := by
        rw [heq]
        exact ((A.cuspAtlas a.1).end_embedding a.2).comp
          ((G.highPresentation (A.cuspAtlas a.1).threshold).isEmbedding.comp
            (Topology.IsEmbedding.id.prodMap hinc))
      have hfinal := hcomp.comp (G.highPresentation τ).symm.isEmbedding
      have heq' : (eT ∘ G.highPresentation τ) ∘ (G.highPresentation τ).symm = eT := by
        funext x
        simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
      rw [heq'] at hfinal
      exact hfinal
    have hCe : C a = KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1) ∘
        KPFiniteCuspAtlas.endMap F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
          ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2) τ := rfl
    rw [hCe]
    exact hcm.comp hend
  have hrange : ∀ a, Set.range (C a) = E a := by
    intro a
    have hCe : C a = KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1) ∘
        KPFiniteCuspAtlas.endMap F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
          ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2) τ := rfl
    rw [hCe, Set.range_comp]
    rw [KPFiniteAdelicCuspEnds.component_transport_range F
      ((A.cuspAtlas a.1).geometry a.2).positive_dimension
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
      ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2) τ _ (fun _ => rfl)]
    rfl
  have hcollar : ∀ a : (Σ i : Fin A.componentCount, Fin (A.cuspAtlas i).cuspCount),
      IsCompact {x : KPFiniteCuspAtlas.rawXU F ζ hζ U |
        x ∈ E a ∧ t a x ∈ Set.Icc T (T + 1)} := by
    intro a
    let S := KPCuspArithmetic.conjugatedStabilizer F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
      ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2)
    let G := (A.cuspAtlas a.1).geometry a.2
    haveI : CompactSpace (KPCuspCharts.CrossQuotient F S) := G.compact_cross
    have hIcc : IsCompact {s : Set.Ioi τ | (s : ℝ) ∈ Set.Icc T (T + 1)} := by
      have hsub : Set.Icc T (T + 1) ⊆ Set.Ioi τ := fun s hs => lt_of_lt_of_le hT hs.1
      have hEq : {s : Set.Ioi τ | (s : ℝ) ∈ Set.Icc T (T + 1)} =
          Set.range (fun s : Set.Icc T (T + 1) =>
            (⟨(s : ℝ), hsub s.property⟩ : Set.Ioi τ)) := by
        ext s
        constructor
        · intro hs
          exact ⟨⟨(s : ℝ), hs⟩, Subtype.ext rfl⟩
        · rintro ⟨s, rfl⟩
          exact s.property
      rw [hEq]
      haveI : CompactSpace (Set.Icc T (T + 1)) := isCompact_iff_compactSpace.mp isCompact_Icc
      exact isCompact_range (by fun_prop)
    have hK : IsCompact (Set.univ ×ˢ {s : Set.Ioi τ | (s : ℝ) ∈ Set.Icc T (T + 1)} :
        Set (KPCuspCharts.CrossQuotient F S × Set.Ioi τ)) := by
      simpa only [Set.univ_prod] using (isCompact_univ.prod hIcc)
    have hcont : Continuous (fun x : KPCuspCharts.CrossQuotient F S × Set.Ioi τ =>
        C a (G.highPresentation τ x)) :=
      (hemb a).continuous.comp (G.highPresentation τ).continuous
    have hset : (fun x : KPCuspCharts.CrossQuotient F S × Set.Ioi τ =>
          C a (G.highPresentation τ x)) ''
          (Set.univ ×ˢ {s : Set.Ioi τ | (s : ℝ) ∈ Set.Icc T (T + 1)}) =
        {x : KPFiniteCuspAtlas.rawXU F ζ hζ U |
          x ∈ E a ∧ t a x ∈ Set.Icc T (T + 1)} := by
      ext x
      constructor
      · rintro ⟨⟨q, s⟩, ⟨-, hs⟩, rfl⟩
        obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
        change C a (G.highPresentation τ (Quotient.mk _ p, s)) ∈
          {x : KPFiniteCuspAtlas.rawXU F ζ hζ U |
            x ∈ E a ∧ t a x ∈ Set.Icc T (T + 1)}
        rw [G.highPresentation_formula]
        have hval : C a (Quotient.mk _ (⟨(p, (s : ℝ)), s.property⟩ :
            {p : KPCuspCharts.Coordinates F // τ < p.2})) = L a (p, (s : ℝ)) := rfl
        rw [hval]
        constructor
        · rw [← hLrange' a]
          exact ⟨(p, (s : ℝ)), s.property, rfl⟩
        · rw [hLval' a (p, (s : ℝ)) s.property]
          exact hs
      · rintro ⟨hxE, hxt⟩
        rw [← hLrange' a] at hxE
        obtain ⟨z, hz, rfl⟩ := hxE
        have hzτ : τ < z.2 := hz
        refine ⟨(Quotient.mk _ z.1, ⟨z.2, hzτ⟩), ⟨Set.mem_univ _, ?_⟩, ?_⟩
        · rw [hLval' a z hzτ] at hxt
          exact hxt
        · show C a (G.highPresentation τ (Quotient.mk _ z.1, ⟨z.2, hzτ⟩)) = L a z
          rw [G.highPresentation_formula]
          rfl
    rw [← hset]
    exact hK.image hcont
  have h5 : ∀ a, IsCompact (closure {x | x ∈ E a ∧ t a x ∈ Set.Icc T (T + 1)}) := by
    intro a
    rw [(hcollar a).isClosed.closure_eq]
    exact hcollar a
  have h6 : ∀ a, closure {x | x ∈ E a ∧ t a x ∈ Set.Icc T (T + 1)} ⊆ interior (E a) := by
    intro a
    rw [(hcollar a).isClosed.closure_eq, (hopen a).interior_eq]
    exact fun x hx => hx.1
  have h7 : IsCompact (KPCutoffSource.closedCollars E t T) := by
    rw [KPCutoffSource.closedCollars]
    exact isCompact_iUnion fun a => h5 a
  exact ⟨hopen, hdisj, hemb, hrange, h5, h6, h7⟩

end DedekindZetaZeroFree.KPActualCollarBuffer

end

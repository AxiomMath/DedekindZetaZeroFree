module

public import DedekindZetaZeroFree.Metaplectic.Cubic.TranslatedChartTopology
public import DedekindZetaZeroFree.Metaplectic.Kubota.DeepCongruenceConjugationCompatibility

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPLocalChartTopology

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F))

def MatrixChartDepth (m : ℕ) : Prop :=
  1 ≤ m ∧ ∀ k ∈ KPLocalCube.Gamma F v m,
    (∀ i : Fin 2, ∃ t : (KPLocalCube.LocalField F v)ˣ,
      ((t ^ 3 : (KPLocalCube.LocalField F v)ˣ) :
        KPLocalCube.LocalField F v) = k i i) ∧
    Matrix.GeneralLinearGroup.det k ∈ KPLocalCube.cubes F v

def translatedChart (m : ℕ)
    (γ : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v))
    (k : KPLocalCube.Gamma F v m) :
    KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v) :=
  γ * KPLocalCover.sectionMap F ζ hζ (Sum.inr v) k.val

def translatedTopology (m : ℕ) :
    TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) where
  IsOpen U := ∀ γ, IsOpen (translatedChart F ζ hζ v m γ ⁻¹' U)
  isOpen_univ := by intro γ; simp
  isOpen_inter := by
    intro U V hU hV γ
    simpa only [Set.preimage_inter] using (hU γ).inter (hV γ)
  isOpen_sUnion := by
    intro S hS γ
    rw [Set.preimage_sUnion]
    exact isOpen_biUnion (fun U hU => hS U hU γ)

theorem isOpen_iff (m : ℕ)
    (U : Set (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v))) :
    @IsOpen _ (translatedTopology F ζ hζ v m) U ↔
      ∀ γ, IsOpen {k : KPLocalCube.Gamma F v m |
        γ * KPLocalCover.sectionMap F ζ hζ (Sum.inr v) k.val ∈ U} := by
  rfl

set_option maxHeartbeats 500000 in

theorem translatedChart_isOpenEmbedding (m : ℕ)
    (hm : MatrixChartDepth F v m)
    (γ : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) :
    letI := translatedTopology F ζ hζ v m
    Topology.IsOpenEmbedding (translatedChart F ζ hζ v m γ) := by
  set_option maxHeartbeats 800000 in
  letI := translatedTopology F ζ hζ v m
  obtain ⟨s, hs, hi, _⟩ := KPDeepRawSplitting.raw_section_splitting F ζ hζ v m
    (fun g hg h hh => KPDeepRawSplitting.sigmaTwo_eq_one_on_Gamma F ζ hζ v m hm.2 g h hg hh)
  have he : CubicCoverTranslatedCharts.topology s = translatedTopology F ζ hζ v m := by
    apply TopologicalSpace.ext
    funext U
    change (∀ g, IsOpen ((fun k => g * s k) ⁻¹' U)) =
      (∀ g, IsOpen ((fun k : KPLocalCube.Gamma F v m =>
        g * KPLocalCover.sectionMap F ζ hζ (Sum.inr v) k.val) ⁻¹' U))
    simp only [hs]
  have h := CubicCoverTranslatedCharts.isOpenEmbedding s hi γ
  rw [he] at h
  have hf : (fun k => γ * s k) = translatedChart F ζ hζ v m γ := by
    funext k
    exact congrArg (fun x => γ * x) (hs k)
  rw [hf] at h
  exact h

theorem translatedChart_homeomorphism (m : ℕ)
    (hm : MatrixChartDepth F v m)
    (γ : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) :
    letI := translatedTopology F ζ hζ v m
    IsOpen (Set.range (translatedChart F ζ hζ v m γ)) ∧
      ∃ e : KPLocalCube.Gamma F v m ≃ₜ
          Set.range (translatedChart F ζ hζ v m γ),
        ∀ k, (e k).val = translatedChart F ζ hζ v m γ k := by
  letI := translatedTopology F ζ hζ v m
  have h := translatedChart_isOpenEmbedding F ζ hζ v m hm γ
  exact ⟨h.isOpen_range, h.isEmbedding.toHomeomorph, fun _ => rfl⟩

theorem finite_topological_group (m : ℕ) (hm : MatrixChartDepth F v m) :
    letI := translatedTopology F ζ hζ v m
    T2Space (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) ∧
      LocallyCompactSpace (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) ∧
      IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) := by
  letI := translatedTopology F ζ hζ v m
  obtain ⟨s, hs, hi, _⟩ := KPDeepRawSplitting.raw_section_splitting F ζ hζ v m
    (fun g hg h hh => KPDeepRawSplitting.sigmaTwo_eq_one_on_Gamma F ζ hζ v m hm.2 g h hg hh)
  have he : CubicCoverTranslatedCharts.topology s = translatedTopology F ζ hζ v m := by
    apply TopologicalSpace.ext
    funext U
    change (∀ g, IsOpen ((fun k => g * s k) ⁻¹' U)) =
      (∀ g, IsOpen ((fun k : KPLocalCube.Gamma F v m =>
        g * KPLocalCover.sectionMap F ζ hζ (Sum.inr v) k.val) ⁻¹' U))
    simp only [hs]
  have hgrp : IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) := by
    change @IsTopologicalGroup _ (translatedTopology F ζ hζ v m) _
    rw [← he]
    apply CubicCoverTranslatedCharts.topologicalGroup s hi
    intro x
    obtain ⟨r, hr, hc⟩ := KPDeepConjugationGerms.raw_extension_conjugation_near_identity
      F ζ hζ v m hm.1 hm.2 x.g
    let J := (KPLocalCube.Gamma F v r).comap (KPLocalCube.Gamma F v m).subtype
    have hJ : IsOpen (J : Set (KPLocalCube.Gamma F v m)) :=
      (KPLocalCube.Gamma_compact_open F v r (hm.1.trans hr)).2.preimage continuous_subtype_val
    let c : J → KPLocalCube.Gamma F v m := fun k =>
      ⟨x.g * k.val.val * x.g⁻¹, (hc _ k.property).1⟩
    have hcc : Continuous c := by
      apply Continuous.subtype_mk
      exact (continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).mul continuous_const
    exact CubicCoverTranslatedCharts.conjugation_tendsto s hi x J hJ c hcc
      (fun k => by rw [hs, hs]; exact (hc _ k.property).2 x rfl)
  letI := hgrp
  have hclosed : IsClosed ({1} : Set (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v))) := by
    apply isOpen_compl_iff.mp
    intro g
    rw [Set.preimage_compl]
    apply isOpen_compl_iff.mpr
    have hinj := (translatedChart_isOpenEmbedding F ζ hζ v m hm g).injective
    by_cases hex : ∃ k, translatedChart F ζ hζ v m g k = 1
    · obtain ⟨k, hk⟩ := hex
      have hset : translatedChart F ζ hζ v m g ⁻¹' {1} = {k} := by
        ext j
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun hj => hinj (hj.trans hk.symm), fun hj => hj ▸ hk⟩
      rw [hset]
      exact isClosed_singleton
    · have hset : translatedChart F ζ hζ v m g ⁻¹' {1} = ∅ := by
        ext k
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun hk => hex ⟨k, hk⟩
      rw [hset]
      exact isClosed_empty
  have ht : T2Space (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) :=
    IsTopologicalGroup.t2Space_iff_one_closed.mpr hclosed
  letI := ht
  have ho := translatedChart_isOpenEmbedding F ζ hζ v m hm 1
  have hcpt : IsCompact (Set.range (translatedChart F ζ hζ v m 1)) := by
    letI : CompactSpace (KPLocalCube.Gamma F v m) :=
      isCompact_iff_compactSpace.mp (KPLocalCube.Gamma_compact_open F v m hm.1).1
    exact isCompact_range ho.continuous
  have hn : Set.range (translatedChart F ζ hζ v m 1) ∈ nhds
      (1 : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) := by
    apply ho.isOpen_range.mem_nhds
    refine ⟨1, ?_⟩
    change (1 : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) * 1 = 1
    exact one_mul _
  exact ⟨ht, hcpt.locallyCompactSpace_of_mem_nhds_of_group hn, hgrp⟩

theorem finite_projection (m : ℕ) (hm : MatrixChartDepth F v m) :
    letI := translatedTopology F ζ hζ v m
    IsLocalHomeomorph (KPLocalCover.projection F ζ hζ (Sum.inr v)) ∧
      ∀ g : KPLocalCover.LocalGL2 F (Sum.inr v),
        Nat.card {x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v) |
          KPLocalCover.projection F ζ hζ (Sum.inr v) x = g} = 3 := by
  letI := translatedTopology F ζ hζ v m
  refine ⟨?_, ?_⟩
  · intro x
    have hs := translatedChart_isOpenEmbedding F ζ hζ v m hm x
    have hb : Topology.IsOpenEmbedding
        (fun k : KPLocalCube.Gamma F v m => x.g * k.val) :=
      (Homeomorph.mulLeft x.g).isOpenEmbedding.comp
        (KPLocalCube.Gamma_compact_open F v m hm.1).2.isOpenEmbedding_subtypeVal
    have heq : KPLocalCover.projection F ζ hζ (Sum.inr v) ∘
        translatedChart F ζ hζ v m x =
        (fun k : KPLocalCube.Gamma F v m => x.g * k.val) := rfl
    have hlocal := (heq ▸ hb.isLocalHomeomorph.isLocalHomeomorphOn
      (s := Set.univ)).of_comp_right hs.isLocalHomeomorph.isLocalHomeomorphOn
    apply hlocal x
    exact ⟨1, Set.mem_univ _, by
      change x * (1 : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) = x
      exact mul_one x⟩
  · intro g
    let q : {x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v) |
        KPLocalCover.projection F ζ hζ (Sum.inr v) x = g} ≃ rootsOfUnity 3 F := {
      toFun x := x.val.epsilon
      invFun ε := ⟨⟨g, ε⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨xg, xe⟩, hx⟩
        change xg = g at hx
        subst xg
        rfl
      right_inv := fun _ => rfl
    }
    exact (Nat.card_congr q).trans (KPHilbert.primitive_three F ζ hζ).card_rootsOfUnity

theorem finite_three_sheet_trivialization (m : ℕ)
    (hm : MatrixChartDepth F v m)
    (g : KPLocalCover.LocalGL2 F (Sum.inr v)) :
    letI := translatedTopology F ζ hζ v m
    letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
    ∃ e : (rootsOfUnity 3 F × KPLocalCube.Gamma F v m) ≃ₜ
        {x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v) |
          x.g ∈ (fun k : KPLocalCube.Gamma F v m => g * k.val) '' Set.univ},
      ∀ ε k, (e (ε, k)).val =
        KPLocalCover.centralInjection F ζ hζ (Sum.inr v) ε *
          KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g *
          KPLocalCover.sectionMap F ζ hζ (Sum.inr v) k.val := by
  letI := translatedTopology F ζ hζ v m
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  let B := {x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v) |
    x.g ∈ (fun k : KPLocalCube.Gamma F v m => g * k.val) '' Set.univ}
  let a : rootsOfUnity 3 F → KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v) :=
    fun ε => KPLocalCover.centralInjection F ζ hζ (Sum.inr v) ε *
      KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g
  let f : (rootsOfUnity 3 F × KPLocalCube.Gamma F v m) → B := fun p =>
    ⟨translatedChart F ζ hζ v m (a p.1) p.2,
      ⟨p.2, Set.mem_univ _, by simp [translatedChart, a]⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨ε, k⟩ ⟨δ, l⟩ heq
      have hkl : k = l := by
        apply Subtype.ext
        apply mul_left_cancel (a := g)
        have h := congrArg (fun z : B => z.val.g) heq
        simpa [f, translatedChart, a] using h
      subst l
      have he : a ε = a δ := mul_right_cancel (congrArg Subtype.val heq)
      have hed : ε = δ := KPLocalCover.centralInjection_injective F ζ hζ (Sum.inr v)
        (mul_right_cancel he)
      exact Prod.ext hed rfl
    · rintro ⟨x, hx⟩
      obtain ⟨k, _, hk⟩ := hx
      let y := (KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g)⁻¹ * x
      have hyg : y.g = k.val := by
        simp only [y, KPLocalCover.mul_g, KPLocalCover.inv_g, KPLocalCover.sectionMap_g]
        rw [← hk]
        simp only [inv_mul_cancel_left]
      refine ⟨(y.epsilon, k), ?_⟩
      apply Subtype.ext
      change a y.epsilon * KPLocalCover.sectionMap F ζ hζ (Sum.inr v) k.val = x
      rw [← hyg]
      dsimp only [a]
      rw [KPDeepConjugationGerms.central_comm F ζ hζ v,
        mul_assoc, ← KPDeepConjugationGerms.cover_eq F ζ hζ v y]
      simp only [y, mul_inv_cancel_left]
  have hfc : Continuous f := by
    apply continuous_prod_of_discrete_left.mpr
    intro ε
    exact (translatedChart_isOpenEmbedding F ζ hζ v m hm (a ε)).continuous.subtype_mk _
  have hfo : IsOpenMap f := by
    intro U hU
    have hset : f '' U = ⋃ ε : rootsOfUnity 3 F,
        (fun k => f (ε, k)) '' ((fun k => (ε, k)) ⁻¹' U) := by
      ext x
      simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨⟨ε, k⟩, hp, hx⟩
        exact ⟨ε, k, hp, hx⟩
      · rintro ⟨ε, k, hp, hx⟩
        exact ⟨(ε, k), hp, hx⟩
    rw [hset]
    apply isOpen_iUnion
    intro ε
    have ho : IsOpenMap (fun k => f (ε, k)) :=
      (translatedChart_isOpenEmbedding F ζ hζ v m hm (a ε)).isOpenMap.subtype_mk _
    exact ho _ (hU.preimage (continuous_const.prodMk continuous_id))
  let e := (Equiv.ofBijective f hf).toHomeomorphOfContinuousOpen hfc hfo
  exact ⟨e, fun _ _ => rfl⟩

theorem finite_discrete_kernel (m : ℕ) (hm : MatrixChartDepth F v m) :
    letI := translatedTopology F ζ hζ v m
    letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
    DiscreteTopology (KPLocalCover.projection F ζ hζ (Sum.inr v)).ker ∧
      ∃ e : rootsOfUnity 3 F ≃ₜ
          (KPLocalCover.projection F ζ hζ (Sum.inr v)).ker,
        ∀ ε, (e ε).val = KPLocalCover.centralInjection F ζ hζ (Sum.inr v) ε := by
  letI := translatedTopology F ζ hζ v m
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  letI : T2Space (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) :=
    (finite_topological_group F ζ hζ v m hm).1
  let q : rootsOfUnity 3 F ≃ (KPLocalCover.projection F ζ hζ (Sum.inr v)).ker := {
    toFun ε := ⟨KPLocalCover.centralInjection F ζ hζ (Sum.inr v) ε, rfl⟩
    invFun x := x.val.epsilon
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨⟨g, ε⟩, hx⟩
      change g = 1 at hx
      subst g
      rfl
  }
  letI : Finite (KPLocalCover.projection F ζ hζ (Sum.inr v)).ker := Finite.of_equiv _ q
  letI : DiscreteTopology (KPLocalCover.projection F ζ hζ (Sum.inr v)).ker := inferInstance
  exact ⟨inferInstance, q.toHomeomorphOfDiscrete, fun _ => rfl⟩

private theorem Gamma_antitone {a b : ℕ} (hab : a ≤ b) :
    KPLocalCube.Gamma F v b ≤ KPLocalCube.Gamma F v a := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g, ?_, rfl⟩
  apply (KPLocalCube.mem_integerCongruence_iff F v a g).mpr
  intro i j
  exact Ideal.pow_le_pow_right hab
    ((KPLocalCube.mem_integerCongruence_iff F v b g).mp hg i j)

private theorem identity_continuous (m n : ℕ)
    (hm : MatrixChartDepth F v m) (hn : MatrixChartDepth F v n) :
    @Continuous _ _ (translatedTopology F ζ hζ v m) (translatedTopology F ζ hζ v n) id := by
  letI := translatedTopology F ζ hζ v m
  letI : IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) :=
    (finite_topological_group F ζ hζ v m hm).2.2
  let r := max m n
  let J := (KPLocalCube.Gamma F v r).comap (KPLocalCube.Gamma F v m).subtype
  have hJ : IsOpen (J : Set (KPLocalCube.Gamma F v m)) :=
    (KPLocalCube.Gamma_compact_open F v r (hm.1.trans (le_max_left _ _))).2.preimage continuous_subtype_val
  have ho := (translatedChart_isOpenEmbedding F ζ hζ v m hm 1).comp hJ.isOpenEmbedding_subtypeVal
  let f : J → KPLocalCube.Gamma F v n := fun k =>
    ⟨k.val.val, Gamma_antitone F v (le_max_right m n) k.property⟩
  have hf : Continuous f := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) _
  have hc : @Continuous _ _ _ (translatedTopology F ζ hζ v n)
      (translatedChart F ζ hζ v m 1 ∘ (Subtype.val : J → KPLocalCube.Gamma F v m)) := by
    letI := translatedTopology F ζ hζ v n
    have hc := (translatedChart_isOpenEmbedding F ζ hζ v n hn 1).continuous.comp hf
    have heq : translatedChart F ζ hζ v n 1 ∘ f =
        translatedChart F ζ hζ v m 1 ∘ (Subtype.val : J → KPLocalCube.Gamma F v m) := by
      funext k
      rfl
    exact heq ▸ hc
  have hcont : @ContinuousAt _ _ (translatedTopology F ζ hζ v m) (translatedTopology F ζ hζ v n)
      id 1 := by
    have ht := (@Topology.IsOpenEmbedding.continuousAt_iff _ _ _
      _ id _ _ (translatedTopology F ζ hζ v n) ho (x := (1 : J))).mp
        (@Continuous.continuousAt _ _ _ (translatedTopology F ζ hζ v n) _ (1 : J) hc)
    change @ContinuousAt _ _ (translatedTopology F ζ hζ v m) (translatedTopology F ζ hζ v n)
      id (1 * (1 : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v))) at ht
    simpa only [one_mul] using ht
  exact @continuous_of_continuousAt_one _ (translatedTopology F ζ hζ v m) _
    (finite_topological_group F ζ hζ v m hm).2.2 _ _ _ (translatedTopology F ζ hζ v n)
    (finite_topological_group F ζ hζ v n hn).2.2.toContinuousMul _ _ (MonoidHom.id _) hcont

theorem translatedTopology_independent (m n : ℕ)
    (hm : MatrixChartDepth F v m) (hn : MatrixChartDepth F v n) :
    translatedTopology F ζ hζ v m = translatedTopology F ζ hζ v n := by
  exact le_antisymm (continuous_id_iff_le.mp (identity_continuous F ζ hζ v m n hm hn))
    (continuous_id_iff_le.mp (identity_continuous F ζ hζ v n m hn hm))

theorem deep_chart_topology :
    ∃ m : ℕ, MatrixChartDepth F v m ∧ ∀ r : ℕ, m ≤ r →
      MatrixChartDepth F v r ∧
        translatedTopology F ζ hζ v r = translatedTopology F ζ hζ v m := by
  obtain ⟨m, hm, _hcubes, hdeep⟩ := KPDeepRawSplitting.deep_raw_splitting F ζ hζ v
  have hchart : ∀ r, m ≤ r → MatrixChartDepth F v r :=
    fun r hr => ⟨hm.trans hr, (hdeep r hr).1⟩
  refine ⟨m, hchart m le_rfl, ?_⟩
  intro r hr
  exact ⟨hchart r hr, translatedTopology_independent F ζ hζ v r m
    (hchart r hr) (hchart m le_rfl)⟩

variable (w : InfinitePlace F)

def complexCoordinates : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) ≃
    (KPLocalCover.LocalGL2 F (Sum.inl w) × rootsOfUnity 3 F) where
  toFun x := (x.g, x.epsilon)
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

def complexTopology :
    TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) :=
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  TopologicalSpace.induced (complexCoordinates F ζ hζ w) inferInstance

theorem complex_sigmaTwo_eq_one
    (g h : KPLocalCover.LocalGL2 F (Sum.inl w)) :
    KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) g h = 1 := by
  simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau,
    KPHilbert.B3, KPHilbert.B6, KPHilbert.squareToThree]

theorem complex_product_cover :
    letI := complexTopology F ζ hζ w
    letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
    ∃ e : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) ≃*
        (KPLocalCover.LocalGL2 F (Sum.inl w) × rootsOfUnity 3 F),
      (∀ x, e x = (x.g, x.epsilon)) ∧
        Continuous e ∧ Continuous e.symm := by
  letI := complexTopology F ζ hζ w
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  let e : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) ≃*
      (KPLocalCover.LocalGL2 F (Sum.inl w) × rootsOfUnity 3 F) :=
    { complexCoordinates F ζ hζ w with
      map_mul' := by
        intro x y
        change (x.g * y.g,
          x.epsilon * y.epsilon * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) x.g y.g) =
          (x.g * y.g, x.epsilon * y.epsilon)
        rw [complex_sigmaTwo_eq_one F ζ hζ w, mul_one] }
  have hi : Topology.IsInducing (complexCoordinates F ζ hζ w) := ⟨rfl⟩
  let h := (complexCoordinates F ζ hζ w).toHomeomorphOfIsInducing hi
  exact ⟨e, (fun _ => rfl), h.continuous, h.symm.continuous⟩

private theorem fst_localHomeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [DiscreteTopology Y] :
    IsLocalHomeomorph (Prod.fst : X × Y → X) := by
  intro p
  let e : OpenPartialHomeomorph (X × Y) X := {
    toFun := Prod.fst
    invFun := fun x => (x, p.2)
    source := {q | q.2 = p.2}
    target := Set.univ
    map_source' := fun _ _ => Set.mem_univ _
    map_target' := fun _ _ => rfl
    left_inv' := by intro q hq; exact Prod.ext rfl hq.symm
    right_inv' := fun _ _ => rfl
    continuousOn_toFun := continuous_fst.continuousOn
    continuousOn_invFun := (continuous_id.prodMk continuous_const).continuousOn
    open_source := (isOpen_discrete ({p.2} : Set Y)).preimage continuous_snd
    open_target := isOpen_univ
  }
  exact ⟨e, rfl, rfl⟩

theorem complex_topological_cover :
    letI := complexTopology F ζ hζ w
    T2Space (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) ∧
      LocallyCompactSpace (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) ∧
      IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) ∧
      IsLocalHomeomorph (KPLocalCover.projection F ζ hζ (Sum.inl w)) ∧
      DiscreteTopology (KPLocalCover.projection F ζ hζ (Sum.inl w)).ker ∧
      ∀ g : KPLocalCover.LocalGL2 F (Sum.inl w),
        Nat.card {x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) |
          KPLocalCover.projection F ζ hζ (Sum.inl w) x = g} = 3 := by
  letI := complexTopology F ζ hζ w
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  obtain ⟨e, he, hc, hci⟩ := complex_product_cover F ζ hζ w
  let E : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) ≃ₜ*
      (KPLocalCover.LocalGL2 F (Sum.inl w) × rootsOfUnity 3 F) :=
    { e with continuous_toFun := hc, continuous_invFun := hci }
  let H := E.toHomeomorph
  letI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) w.Completion) := by
    change LocallyCompactSpace (Fin 2 → Fin 2 → w.Completion)
    infer_instance
  letI : LocallyCompactSpace (KPLocalCover.LocalGL2 F (Sum.inl w)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have ht : T2Space (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) := H.symm.t2Space
  letI := ht
  have hl : IsLocalHomeomorph (KPLocalCover.projection F ζ hζ (Sum.inl w)) := by
    have hp := fst_localHomeomorph.comp H.isLocalHomeomorph
    have heq : (Prod.fst ∘ H) = KPLocalCover.projection F ζ hζ (Sum.inl w) := by
      funext x
      exact congrArg Prod.fst (he x)
    exact heq ▸ hp
  have hk : DiscreteTopology (KPLocalCover.projection F ζ hζ (Sum.inl w)).ker := by
    haveI : Finite (KPLocalCover.projection F ζ hζ (Sum.inl w)).ker :=
      Finite.of_injective (fun x => x.val.epsilon) (by
        intro x y hxy
        apply Subtype.ext
        cases x with
        | mk x hx =>
          cases y with
          | mk y hy =>
            cases x with
            | mk xg xe =>
              cases y with
              | mk yg ye =>
                change xg = 1 at hx
                change yg = 1 at hy
                change xe = ye at hxy
                simp only [hx, hy, hxy])
    infer_instance
  refine ⟨ht, H.locallyCompactSpace_iff.mpr inferInstance,
    E.isTopologicalGroup, hl, hk, ?_⟩
  intro g
  let q : {x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) |
      KPLocalCover.projection F ζ hζ (Sum.inl w) x = g} ≃ rootsOfUnity 3 F := {
    toFun x := x.val.epsilon
    invFun ε := ⟨⟨g, ε⟩, rfl⟩
    left_inv := by
      rintro ⟨⟨xg, xe⟩, hx⟩
      change xg = g at hx
      subst xg
      rfl
    right_inv := fun _ => rfl
  }
  exact (Nat.card_congr q).trans (KPHilbert.primitive_three F ζ hζ).card_rootsOfUnity

end
end DedekindZetaZeroFree.KPLocalChartTopology

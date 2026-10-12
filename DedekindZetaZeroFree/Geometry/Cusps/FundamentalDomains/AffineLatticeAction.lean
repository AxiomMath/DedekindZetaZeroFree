module

public import DedekindZetaZeroFree.Geometry.Cusps.AffineTorusBundles.QuotientCoordinates

@[expose] public section

noncomputable section
open scoped Classical Matrix Pointwise
open MeasureTheory Set

namespace DedekindZetaZeroFree.KPCuspChart.SectionConstruction

theorem measurable_fundamental_domain_of_countable_slices
    {H X : Type*} [Group H] [Countable H] [MeasurableSpace X]
    [MulAction H X] [MeasurableConstSMul H X]
    (ν : Measure X) (U : ℕ → Set X)
    (hU : ∀ n, MeasurableSet (U n))
    (hslice : ∀ n (g : H), g ≠ 1 → Disjoint (g • U n) (U n))
    (hcover : ∀ᵐ x ∂ν, ∃ n, ∃ g : H, g • x ∈ U n) :
    ∃ Ω : Set X, MeasurableSet Ω ∧ IsFundamentalDomain H Ω ν := by
  let V : ℕ → Set X := fun n => U n \ ⋃ (j : ℕ), ⋃ (_ : j < n), ⋃ (g : H), g • U j
  let Ω : Set X := ⋃ n, V n
  have hV : ∀ n, MeasurableSet (V n) := fun n =>
    (hU n).diff (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iUnion fun g => (hU j).const_smul g)
  have hΩ : MeasurableSet Ω := MeasurableSet.iUnion hV
  have unique : ∀ x (a b : H), a • x ∈ Ω → b • x ∈ Ω → a = b := by
    intro x a b ha hb
    obtain ⟨i, hi⟩ := mem_iUnion.mp ha
    obtain ⟨j, hj⟩ := mem_iUnion.mp hb
    have hij : i = j := by
      by_contra h
      rcases lt_or_gt_of_ne h with hlt | hgt
      · apply hj.2
        exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hlt, mem_iUnion.mpr
          ⟨b * a⁻¹, ⟨a • x, hi.1, by simp [mul_smul]⟩⟩⟩⟩
      · apply hi.2
        exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hgt, mem_iUnion.mpr
          ⟨a * b⁻¹, ⟨b • x, hj.1, by simp [mul_smul]⟩⟩⟩⟩
    subst j
    by_contra hab
    have hne : b * a⁻¹ ≠ 1 := by
      intro h
      apply hab
      exact (mul_inv_eq_one.mp h).symm
    exact Set.disjoint_left.mp (hslice i (b * a⁻¹) hne)
      ⟨a • x, hi.1, by simp [mul_smul]⟩ hj.1
  refine ⟨Ω, hΩ, ?_⟩
  refine ⟨hΩ.nullMeasurableSet, ?_, ?_⟩
  · filter_upwards [hcover] with x hx
    let n := Nat.find hx
    obtain ⟨g, hg⟩ := Nat.find_spec hx
    refine ⟨g, mem_iUnion.mpr ⟨n, hg, ?_⟩⟩
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    obtain ⟨hjn, hj⟩ := mem_iUnion.mp hj
    obtain ⟨a, y, hy, heq⟩ := mem_iUnion.mp hj
    have hsmall : ∃ b : H, b • x ∈ U j := by
      refine ⟨a⁻¹ * g, ?_⟩
      have : a⁻¹ • (g • x) = y := by rw [← heq]; simp
      simpa [mul_smul] using this.symm ▸ hy
    exact Nat.find_min hx hjn hsmall
  · intro a b hab
    apply Disjoint.aedisjoint
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    rw [mem_smul_set_iff_inv_smul_mem] at hxa hxb
    exact hab (inv_injective (unique x a⁻¹ b⁻¹ hxa hxb))

theorem measurable_fundamental_domain_of_properly_discontinuous_ae_free
    {H X : Type*} [Group H] [Countable H] [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [MulAction H X]
    [ContinuousConstSMul H X] [ProperlyDiscontinuousSMul H X]
    (ν : Measure X)
    (hfree : ∀ᵐ x ∂ν, ∀ g : H, g • x = x → g = 1) :
    ∃ Ω : Set X, MeasurableSet Ω ∧ IsFundamentalDomain H Ω ν := by
  let T := {x : X // ∀ g : H, g • x = x → g = 1}
  have hlocal : ∀ x : T, ∃ U : Set X, IsOpen U ∧ x.val ∈ U ∧
      ∀ g : H, g ≠ 1 → Disjoint (g • U) U := by
    intro x
    obtain ⟨V, hV, hdisj⟩ := ProperlyDiscontinuousSMul.exists_nhds_disjoint_image H x.val
    obtain ⟨U, hUV, hU, hxU⟩ := mem_nhds_iff.mp hV
    refine ⟨U, hU, hxU, fun g hg => ?_⟩
    exact (hdisj g (fun h => hg (x.property g h))).mono (Set.image_mono hUV) hUV
  choose U hU hxU hslice using hlocal
  obtain ⟨C, hC, hcoverC⟩ := TopologicalSpace.isOpen_iUnion_countable U hU
  by_cases hT : Nonempty T
  · letI := hT
    obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.mp hC
    apply measurable_fundamental_domain_of_countable_slices ν (U ∘ f)
      (fun n => (hU _).measurableSet) (fun n g hg => hslice _ g hg)
    filter_upwards [hfree] with x hx
    have hxW : x ∈ ⋃ t, U t := mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
    rw [← hcoverC] at hxW
    obtain ⟨t, ht⟩ := mem_iUnion.mp hxW
    obtain ⟨htC, hxt⟩ := mem_iUnion.mp ht
    obtain ⟨n, hn⟩ := hf htC
    refine ⟨n, 1, ?_⟩
    simpa [Function.comp_def, hn] using hxt
  · have hempty : ∀ᵐ x ∂ν, False := by
      filter_upwards [hfree] with x hx
      exact hT ⟨⟨x, hx⟩⟩
    refine ⟨∅, MeasurableSet.empty, ?_⟩
    refine ⟨MeasurableSet.empty.nullMeasurableSet, ?_, ?_⟩
    · exact hempty.mono fun x hx => hx.elim
    · intro a b hab
      simp only [smul_set_empty]
      exact (disjoint_bot_left : Disjoint (∅ : Set X) ∅).aedisjoint

theorem properlyDiscontinuous_of_equivariant
    {H J X Y : Type*} [Group H] [Group J]
    [TopologicalSpace X] [TopologicalSpace Y] [MulAction H X] [MulAction J Y]
    [ContinuousConstSMul H X] [ProperlyDiscontinuousSMul J Y]
    (r : H →* J) [ProperlyDiscontinuousSMul r.ker X]
    (f : X → Y) (hf : Continuous f) (he : ∀ g x, f (g • x) = r g • f x) :
    ProperlyDiscontinuousSMul H X := by
  constructor
  intro K L hK hL
  let T : Set H := {g | ((g • ·) '' K ∩ L).Nonempty}
  have himage : (r '' T).Finite := by
    apply (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (hK.image hf) (hL.image hf)).subset
    rintro _ ⟨g, ⟨y, ⟨x, hx, hxy⟩, hyL⟩, rfl⟩
    refine ⟨f y, ⟨f x, ⟨x, hx, rfl⟩, ?_⟩, ⟨y, hyL, rfl⟩⟩
    change r g • f x = f y
    change g • x = y at hxy
    rw [← he, hxy]
  apply Set.Finite.of_finite_fibers r himage
  intro j hj
  obtain ⟨a, ha, haj⟩ := hj
  ·
    let b : {g : H // g ∈ T ∧ r g = j} → r.ker := fun g =>
      ⟨a⁻¹ * g, by change r (a⁻¹ * g) = 1; simp [haj, g.property.2]⟩
    have hb : Function.Injective b := by
      intro g g' h
      apply Subtype.ext
      exact mul_left_cancel (congrArg Subtype.val h)
    have hfinite := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
      (Γ := r.ker) hK (hL.image (continuous_const_smul a⁻¹))
    have hsub : range b ⊆ {n : r.ker | ((n • ·) '' K ∩ (a⁻¹ • ·) '' L).Nonempty} := by
      rintro _ ⟨g, rfl⟩
      obtain ⟨y, ⟨x, hx, hxy⟩, hy⟩ := g.property.1
      refine ⟨a⁻¹ • y, ⟨x, hx, ?_⟩, ⟨y, hy, rfl⟩⟩
      change (a⁻¹ * g.val) • x = a⁻¹ • y
      change g.val • x = y at hxy
      rw [mul_smul, hxy]
    letI : Fintype (range b) := (hfinite.subset hsub).fintype
    letI : Finite {g : H // g ∈ T ∧ r g = j} :=
      Finite.of_injective (fun g => (⟨b g, mem_range_self g⟩ : range b))
        (fun g g' h => hb (congrArg Subtype.val h))
    have hfin : {g : H | g ∈ T ∧ r g = j}.Finite := by
      rw [← Set.finite_coe_iff]
      change Finite {g : H // g ∈ T ∧ r g = j}
      infer_instance
    convert hfin using 1
    ext g
    simp

private theorem translation_formula
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (x : D.L) (p : Cross F) :
    G.crossAction (D.inclusion (Multiplicative.ofAdd x)) p =
      (p.1 + embedding F x.val, p.2) := by
  obtain ⟨A, hA, hc⟩ := D.upper
    (D.inclusion (Multiplicative.ofAdd x)).val
    (D.inclusion (Multiplicative.ofAdd x)).property
  obtain ⟨_, hd, ht⟩ := D.unipotentFormula x A hA
  have hn : A 1 1 ≠ 0 := by
    intro hz
    exact A.det_ne_zero (by simp [Matrix.det_fin_two, hc, hd, hz])
  have hv : A 0 1 / A 1 1 = x.val := by
    rw [ht, hd, mul_div_cancel_right₀ _ hn]
  have hr : D.ratio (D.inclusion (Multiplicative.ofAdd x)) = 1 := by
    have hm : D.inclusion (Multiplicative.ofAdd x) ∈ D.ratio.ker := by
      rw [← D.exact]
      exact ⟨Multiplicative.ofAdd x, rfl⟩
    exact hm
  rw [G.crossAction_formula _ A hA hc, hv, hr]
  apply Prod.ext
  · ext i
    simp [crossAffine, affine, embedding]
  · simp [crossAffine, affine]

theorem actual_ratio_kernel_properly_discontinuous
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (hdisc : DiscreteTopology (translationLattice F D.L).toIntSubmodule)
    (G : GeometryData F hF S D) :
    letI := homeomorphAction G.crossAction
    ProperlyDiscontinuousSMul D.ratio.ker (Cross F) := by
  letI := homeomorphAction G.crossAction
  let N := translationLattice F D.L
  letI : DiscreteTopology N := hdisc
  have hd : ProperlyDiscontinuousVAdd N (Horizontal F) :=
    N.properlyDiscontinuousVAdd_of_tendsto_cofinite
      (N.tendsto_coe_cofinite_of_isDiscrete (isDiscrete_iff_discreteTopology.mpr inferInstance))
  constructor
  intro K L hK hL
  have hx : ∀ g : D.ratio.ker, ∃ x : D.L, D.inclusion (Multiplicative.ofAdd x) = g.val := by
    intro g
    have hm : g.val ∈ D.inclusion.range := by rw [D.exact]; exact g.property
    obtain ⟨x, hx⟩ := hm
    exact ⟨x.toAdd, hx⟩
  choose x hx using hx
  let b : D.ratio.ker → N := fun g => ⟨embedding F (x g).val, ⟨(x g).val, (x g).property, rfl⟩⟩
  have hb : Function.Injective b := by
    intro g g' h
    apply Subtype.ext
    rw [← hx g, ← hx g']
    congr 1
    apply Subtype.ext
    let i : Fin (KPCuspLogShape.dimension F) := ⟨0, KPCuspLogShape.dimension_pos F hF⟩
    apply (KPCusp.complexPlace F i).embedding.injective
    exact congrArg (fun y : N => y.val i) h
  letI := hd
  have hfin : Set.Finite _ := ProperlyDiscontinuousVAdd.finite_disjoint_inter_image
    (Γ := N) (hK.image continuous_fst) (hL.image continuous_fst)
  apply (Set.Finite.preimage hb.injOn hfin).subset
  rintro g ⟨p, ⟨q, hq, hqp⟩, hp⟩
  refine ⟨p.1, ⟨q.1, ⟨q, hq, rfl⟩, ?_⟩, ⟨p, hp, rfl⟩⟩
  have he := translation_formula F hF S D G (x g) q
  rw [hx g] at he
  have heq : G.crossAction g.val q = p := hqp
  change (b g : Horizontal F) + q.1 = p.1
  rw [heq] at he
  have := congrArg Prod.fst he
  simpa [b, add_comm] using this.symm

theorem actual_cross_action_properly_discontinuous
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (hdisc : DiscreteTopology (translationLattice F D.L).toIntSubmodule)
    (G : GeometryData F hF S D) :
    letI := homeomorphAction G.crossAction
    ProperlyDiscontinuousSMul S (Cross F) := by
  letI := homeomorphAction G.crossAction
  letI : ContinuousConstSMul S (Cross F) := ⟨fun g => (G.crossAction g).continuous⟩
  let Λ := KPCuspLogShape.logLattice F hF D.E D.integralUnits
  let ell := KPCuspLogShape.logarithm F hF D.E D.integralUnits
  letI : DiscreteTopology Λ := KPCuspLogShape.logarithm_discrete F hF D.E D.integralUnits
  let r : D.E →* Multiplicative Λ :=
    { toFun := fun u => Multiplicative.ofAdd ⟨ell (Additive.ofMul u), ⟨Additive.ofMul u, rfl⟩⟩
      map_one' := by apply Multiplicative.toAdd.injective; apply Subtype.ext; exact ell.map_zero
      map_mul' := by intro a b; apply Multiplicative.toAdd.injective; apply Subtype.ext; exact ell.map_add _ _ }
  letI : ProperlyDiscontinuousSMul (Multiplicative Λ) (Shape F) := by
    have hd : ProperlyDiscontinuousVAdd Λ (Shape F) :=
      Λ.toAddSubgroup.properlyDiscontinuousVAdd_of_tendsto_cofinite
        (Λ.toAddSubgroup.tendsto_coe_cofinite_of_isDiscrete (isDiscrete_iff_discreteTopology.mpr inferInstance))
    constructor
    intro K L hK hL
    have hfin : Set.Finite _ := @ProperlyDiscontinuousVAdd.finite_disjoint_inter_image Λ (Shape F) _ _ hd K L hK hL
    apply (Set.Finite.preimage Multiplicative.toAdd.injective.injOn hfin).subset
    rintro u ⟨y, ⟨x, hx, hxy⟩, hy⟩
    refine ⟨y, ⟨x, hx, ?_⟩, hy⟩
    change u.toAdd.val + x = y
    change u.toAdd.val + x = y at hxy
    simpa only [add_comm] using hxy
  letI : MulAction D.E (Shape F) := MulAction.compHom _ r
  letI : ContinuousConstSMul D.E (Shape F) := ⟨fun u => by change Continuous (fun b : Shape F => (r u).toAdd.val + b); fun_prop⟩
  letI : Finite r.ker := by
    let f : r.ker → kernelUnits F hF D.E D.integralUnits := fun u => ⟨u.val, by
      have h := congrArg (fun v : Multiplicative Λ => v.toAdd.val) u.property
      exact h⟩
    letI := G.finite_isotropy
    exact Finite.of_injective f (fun a b h => Subtype.ext (congrArg (fun u : kernelUnits F hF D.E D.integralUnits => u.val) h))
  letI : ProperlyDiscontinuousSMul D.E (Shape F) :=
    properlyDiscontinuous_of_equivariant r id continuous_id (fun _ _ => rfl)
  letI : ProperlyDiscontinuousSMul D.ratio.ker (Cross F) :=
    actual_ratio_kernel_properly_discontinuous F hF S D hdisc G
  apply properlyDiscontinuous_of_equivariant D.ratio Prod.snd continuous_snd
  intro g p
  obtain ⟨A, hA, hc⟩ := D.upper g g.property
  change (G.crossAction g p).2 = ell (Additive.ofMul (D.ratio g)) + p.2
  rw [G.crossAction_formula g A hA hc]
  change p.2 + ell (Additive.ofMul (D.ratio g)) = ell (Additive.ofMul (D.ratio g)) + p.2
  exact add_comm _ _

private theorem actual_group_countable (F : Type*) [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) : Countable S := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := by change Countable (Fin 2 → Fin 2 → F); infer_instance
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Function.Injective.countable Units.val_injective
  letI : Countable (KPCuspArithmetic.PGL2 F) := Function.Surjective.countable Matrix.ProjGenLinGroup.mk_surjective
  infer_instance

theorem actual_fixed_locus_null
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (μ : Measure (Shape F)) [SFinite μ]
    (g : S) (hg : g ≠ 1) :
    (volume.prod μ) {p : Cross F | G.crossAction g p = p} = 0 := by
  let i : Fin (KPCuspLogShape.dimension F) := ⟨0, KPCuspLogShape.dimension_pos F hF⟩
  by_cases hr : D.ratio g = 1
  · have hmem : g ∈ D.inclusion.range := by rw [D.exact]; exact hr
    obtain ⟨x, hx⟩ := hmem
    have hx0 : (x.toAdd : F) ≠ 0 := by
      intro hz
      have he : x = 1 := by apply Multiplicative.toAdd.injective; exact Subtype.ext hz
      apply hg
      rw [← hx, he, map_one]
    obtain ⟨A, hA, hc⟩ := D.upper g g.property
    have hAi : Matrix.ProjGenLinGroup.mk A = (D.inclusion x : KPCuspArithmetic.PGL2 F) := by rw [hA, hx]
    obtain ⟨_, hd, ht⟩ := D.unipotentFormula x.toAdd A hAi
    have hn : A 1 1 ≠ 0 := by
      intro hz
      exact A.det_ne_zero (by simp [Matrix.det_fin_two, hc, hd, hz])
    have hv : A 0 1 / A 1 1 = (x.toAdd : F) := by rw [ht, hd, mul_div_cancel_right₀ _ hn]
    have hempty : {p : Cross F | G.crossAction g p = p} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hi := congrArg (fun q : Cross F => q.1 i) hp
      rw [G.crossAction_formula g A hA hc, hr] at hi
      simp only [crossAffine, affine, embedding, OneMemClass.coe_one, Units.val_one,
        map_one, one_mul] at hi
      rw [hv] at hi
      change (KPCusp.complexPlace F i).embedding 1 * p.1 i +
        (KPCusp.complexPlace F i).embedding (x.toAdd : F) = p.1 i at hi
      simp only [map_one, one_mul] at hi
      have hz : (KPCusp.complexPlace F i).embedding (x.toAdd : F) = 0 := by linear_combination hi
      exact hx0 ((map_eq_zero (KPCusp.complexPlace F i).embedding).mp hz)
    rw [hempty, measure_empty]
  · obtain ⟨A, hA, hc⟩ := D.upper g g.property
    let a : ℂ := embedding F ((D.ratio g : Fˣ) : F) i
    let v : ℂ := embedding F (A 0 1 / A 1 1) i
    have ha : a - 1 ≠ 0 := by
      intro h
      apply hr
      apply Subtype.ext
      apply Units.ext
      apply (KPCusp.complexPlace F i).embedding.injective
      simpa [a, embedding] using sub_eq_zero.mp h
    have hsub : {p : Cross F | G.crossAction g p = p} ⊆
        {x : Horizontal F | x i = -v / (a - 1)} ×ˢ (univ : Set (Shape F)) := by
      intro p hp
      refine ⟨?_, mem_univ _⟩
      have hi := congrArg (fun q : Cross F => q.1 i) hp
      rw [G.crossAction_formula g A hA hc] at hi
      change a * p.1 i + v = p.1 i at hi
      change p.1 i = -v / (a - 1)
      apply (eq_div_iff ha).mpr
      linear_combination hi
    apply measure_mono_null hsub
    rw [Measure.prod_prod]
    have hz : (volume : Measure (Horizontal F)) {x : Horizontal F | x i = -v / (a - 1)} = 0 :=
      Measure.pi_hyperplane (fun _ => (volume : Measure ℂ)) i _
    rw [hz, zero_mul]

theorem actual_cross_action_ae_free
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (μ : Measure (Shape F)) [SFinite μ] :
    ∀ᵐ p ∂(volume.prod μ), ∀ g : S, G.crossAction g p = p → g = 1 := by
  letI : Countable S := actual_group_countable F S
  rw [ae_all_iff]
  intro g
  by_cases hg : g = 1
  · exact Filter.Eventually.of_forall fun p _ => hg
  · have hn : ∀ᵐ p ∂(volume.prod μ), G.crossAction g p ≠ p := by
      rw [ae_iff]
      simpa only [not_not] using actual_fixed_locus_null F hF S D G μ g hg
    exact hn.mono fun p hp he => (hp he).elim

theorem actual_measurable_fundamental_domain
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (hdisc : DiscreteTopology (translationLattice F D.L).toIntSubmodule)
    (hlattice : letI := hdisc; IsZLattice ℝ (translationLattice F D.L).toIntSubmodule)
    (G : GeometryData F hF S D)
    (μ : Measure (Shape F)) [μ.IsAddHaarMeasure] :
    ∃ Ω : Set (Cross F), MeasurableSet Ω ∧
      (letI := homeomorphAction G.crossAction;
       IsFundamentalDomain S Ω (volume.prod μ)) := by
  letI := homeomorphAction G.crossAction
  letI : Countable S := actual_group_countable F S
  letI : ContinuousConstSMul S (Cross F) := ⟨fun g => (G.crossAction g).continuous⟩
  letI : ProperlyDiscontinuousSMul S (Cross F) :=
    actual_cross_action_properly_discontinuous F hF S D hdisc G
  exact measurable_fundamental_domain_of_properly_discontinuous_ae_free
    (volume.prod μ) (actual_cross_action_ae_free F hF S D G μ)

end DedekindZetaZeroFree.KPCuspChart.SectionConstruction

end

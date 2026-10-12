module

public import DedekindZetaZeroFree.Geometry.Cusps.AffineTorusBundles.QuotientCoordinates

@[expose] public section

noncomputable section
open scoped Classical Matrix
open MeasureTheory
namespace DedekindZetaZeroFree.KPCuspChart
private theorem split_upper_action (g : Matrix.GeneralLinearGroup (Fin 2) ℂ)
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

private theorem split_actual_affine_action (F : Type*) [Field F] [NumberField F]
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
  rw [split_upper_action _ hi _ hu ha]
  apply Prod.ext
  · change σ ((D.ratio g : Fˣ) : F) * p.1.1 i + σ (A 0 1) / σ (A 1 1) =
      σ ((D.ratio g : Fˣ) : F) * p.1.1 i + σ (A 0 1 / A 1 1)
    rw [map_div₀]
  · change p.2 + (p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i + Real.log ‖σ _‖ =
      p.2 + ((p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i +
        Real.log ((KPCusp.complexPlace F i) ((D.ratio g : Fˣ) : F)))
    rw [NumberField.InfinitePlace.norm_embedding_eq]
    ring

private theorem split_meanHeight (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) (p : Coordinates F) :
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) (toArch F p) = p.2 := by
  have hb : ∑ i, (p.1.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i = 0 := p.1.2.property
  have hn : (KPCuspLogShape.dimension F : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (KPCuspLogShape.dimension_pos F hF))
  simp only [KPCuspLogShape.meanHeight, toArch, Finset.sum_add_distrib, hb,
    add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ p.2 hn

private theorem split_toArch_injective (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) : Function.Injective (toArch F) := by
  intro p q h
  have ht : p.2 = q.2 := by
    rw [← split_meanHeight F hF p, ← split_meanHeight F hF q, h]
  apply Prod.ext _ ht
  apply Prod.ext
  · funext i
    exact congrArg Prod.fst (congrFun h i)
  · apply Subtype.ext
    funext i
    have he := congrArg Prod.snd (congrFun h i)
    change p.2 + _ = q.2 + _ at he
    rw [ht] at he
    exact add_left_cancel he

private theorem split_cross_action (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (g : S) (p : Coordinates F) :
    (g : KPCuspArithmetic.PGL2 F) • toArch F p = toArch F (G.crossAction g p.1, p.2) := by
  obtain ⟨A, hA, hc⟩ := D.upper g g.property
  change KPCuspSiegel.action F (g : KPCuspArithmetic.PGL2 F) _ = _
  rw [split_actual_affine_action F hF S D g A hA hc p,
    G.crossAction_formula g A hA hc]
  rfl

theorem radial_orbit_relation_iff (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (p q : Coordinates F) :
    totalRelation F S p q ↔ crossRelation F S p.1 q.1 ∧ p.2 = q.2 := by
  change (∃ g : S, g • toArch F q = toArch F p) ↔
    (∃ g : S, g • toArch F (q.1, 0) = toArch F (p.1, 0)) ∧ p.2 = q.2
  constructor
  · rintro ⟨g, hg⟩
    have he := split_toArch_injective F hF ((split_cross_action F hF S D G g q).symm.trans hg)
    refine ⟨⟨g, ?_⟩, (congrArg Prod.snd he).symm⟩
    have hx : G.crossAction g q.1 = p.1 := congrArg Prod.fst he
    exact (split_cross_action F hF S D G g (q.1, 0)).trans
      (congrArg (toArch F) (Prod.ext hx rfl))
  · rintro ⟨⟨g, hg⟩, ht⟩
    have he := split_toArch_injective F hF ((split_cross_action F hF S D G g (q.1, 0)).symm.trans hg)
    refine ⟨g, ?_⟩
    have hx : G.crossAction g q.1 = p.1 := congrArg Prod.fst he
    exact (split_cross_action F hF S D G g q).trans
      (congrArg (toArch F) (Prod.ext hx ht.symm))
end DedekindZetaZeroFree.KPCuspChart
noncomputable section
open scoped Classical
open MeasureTheory
namespace DedekindZetaZeroFree.KPCuspChart
 def quotientRadialEquiv {X Y : Type*} (s : Setoid X) (r : Setoid (X × Y))
    (hr : ∀ p q, r p q ↔ s p.1 q.1 ∧ p.2 = q.2) :
    Quotient s × Y ≃ Quotient r where
  toFun p := Quotient.lift (fun x => Quotient.mk r (x, p.2))
    (fun a b h => Quotient.sound ((hr _ _).mpr ⟨h, rfl⟩)) p.1
  invFun := Quotient.lift (fun p => (Quotient.mk s p.1, p.2))
    (fun a b h => Prod.ext (Quotient.sound ((hr _ _).mp h).1) ((hr _ _).mp h).2)
  left_inv p := by obtain ⟨q, y⟩ := p; induction q using Quotient.inductionOn; rfl
  right_inv p := by induction p using Quotient.inductionOn; rfl

 def quotientRadialHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace Y] (s : Setoid X) (r : Setoid (X × Y))
    (hr : ∀ p q, r p q ↔ s p.1 q.1 ∧ p.2 = q.2) :
    Quotient s × Y ≃ₜ Quotient r where
  toEquiv := quotientRadialEquiv s r hr
  continuous_toFun := isQuotientMap_quotient_mk'.continuous_lift_prod_left
    (show Continuous (fun p : X × Y => Quotient.mk r p) from continuous_quotient_mk')
  continuous_invFun := continuous_quot_lift _
    (continuous_quotient_mk'.comp continuous_fst |>.prodMk continuous_snd)

def radialOrbitHomeomorph (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) : CrossQuotient F S × ℝ ≃ₜ TotalQuotient F S :=
  quotientRadialHomeomorph _ _ (radial_orbit_relation_iff F hF S D G)

@[simp] theorem radialOrbitHomeomorph_mk (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (p : Cross F) (t : ℝ) :
    radialOrbitHomeomorph F hF S D G (Quotient.mk _ p, t) = Quotient.mk _ (p,t) := rfl

def radialHighProductHomeomorph (F : Type*) [Field F] [NumberField F] (T : ℝ) :
    Cross F × Set.Ioi T ≃ₜ {p : Coordinates F // T < p.2} where
  toFun p := ⟨(p.1, p.2.val), p.2.property⟩
  invFun p := (p.val.1, ⟨p.val.2, p.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

def highRadialOrbitHomeomorph (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (T : ℝ) :
    CrossQuotient F S × Set.Ioi T ≃ₜ HighQuotient F S T :=
  letI : LocallyCompactSpace (Set.Ioi T) := isOpen_Ioi.locallyCompactSpace
  let e := radialHighProductHomeomorph F T
  let s := Setoid.comap e (highRelation F S T)
  (quotientRadialHomeomorph (crossRelation F S) s (by
    intro p q
    change totalRelation F S (p.1, p.2.val) (q.1, q.2.val) ↔ _
    rw [radial_orbit_relation_iff F hF S D G]
    exact and_congr_right (fun _ => Subtype.ext_iff.symm))).trans
    (Homeomorph.Quotient.congr e (fun _ _ => Iff.rfl))

@[simp] theorem highRadialOrbitHomeomorph_mk (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (T : ℝ) (p : Cross F) (t : Set.Ioi T) :
    highRadialOrbitHomeomorph F hF S D G T (Quotient.mk _ p, t) =
      Quotient.mk _ ⟨(p,t.val), t.property⟩ := rfl
end DedekindZetaZeroFree.KPCuspChart

namespace DedekindZetaZeroFree.KPCuspChart

end DedekindZetaZeroFree.KPCuspChart

namespace DedekindZetaZeroFree.KPCuspChart
private theorem radial_sigmaFinite_comap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : MeasurableEmbedding f) (ν : Measure Y) [SigmaFinite ν] :
    SigmaFinite (ν.comap f) := by
  apply Measure.sigmaFinite_of_countable (Set.countable_range (fun n : ℕ => f ⁻¹' spanningSets ν n))
  · rintro _ ⟨n, rfl⟩
    rw [hf.comap_apply]
    exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top ν n)
  · simp only [Set.sUnion_range, ← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]

theorem radial_high_coordinate_measure
    (F : Type*) [Field F] [NumberField F] (T : ℝ)
    (μ : Measure (Cross F)) (ν : Measure ℝ) [SFinite μ] [SigmaFinite ν] :
    Measure.map (radialHighProductHomeomorph F T)
      (μ.prod (ν.comap (Subtype.val : Set.Ioi T → ℝ))) =
    (μ.prod ν).comap (Subtype.val : {p : Coordinates F // T < p.2} → Coordinates F) := by
  let a : MeasurableEmbedding (Subtype.val : Set.Ioi T → ℝ) :=
    MeasurableEmbedding.subtype_coe isOpen_Ioi.measurableSet
  let b : MeasurableEmbedding (Subtype.val : {p : Coordinates F // T < p.2} → Coordinates F) :=
    MeasurableEmbedding.subtype_coe (measurableSet_lt measurable_const measurable_snd)
  letI := radial_sigmaFinite_comap _ a ν
  let e := radialHighProductHomeomorph F T
  apply b.map_injective
  rw [Measure.map_map b.measurable e.continuous.measurable, b.map_comap]
  change Measure.map (Prod.map id (Subtype.val : Set.Ioi T → ℝ)) _ = _
  rw [← Measure.map_prod_map _ _ measurable_id a.measurable, Measure.map_id, a.map_comap]
  have he : Set.range (Subtype.val : {p : Coordinates F // T < p.2} → Coordinates F) =
      Set.univ ×ˢ Set.Ioi T := by
    ext p
    simp
  rw [Subtype.range_val, he, ← Measure.prod_restrict, Measure.restrict_univ]

 theorem radial_high_quotient_volume_of_measurable
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (V : SectionData F hF S D G) (T : ℝ)
    (hm : Measurable (highRadialOrbitHomeomorph F hF S D G T)) :
    Measure.map (highRadialOrbitHomeomorph F hF S D G T)
      (V.sectionMeasure.prod (Measure.comap (Subtype.val : Set.Ioi T → ℝ)
        (radialMeasure (KPCuspLogShape.dimension F)))) =
    Measure.map (Quotient.mk (highRelation F S T))
      (Measure.comap (Subtype.val : {p : Coordinates F // T < p.2} → Coordinates F)
        (((volume.prod V.shapeMeasure).prod (radialMeasure (KPCuspLogShape.dimension F))).restrict
          {p : Coordinates F | p.1 ∈ V.fundamentalDomain})) := by
  letI := V.haar_shapeMeasure
  let ν := radialMeasure (KPCuspLogShape.dimension F)
  letI : SigmaFinite ν := by unfold ν radialMeasure; infer_instance
  letI := radial_sigmaFinite_comap (Subtype.val : Set.Ioi T → ℝ)
    (MeasurableEmbedding.subtype_coe isOpen_Ioi.measurableSet) ν
  rw [V.sectionMeasure_formula]
  rw [show ν.comap (Subtype.val : Set.Ioi T → ℝ) =
    Measure.map (id : Set.Ioi T → Set.Ioi T) (ν.comap (Subtype.val : Set.Ioi T → ℝ)) from (Measure.map_id).symm]
  rw [Measure.map_prod_map _ _ measurable_quotient_mk'' measurable_id, Measure.map_map hm (by fun_prop)]
  have hf : (highRadialOrbitHomeomorph F hF S D G T) ∘
      Prod.map (Quotient.mk (crossRelation F S)) (id : Set.Ioi T → Set.Ioi T) =
      (Quotient.mk (highRelation F S T)) ∘ (radialHighProductHomeomorph F T) := by
    funext p
    exact highRadialOrbitHomeomorph_mk F hF S D G T p.1 p.2
  rw [hf, ← Measure.map_map measurable_quotient_mk'' (radialHighProductHomeomorph F T).continuous.measurable,
    radial_high_coordinate_measure]
  rw [Measure.restrict_prod_eq_prod_univ]
  congr 3
  ext p
  simp
end DedekindZetaZeroFree.KPCuspChart

namespace DedekindZetaZeroFree.KPCuspChart
 theorem radial_quotient_volume_of_measurable
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (V : SectionData F hF S D G)
    (hm : Measurable (radialOrbitHomeomorph F hF S D G)) :
    Measure.map (radialOrbitHomeomorph F hF S D G)
      (V.sectionMeasure.prod (radialMeasure (KPCuspLogShape.dimension F))) =
    Measure.map (Quotient.mk (totalRelation F S))
      (((volume.prod V.shapeMeasure).prod (radialMeasure (KPCuspLogShape.dimension F))).restrict
        {p : Coordinates F | p.1 ∈ V.fundamentalDomain}) := by
  letI := V.haar_shapeMeasure
  letI : SigmaFinite (radialMeasure (KPCuspLogShape.dimension F)) := by
    unfold radialMeasure
    infer_instance
  rw [V.sectionMeasure_formula]
  rw [show radialMeasure (KPCuspLogShape.dimension F) =
    Measure.map (id : ℝ → ℝ) (radialMeasure (KPCuspLogShape.dimension F)) from (Measure.map_id).symm]
  rw [Measure.map_prod_map _ _ measurable_quotient_mk'' measurable_id, Measure.map_map hm (by fun_prop)]
  simp only [Measure.map_id]
  have hf : (radialOrbitHomeomorph F hF S D G) ∘
      Prod.map (Quotient.mk (crossRelation F S)) (id : ℝ → ℝ) =
      Quotient.mk (totalRelation F S) := by
    funext p
    exact radialOrbitHomeomorph_mk F hF S D G p.1 p.2
  rw [hf, Measure.restrict_prod_eq_prod_univ]
  congr 2
  ext p
  simp
end DedekindZetaZeroFree.KPCuspChart

namespace DedekindZetaZeroFree.KPCuspChart
 theorem radial_disintegration_of_borel_quotients
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (V : SectionData F hF S D G)
    [BorelSpace (CrossQuotient F S × ℝ)]
    [BorelSpace (TotalQuotient F S)]
    [∀ T : ℝ, BorelSpace (CrossQuotient F S × Set.Ioi T)]
    [∀ T : ℝ, BorelSpace (HighQuotient F S T)] :
    Nonempty (RadialData F hF S D G V) := by
  exact ⟨{
    radialPresentation := radialOrbitHomeomorph F hF S D G
    radialPresentation_formula := radialOrbitHomeomorph_mk F hF S D G
    quotientVolume_formula := radial_quotient_volume_of_measurable F hF S D G V
      (radialOrbitHomeomorph F hF S D G).continuous.measurable
    highPresentation := highRadialOrbitHomeomorph F hF S D G
    highPresentation_formula := highRadialOrbitHomeomorph_mk F hF S D G
    highVolume_formula := fun T => radial_high_quotient_volume_of_measurable F hF S D G V T
      (highRadialOrbitHomeomorph F hF S D G T).continuous.measurable
  }⟩
end DedekindZetaZeroFree.KPCuspChart

namespace DedekindZetaZeroFree.KPCuspChart
open scoped Pointwise
open Function
private theorem orbit_section_embedding {X H : Type*} [Group H] [Countable H]
    [MeasurableSpace X] [MulAction H X] [MeasurableConstSMul H X]
    (s : Set X) (hs : MeasurableSet s)
    (hd : Pairwise (Disjoint on fun g : H => g • s)) :
    MeasurableEmbedding (fun x : s => Quotient.mk (MulAction.orbitRel H X) x.val) := by
  refine ⟨?_, measurable_quotient_mk''.comp measurable_subtype_coe, ?_⟩
  · intro x y h
    obtain ⟨g, hg⟩ := Quotient.exact h
    have hg1 : g = 1 := by
      by_contra hn
      have hx : x.val ∈ g • s := ⟨y.val, y.property, hg⟩
      have hy : x.val ∈ (1 : H) • s := by simpa using x.property
      exact Set.disjoint_left.mp (hd hn) hx hy
    apply Subtype.ext
    simpa [hg1] using hg.symm
  · intro t ht
    apply measurableSet_quotient.mpr
    have he : Quotient.mk (MulAction.orbitRel H X) ⁻¹'
        ((fun x : s => Quotient.mk (MulAction.orbitRel H X) x.val) '' t) =
        ⋃ g : H, g • ((Subtype.val : s → X) '' t) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
      constructor
      · rintro ⟨y, hy, he⟩
        obtain ⟨g, hg⟩ := Quotient.exact he.symm
        exact ⟨g, y.val, ⟨y, hy, rfl⟩, hg⟩
      · rintro ⟨g, y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, Quotient.sound ⟨g⁻¹, by simp⟩⟩
    rw [he]
    exact MeasurableSet.iUnion fun g =>
      ((MeasurableEmbedding.subtype_coe hs).measurableSet_image.mpr ht).const_smul g
private theorem orbit_ae_section {X H : Type*} [Group H] [Countable H]
    [MeasurableSpace X] [Nonempty X] [MulAction H X] [MeasurableConstSMul H X]
    (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (hfd : IsFundamentalDomain H s μ) :
    ∃ k : Quotient (MulAction.orbitRel H X) → X, Measurable k ∧
      ∀ᵐ z ∂Measure.map (Quotient.mk (MulAction.orbitRel H X)) (μ.restrict s),
        Quotient.mk (MulAction.orbitRel H X) (k z) = z := by
  let s0 := fundamentalInterior H s
  have hs0 : MeasurableSet s0 := hs.diff (MeasurableSet.iUnion fun g =>
    MeasurableSet.iUnion fun _ : g ≠ 1 => hs.const_smul g)
  let q : X → Quotient (MulAction.orbitRel H X) := Quotient.mk _
  let q0 : s0 → Quotient (MulAction.orbitRel H X) := fun x => q x.val
  have hq0 : MeasurableEmbedding q0 := orbit_section_embedding s0 hs0
    (pairwise_disjoint_fundamentalInterior H s)
  obtain ⟨k, hk, hke⟩ := hq0.exists_measurable_extend measurable_subtype_coe (fun _ => inferInstance)
  refine ⟨k, hk, ?_⟩
  have he : ∀ᵐ x ∂μ.restrict s, x ∈ s0 := by
    have hn : ∀ᵐ x ∂μ, x ∉ fundamentalFrontier H s := by
      rw [ae_iff]
      convert hfd.measure_fundamentalFrontier using 2
      ext x
      simp
    filter_upwards [ae_restrict_mem hs, ae_restrict_of_ae hn] with x hx hnx
    exact ⟨hx, fun ht => hnx ⟨hx, ht⟩⟩
  have hr : ∀ᵐ z ∂Measure.map q (μ.restrict s), z ∈ Set.range q0 := by
    apply (ae_map_iff measurable_quotient_mk''.aemeasurable hq0.measurableSet_range).mpr
    exact he.mono fun x hx => ⟨⟨x, hx⟩, rfl⟩
  filter_upwards [hr] with z hz
  obtain ⟨x, rfl⟩ := hz
  have he := congrFun hke x
  change k (q0 x) = x.val at he
  rw [he]
private theorem split_crossRelation_eq (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) :
    letI := homeomorphAction G.crossAction
    crossRelation F S = MulAction.orbitRel S (Cross F) := by
  letI := homeomorphAction G.crossAction
  apply Setoid.ext
  intro p q
  change (∃ g : S, g • toArch F (q,0) = toArch F (p,0)) ↔
    (∃ g : S, G.crossAction g q = p)
  constructor
  · rintro ⟨g, hg⟩
    have he := split_toArch_injective F hF ((split_cross_action F hF S D G g (q,0)).symm.trans hg)
    exact ⟨g, congrArg Prod.fst he⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, (split_cross_action F hF S D G g (q,0)).trans
      (congrArg (toArch F) (Prod.ext hg rfl))⟩

private theorem split_cross_ae_section (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (V : SectionData F hF S D G) :
    ∃ k : CrossQuotient F S → Cross F, Measurable k ∧
      ∀ᵐ z ∂V.sectionMeasure, Quotient.mk (crossRelation F S) (k z) = z := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := by
    unfold Matrix
    infer_instance
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Function.Injective.countable (f := fun g => (g : Matrix (Fin 2) (Fin 2) F)) Units.val_injective
  letI : Countable (KPCuspArithmetic.PGL2 F) := by
    unfold KPCuspArithmetic.PGL2 Matrix.ProjGenLinGroup
    exact Function.Surjective.countable (Quotient.mk_surjective :
      Function.Surjective (Quotient.mk (QuotientGroup.leftRel _)))
  letI := homeomorphAction G.crossAction
  letI : MeasurableConstSMul S (Cross F) := ⟨fun g => (G.crossAction g).continuous.measurable⟩
  rw [V.sectionMeasure_formula]
  have he := split_crossRelation_eq F hF S D G
  unfold CrossQuotient
  rw [he]
  exact orbit_ae_section (volume.prod V.shapeMeasure) V.fundamentalDomain
    V.measurable_fundamentalDomain V.isFundamentalDomain

private theorem split_radial_aemeasurable (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (V : SectionData F hF S D G) :
    AEMeasurable (radialOrbitHomeomorph F hF S D G)
      (V.sectionMeasure.prod (radialMeasure (KPCuspLogShape.dimension F))) := by
  obtain ⟨k, hk, he⟩ := split_cross_ae_section F hF S D G V
  let ν := radialMeasure (KPCuspLogShape.dimension F)
  letI : SigmaFinite ν := by unfold ν radialMeasure; infer_instance
  have hm : Measurable (fun p : CrossQuotient F S × ℝ =>
      Quotient.mk (totalRelation F S) (k p.1, p.2)) :=
    measurable_quotient_mk''.comp ((hk.comp measurable_fst).prodMk measurable_snd)
  apply hm.aemeasurable.congr
  have hep := (Measure.quasiMeasurePreserving_fst (μ := V.sectionMeasure) (ν := ν)).ae he
  filter_upwards [hep] with p hp
  change Quotient.mk (totalRelation F S) (k p.1, p.2) = _
  rw [← radialOrbitHomeomorph_mk F hF S D G, hp]

private theorem split_high_aemeasurable (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (V : SectionData F hF S D G) (T : ℝ) :
    AEMeasurable (highRadialOrbitHomeomorph F hF S D G T)
      (V.sectionMeasure.prod (Measure.comap (Subtype.val : Set.Ioi T → ℝ)
        (radialMeasure (KPCuspLogShape.dimension F)))) := by
  obtain ⟨k, hk, he⟩ := split_cross_ae_section F hF S D G V
  let ν := radialMeasure (KPCuspLogShape.dimension F)
  letI : SigmaFinite ν := by unfold ν radialMeasure; infer_instance
  letI := radial_sigmaFinite_comap (Subtype.val : Set.Ioi T → ℝ)
    (MeasurableEmbedding.subtype_coe isOpen_Ioi.measurableSet) ν
  have hm : Measurable (fun p : CrossQuotient F S × Set.Ioi T =>
      Quotient.mk (highRelation F S T)
        ((radialHighProductHomeomorph F T) (k p.1, p.2))) :=
    measurable_quotient_mk''.comp ((radialHighProductHomeomorph F T).continuous.measurable.comp
      ((hk.comp measurable_fst).prodMk measurable_snd))
  apply hm.aemeasurable.congr
  have hep := (Measure.quasiMeasurePreserving_fst (μ := V.sectionMeasure)
    (ν := ν.comap (Subtype.val : Set.Ioi T → ℝ))).ae he
  filter_upwards [hep] with p hp
  change Quotient.mk (highRelation F S T) ⟨(k p.1, p.2.val), p.2.property⟩ = _
  rw [← highRadialOrbitHomeomorph_mk F hF S D G, hp]

private theorem split_radial_volume (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (V : SectionData F hF S D G) :
    Measure.map (radialOrbitHomeomorph F hF S D G)
      (V.sectionMeasure.prod (radialMeasure (KPCuspLogShape.dimension F))) =
    Measure.map (Quotient.mk (totalRelation F S))
      (((volume.prod V.shapeMeasure).prod (radialMeasure (KPCuspLogShape.dimension F))).restrict
        {p : Coordinates F | p.1 ∈ V.fundamentalDomain}) := by
  letI := V.haar_shapeMeasure
  let ν := radialMeasure (KPCuspLogShape.dimension F)
  letI : SigmaFinite ν := by unfold ν radialMeasure; infer_instance
  let μ := (volume.prod V.shapeMeasure).restrict V.fundamentalDomain
  have hp : V.sectionMeasure.prod ν =
      Measure.map (Prod.map (Quotient.mk (crossRelation F S)) (id : ℝ → ℝ)) (μ.prod ν) := by
    rw [V.sectionMeasure_formula]
    simpa [μ] using Measure.map_prod_map μ ν measurable_quotient_mk'' measurable_id
  have hm := split_radial_aemeasurable F hF S D G V
  change AEMeasurable _ (V.sectionMeasure.prod ν) at hm
  change Measure.map _ (V.sectionMeasure.prod ν) = _
  rw [hp] at hm ⊢
  rw [hm.map_map_of_aemeasurable (measurable_quotient_mk''.prodMap measurable_id).aemeasurable]
  have hf : (radialOrbitHomeomorph F hF S D G) ∘
      Prod.map (Quotient.mk (crossRelation F S)) (id : ℝ → ℝ) =
      Quotient.mk (totalRelation F S) := by
    funext p
    exact radialOrbitHomeomorph_mk F hF S D G p.1 p.2
  rw [hf]
  change Measure.map _ (((volume.prod V.shapeMeasure).restrict V.fundamentalDomain).prod ν) = _
  rw [Measure.restrict_prod_eq_prod_univ]
  congr 2
  ext p
  simp

private theorem split_high_volume (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (V : SectionData F hF S D G) (T : ℝ) :
    Measure.map (highRadialOrbitHomeomorph F hF S D G T)
      (V.sectionMeasure.prod (Measure.comap (Subtype.val : Set.Ioi T → ℝ)
        (radialMeasure (KPCuspLogShape.dimension F)))) =
    Measure.map (Quotient.mk (highRelation F S T))
      (Measure.comap (Subtype.val : {p : Coordinates F // T < p.2} → Coordinates F)
        (((volume.prod V.shapeMeasure).prod (radialMeasure (KPCuspLogShape.dimension F))).restrict
          {p : Coordinates F | p.1 ∈ V.fundamentalDomain})) := by
  letI := V.haar_shapeMeasure
  let ν := radialMeasure (KPCuspLogShape.dimension F)
  letI : SigmaFinite ν := by unfold ν radialMeasure; infer_instance
  let νT := ν.comap (Subtype.val : Set.Ioi T → ℝ)
  letI : SigmaFinite νT := radial_sigmaFinite_comap _
    (MeasurableEmbedding.subtype_coe isOpen_Ioi.measurableSet) ν
  let μ := (volume.prod V.shapeMeasure).restrict V.fundamentalDomain
  have hp : V.sectionMeasure.prod νT =
      Measure.map (Prod.map (Quotient.mk (crossRelation F S)) (id : Set.Ioi T → Set.Ioi T))
        (μ.prod νT) := by
    rw [V.sectionMeasure_formula]
    simpa [μ] using Measure.map_prod_map μ νT measurable_quotient_mk'' measurable_id
  have hm := split_high_aemeasurable F hF S D G V T
  change AEMeasurable _ (V.sectionMeasure.prod νT) at hm
  change Measure.map _ (V.sectionMeasure.prod νT) = _
  rw [hp] at hm ⊢
  rw [hm.map_map_of_aemeasurable (measurable_quotient_mk''.prodMap measurable_id).aemeasurable]
  have hf : (highRadialOrbitHomeomorph F hF S D G T) ∘
      Prod.map (Quotient.mk (crossRelation F S)) (id : Set.Ioi T → Set.Ioi T) =
      (Quotient.mk (highRelation F S T)) ∘ (radialHighProductHomeomorph F T) := by
    funext p
    exact highRadialOrbitHomeomorph_mk F hF S D G T p.1 p.2
  rw [hf, ← Measure.map_map measurable_quotient_mk'' (radialHighProductHomeomorph F T).continuous.measurable,
    radial_high_coordinate_measure]
  change Measure.map _ (Measure.comap _ (μ.prod ν)) = _
  change Measure.map _ (Measure.comap _ (((volume.prod V.shapeMeasure).restrict V.fundamentalDomain).prod ν)) = _
  rw [Measure.restrict_prod_eq_prod_univ]
  congr 3
  ext p
  simp

 theorem radial_disintegration_of_separated_quotient
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (V : SectionData F hF S D G)
    [T0Space (CrossQuotient F S)] [SecondCountableTopology (CrossQuotient F S)] :
    Nonempty (RadialData F hF S D G V) := by
  letI : T0Space (TotalQuotient F S) := (radialOrbitHomeomorph F hF S D G).t0Space
  letI : SecondCountableTopology (TotalQuotient F S) := (radialOrbitHomeomorph F hF S D G).symm.secondCountableTopology
  letI (T : ℝ) : T0Space (HighQuotient F S T) := (highRadialOrbitHomeomorph F hF S D G T).t0Space
  letI (T : ℝ) : SecondCountableTopology (HighQuotient F S T) := (highRadialOrbitHomeomorph F hF S D G T).symm.secondCountableTopology
  letI (T : ℝ) : PolishSpace {p : Coordinates F // T < p.2} :=
    (isOpen_lt continuous_const continuous_snd).polishSpace
  letI (T : ℝ) : BorelSpace (CrossQuotient F S × Set.Ioi T) := inferInstance
  letI (T : ℝ) : BorelSpace (HighQuotient F S T) := inferInstance
  exact radial_disintegration_of_borel_quotients F hF S D G V
end DedekindZetaZeroFree.KPCuspChart

namespace DedekindZetaZeroFree.KPCuspChart

theorem radial_quotient_disintegration
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (G : GeometryData F hF S D) (V : SectionData F hF S D G) :
    Nonempty (RadialData F hF S D G V) := by
  exact ⟨{
    radialPresentation := radialOrbitHomeomorph F hF S D G
    radialPresentation_formula := radialOrbitHomeomorph_mk F hF S D G
    quotientVolume_formula := split_radial_volume F hF S D G V
    highPresentation := highRadialOrbitHomeomorph F hF S D G
    highPresentation_formula := highRadialOrbitHomeomorph_mk F hF S D G
    highVolume_formula := split_high_volume F hF S D G V
  }⟩

end DedekindZetaZeroFree.KPCuspChart

end
end

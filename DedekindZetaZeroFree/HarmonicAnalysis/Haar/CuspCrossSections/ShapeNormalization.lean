module

public import DedekindZetaZeroFree.Geometry.Cusps.AffineTorusBundles.QuotientCoordinates

@[expose] public section

noncomputable section
open scoped Classical
open MeasureTheory

namespace DedekindZetaZeroFree.KPCuspChart.SectionConstruction

 def shapeEquiv (d : ℕ) : (Fin d → ℝ) ≃ₗ[ℝ] KPCuspLogShape.hyperplane (d+1) where
  toFun b := ⟨KPArch.shape d b, by
    change ∑ i, KPArch.shape d b i = 0
    simp [KPArch.shape, Fin.sum_univ_castSucc]⟩
  invFun b := fun i => b.val i.castSucc
  left_inv b := by funext i; simp [KPArch.shape]
  right_inv b := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hb := b.property
      change ∑ i, b.val i = 0 at hb
      rw [Fin.sum_univ_castSucc] at hb
      simp only [KPArch.shape, Fin.snoc_last]
      linarith
    · simp [KPArch.shape]
  map_add' b c := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [KPArch.shape, Finset.sum_add_distrib, add_comm]
  map_smul' c b := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [KPArch.shape, Finset.mul_sum]

private theorem normalized_succ (d : ℕ) :
    ∃ μ : Measure (KPCuspLogShape.hyperplane (d+1)), μ.IsAddHaarMeasure ∧
      Measure.map (fun p : ((Fin (d+1) → ℂ) × KPCuspLogShape.hyperplane (d+1)) × ℝ =>
        fun i => (p.1.1 i, p.2 + p.1.2.val i))
        ((volume.prod μ).prod (radialMeasure (d+1))) = KPArch.hyperbolicVolume (d+1) := by
  let c := ENNReal.ofReal (d+1 : ℝ)
  let e := (shapeEquiv d).toContinuousLinearEquiv
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  letI : (c • (volume : Measure (Fin d → ℝ))).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul volume hc hct
  let μ := Measure.map e (c • (volume : Measure (Fin d → ℝ)))
  haveI : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map _
  refine ⟨μ, inferInstance, ?_⟩
  have he : MeasurePreserving e (c • (volume : Measure (Fin d → ℝ))) μ :=
    ⟨e.continuous.measurable, rfl⟩
  let ρ := radialMeasure (d+1)
  haveI : SFinite ρ := by dsimp [ρ, radialMeasure]; infer_instance
  have hs := (MeasurePreserving.id (volume : Measure (Fin (d+1) → ℂ))).prod
    (Measure.measurePreserving_swap (μ := ρ) (ν := c • (volume : Measure (Fin d → ℝ))))
  have ha := (measurePreserving_prodAssoc (volume : Measure (Fin (d+1) → ℂ))
    (c • (volume : Measure (Fin d → ℝ))) ρ).symm
  have hp := ((MeasurePreserving.id (volume : Measure (Fin (d+1) → ℂ))).prod he).prod
    (MeasurePreserving.id ρ)
  have hj := hp.comp (ha.comp hs)
  rw [← hj.map_eq]
  have hf : Measurable (fun p : ((Fin (d+1) → ℂ) × KPCuspLogShape.hyperplane (d+1)) × ℝ =>
      fun i => (p.1.1 i, p.2 + p.1.2.val i)) := by
    apply measurable_pi_lambda
    intro i
    exact ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.add ((measurable_pi_apply i).comp
        (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))))
  rw [Measure.map_map hf hj.measurable]
  have hsource : (volume : Measure (Fin (d+1) → ℂ)).prod
      (ρ.prod (c • (volume : Measure (Fin d → ℝ)))) =
      (volume : Measure (KPArch.SplitSpace d)).withDensity (fun p =>
        ENNReal.ofReal ((d+1 : ℝ) * Real.exp (-2 * (d+1 : ℝ) * p.2.1))) := by
    dsimp [ρ, radialMeasure]
    rw [Measure.prod_smul_right, Measure.prod_smul_right]
    rw [prod_withDensity_left (by fun_prop), prod_withDensity_right (by fun_prop)]
    rw [← withDensity_smul _ (by fun_prop)]
    congr 1
    ext p
    dsimp [c]
    rw [ENNReal.ofReal_mul (by positivity)]
    simp
  rw [hsource]
  rw [← KPArch.hyperbolicVolume_split d]
  congr 1

theorem normalized_shape_haar
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) :
    ∃ μ : Measure (Shape F), μ.IsAddHaarMeasure ∧
      Measure.map (toArch F)
        ((volume.prod μ).prod (radialMeasure (KPCuspLogShape.dimension F))) =
        KPArch.hyperbolicVolume (KPCuspLogShape.dimension F) := by
  have hn := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank F
  have hp := Module.finrank_pos (R := ℚ) (M := F)
  have hd : 0 < KPCuspLogShape.dimension F := by
    dsimp [KPCuspLogShape.dimension]
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  unfold toArch
  change ∃ μ : Measure (KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F)),
    μ.IsAddHaarMeasure ∧
      Measure.map (fun p : ((Fin (KPCuspLogShape.dimension F) → ℂ) ×
        KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F)) × ℝ =>
        fun i => (p.1.1 i, p.2 + p.1.2.val i))
        ((volume.prod μ).prod (radialMeasure (KPCuspLogShape.dimension F))) =
        KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)
  rw [hd]
  exact normalized_succ d

end DedekindZetaZeroFree.KPCuspChart.SectionConstruction

end

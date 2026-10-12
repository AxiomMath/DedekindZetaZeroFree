module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspDisintegration.WeightedSections

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.KPMsFixedHaar.RadiusShift

open _root_.DedekindZetaZeroFree.KPMsFixedHaar.AllLevelGeometry renaming coordinate_transition → coordinate_transition

variable {F : Type} [Field F] [NumberField F]

 def logRatio (u : Fˣ) : ℝ :=
  ∑ i : Fin (KPCuspLogShape.dimension F),
    Real.log ((KPCusp.complexPlace F i) (u : F))

 def radiusMultiplier (u : Fˣ) : ℝ := Real.exp (2 * logRatio u)

 theorem radiusMultiplier_pos (u : Fˣ) : 0 < radiusMultiplier u :=
  Real.exp_pos _

private theorem radiusMultiplier_eq_prod (u : Fˣ) :
    radiusMultiplier u = ∏ i : Fin (KPCuspLogShape.dimension F),
      ‖(KPCusp.complexPlace F i).embedding (u : F)‖ ^ 2 := by
  unfold radiusMultiplier logRatio
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, Real.exp_nat_mul,
    Real.exp_sum, Finset.prod_pow]
  apply congrArg (fun x : ℝ => x ^ 2)
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.exp_log ((KPCusp.complexPlace F i).pos_iff.mpr (Units.ne_zero u)),
    NumberField.InfinitePlace.norm_embedding_eq]

 def shapeShift (hd : 0 < KPCuspLogShape.dimension F) (u : Fˣ) :
    KPCuspCharts.Shape F :=
  ⟨fun i => Real.log ((KPCusp.complexPlace F i) (u : F)) -
    logRatio u / (KPCuspLogShape.dimension F : ℝ), by
    have hd0 : (KPCuspLogShape.dimension F : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hd)
    change (∑ i : Fin (KPCuspLogShape.dimension F),
      (Real.log ((KPCusp.complexPlace F i) (u : F)) -
        logRatio u / (KPCuspLogShape.dimension F : ℝ))) = 0
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    change logRatio u - (KPCuspLogShape.dimension F : ℝ) *
      (logRatio u / (KPCuspLogShape.dimension F : ℝ)) = 0
    field_simp
    ring⟩

 def crossCoordinate (hd : 0 < KPCuspLogShape.dimension F)
    (u : Fˣ) (v : F) (p : KPCuspCharts.Cross F) : KPCuspCharts.Cross F :=
  (fun i => (KPCusp.complexPlace F i).embedding (u : F) * p.1 i +
    (KPCusp.complexPlace F i).embedding v, p.2 + shapeShift hd u)

open _root_.DedekindZetaZeroFree.KPCuspCharts renaming upper_action → upper_action

 theorem crossCoordinate_action
    (hd : 0 < KPCuspLogShape.dimension F)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (u : Fˣ)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (p : KPCuspCharts.Cross F) (t : ℝ) :
    Matrix.ProjGenLinGroup.mk A • KPCuspCharts.toArch F (p,t) =
      KPCuspCharts.toArch F
        (crossCoordinate hd u (A 0 1 / A 1 1) p,
          t + logRatio u / (KPCuspLogShape.dimension F : ℝ)) := by
  change KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk A) _ = _
  rw [KPCuspSiegel.action_mk]
  funext i
  let w := KPCusp.complexPlace F i
  have hz : (Matrix.GeneralLinearGroup.map w.embedding A) 1 0 = 0 := by
    change w.embedding ((A : Matrix (Fin 2) (Fin 2) F) 1 0) = 0
    rw [hA, map_zero]
  have hratio : (Matrix.GeneralLinearGroup.map w.embedding A) 0 0 =
      w.embedding (u : F) * (Matrix.GeneralLinearGroup.map w.embedding A) 1 1 := by
    change w.embedding ((A : Matrix (Fin 2) (Fin 2) F) 0 0) = _
    rw [hr, map_mul]
    rfl
  change KPArch.action (Matrix.GeneralLinearGroup.map w.embedding A) _ = _
  rw [upper_action _ hz _ ((map_ne_zero _).mpr (Units.ne_zero u)) hratio]
  apply Prod.ext
  · simp [KPCuspCharts.toArch, crossCoordinate, Matrix.GeneralLinearGroup.map,
      Matrix.map_apply, map_div₀, w]
  · simp only [KPCuspCharts.toArch, crossCoordinate, shapeShift,
      Submodule.coe_add, Pi.add_apply, NumberField.InfinitePlace.norm_embedding_eq]
    change t + (p.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i +
      Real.log (w (u : F)) =
        (t + logRatio u / (KPCuspLogShape.dimension F : ℝ)) +
          ((p.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i +
            (Real.log (w (u : F)) - logRatio u / (KPCuspLogShape.dimension F : ℝ)))
    ring

open _root_.DedekindZetaZeroFree.KPCuspChart.SectionConstruction renaming horizontalLinear → horizontalLinear
open _root_.DedekindZetaZeroFree.KPCuspChart.SectionConstruction renaming horizontal_det → horizontal_det
open MeasureTheory
open scoped ENNReal

private theorem horizontal_map_volume (u : Fˣ) (v : F) :
    Measure.map (fun x : KPCuspCharts.Horizontal F => fun i =>
      (KPCusp.complexPlace F i).embedding (u : F) * x i +
        (KPCusp.complexPlace F i).embedding v) volume =
      ENNReal.ofReal (radiusMultiplier u)⁻¹ • volume := by
  let a := fun i : Fin (KPCuspLogShape.dimension F) =>
    (KPCusp.complexPlace F i).embedding (u : F)
  have hd : (horizontalLinear a).det = radiusMultiplier u := by
    rw [horizontal_det, radiusMultiplier_eq_prod]
  have hm : Measure.map (horizontalLinear a) volume =
      ENNReal.ofReal (radiusMultiplier u)⁻¹ • volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      (by rw [hd]; exact (radiusMultiplier_pos u).ne'), hd,
      abs_of_pos (inv_pos.mpr (radiusMultiplier_pos u)),
      ENNReal.ofReal_inv_of_pos (radiusMultiplier_pos u)]
  have ht : (fun x : KPCuspCharts.Horizontal F => fun i =>
      (KPCusp.complexPlace F i).embedding (u : F) * x i +
        (KPCusp.complexPlace F i).embedding v) =
      (fun x : KPCuspCharts.Horizontal F => x + KPCuspCharts.embedding F v) ∘
        horizontalLinear a := rfl
  rw [ht, ← Measure.map_map (by fun_prop)
    (horizontalLinear a).continuous_of_finiteDimensional.measurable,
    hm, Measure.map_smul _ (by fun_prop), map_add_right_eq_self]

private theorem logHeight_scaled (hd : 0 < KPCuspLogShape.dimension F)
    (u : Fˣ) (r : ℝ) (hr : 0 < r) :
    logHeight (F := F) (radiusMultiplier u * r) =
      logHeight (F := F) r + logRatio u / (KPCuspLogShape.dimension F : ℝ) := by
  have hd0 : (KPCuspLogShape.dimension F : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  unfold logHeight radiusMultiplier
  rw [Real.log_mul (Real.exp_pos _).ne' hr.ne', Real.log_exp]
  field_simp
  ring

open _root_.DedekindZetaZeroFree.KPMsFixedHaar.PinnedRadialCharts renaming actual_coordinate_relation → actual_coordinate_relation

 def crossTransition
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S T : Subgroup (KPCuspArithmetic.PGL2 F)}
    {DS : KPCuspCharts.ParabolicData F S} {DT : KPCuspCharts.ParabolicData F T}
    (GS : KPCuspCharts.ChartOutput F hF S DS)
    (GT : KPCuspCharts.ChartOutput F hF T DT)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (u : Fˣ)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (h : S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom ≤ T) :
    KPCuspCharts.CrossQuotient F S → KPCuspCharts.CrossQuotient F T :=
  Quotient.lift (fun p => Quotient.mk _
    (crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1) p)) (by
    intro p q hpq
    have hsource : KPCuspCharts.totalRelation F S (p,0) (q,0) := by
      obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hpq)
      exact ⟨g,hg⟩
    have htarget : KPCuspCharts.totalRelation F T
        (crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1) p,
          logRatio u / (KPCuspLogShape.dimension F : ℝ))
        (crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1) q,
          logRatio u / (KPCuspLogShape.dimension F : ℝ)) := by
      obtain ⟨g,hg⟩ := hsource
      refine ⟨⟨Matrix.ProjGenLinGroup.mk A * g.val * (Matrix.ProjGenLinGroup.mk A)⁻¹,
        h ⟨g.val,g.property,rfl⟩⟩, ?_⟩
      rw [← zero_add (logRatio u / (KPCuspLogShape.dimension F : ℝ))]
      rw [← crossCoordinate_action GS.positive_dimension A hA u hr,
        ← crossCoordinate_action GS.positive_dimension A hA u hr]
      change (Matrix.ProjGenLinGroup.mk A * g.val * (Matrix.ProjGenLinGroup.mk A)⁻¹) •
        (Matrix.ProjGenLinGroup.mk A • KPCuspCharts.toArch F (q,0)) = _
      simp only [mul_smul, inv_smul_smul]
      exact congrArg (fun x => Matrix.ProjGenLinGroup.mk A • x) hg
    obtain ⟨g,hg⟩ := (actual_coordinate_relation GT _ _).mp htarget
    have he := congrArg Prod.fst hg
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    have hh : KPCuspCharts.totalRelation F T
        (crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1) p,0)
        (crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1) q,0) :=
      (actual_coordinate_relation GT _ _).mpr ⟨g, Prod.ext he rfl⟩
    obtain ⟨g', hg'⟩ := hh
    exact ⟨g',hg'⟩)

private theorem crossTransition_continuous
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S T : Subgroup (KPCuspArithmetic.PGL2 F)}
    {DS : KPCuspCharts.ParabolicData F S} {DT : KPCuspCharts.ParabolicData F T}
    (GS : KPCuspCharts.ChartOutput F hF S DS)
    (GT : KPCuspCharts.ChartOutput F hF T DT)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (u : Fˣ)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (h : S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom ≤ T) :
    Continuous (crossTransition GS GT A hA u hr h) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  apply continuous_quotient_mk'.comp
  exact (continuous_pi fun i => (continuous_const.mul
    ((continuous_apply i).comp continuous_fst)).add continuous_const).prodMk
      (continuous_snd.add continuous_const)

private theorem sectionShape_mul
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (w : NumberField.InfinitePlace F) (a r : Radius) :
    sectionShape F hF w ⟨a.val * r.val, mul_pos a.property r.property⟩ =
      sectionShape F hF w a + sectionShape F hF w r := by
  apply Subtype.ext
  funext i
  simp only [sectionShape, Real.log_mul a.property.ne' r.property.ne',
    Submodule.coe_add, Pi.add_apply]
  split_ifs <;> ring

 def pinnedCrossCoordinate
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (hd : 0 < KPCuspLogShape.dimension F) (w : NumberField.InfinitePlace F)
    (u : Fˣ) (v : F) (p : KPCuspCharts.Cross F) : KPCuspCharts.Cross F :=
  ((crossCoordinate hd u v p).1,
    (crossCoordinate hd u v p).2 -
      sectionShape F hF w ⟨radiusMultiplier u, radiusMultiplier_pos u⟩)

private theorem pinnedCoordinate_action
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (hd : 0 < KPCuspLogShape.dimension F) (w : NumberField.InfinitePlace F)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (u : Fˣ)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (p : KPCuspCharts.Cross F) (r : Radius) :
    Matrix.ProjGenLinGroup.mk A • KPCuspCharts.toArch F
        ((p.1, p.2 + sectionShape F hF w r), logHeight (F := F) r.val) =
      KPCuspCharts.toArch F
        (((pinnedCrossCoordinate hF hd w u (A 0 1 / A 1 1) p).1,
          (pinnedCrossCoordinate hF hd w u (A 0 1 / A 1 1) p).2 +
            sectionShape F hF w
              ⟨radiusMultiplier u * r.val, mul_pos (radiusMultiplier_pos u) r.property⟩),
          logHeight (F := F) (radiusMultiplier u * r.val)) := by
  rw [crossCoordinate_action hd A hA u hr,
    logHeight_scaled hd u r.val r.property]
  apply congrArg (KPCuspCharts.toArch F)
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · change (p.2 + sectionShape F hF w r) + shapeShift hd u = _
      rw [show (⟨radiusMultiplier u * r.val,
        mul_pos (radiusMultiplier_pos u) r.property⟩ : Radius) =
        ⟨(⟨radiusMultiplier u, radiusMultiplier_pos u⟩ : Radius).val * r.val,
          mul_pos (radiusMultiplier_pos u) r.property⟩ from rfl,
        sectionShape_mul]
      change (p.2 + sectionShape F hF w r) + shapeShift hd u =
        (p.2 + shapeShift hd u - sectionShape F hF w _) +
          (sectionShape F hF w _ + sectionShape F hF w r)
      abel
  · rfl

open _root_.DedekindZetaZeroFree.KPMsFixedHaar.PinnedRadialCharts renaming actual_shape_translation → actual_shape_translation
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.PinnedRadialCharts renaming actual_shape_translation_formula → actual_shape_translation_formula
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.PinnedRadialCharts renaming pinned_cusp_chart → pinned_cusp_chart
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.PinnedRadialCharts renaming pinned_cusp_chart_formula → pinned_cusp_chart_formula
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.AllLevelGeometry renaming actual_full_chart_commutes → actual_full_chart_commutes
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.AllLevelGeometry renaming coordinate_transition_formula → coordinate_transition_formula

 def pinnedCrossTransition
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S T : Subgroup (KPCuspArithmetic.PGL2 F)}
    {DS : KPCuspCharts.ParabolicData F S} {DT : KPCuspCharts.ParabolicData F T}
    (GS : KPCuspCharts.ChartOutput F hF S DS)
    (GT : KPCuspCharts.ChartOutput F hF T DT)
    (w : NumberField.InfinitePlace F)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (u : Fˣ)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (h : S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom ≤ T) :
    KPCuspCharts.CrossQuotient F S → KPCuspCharts.CrossQuotient F T :=
  (actual_shape_translation GT
    (-sectionShape F hF w ⟨radiusMultiplier u, radiusMultiplier_pos u⟩)) ∘
      crossTransition GS GT A hA u hr h

private theorem pinnedCrossTransition_formula
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S T : Subgroup (KPCuspArithmetic.PGL2 F)}
    {DS : KPCuspCharts.ParabolicData F S} {DT : KPCuspCharts.ParabolicData F T}
    (GS : KPCuspCharts.ChartOutput F hF S DS)
    (GT : KPCuspCharts.ChartOutput F hF T DT)
    (w : NumberField.InfinitePlace F)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (u : Fˣ)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (h : S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom ≤ T)
    (p : KPCuspCharts.Cross F) :
    pinnedCrossTransition GS GT w A hA u hr h (Quotient.mk _ p) =
      Quotient.mk _ (pinnedCrossCoordinate hF GS.positive_dimension w u (A 0 1 / A 1 1) p) := by
  unfold pinnedCrossTransition
  simp only [Function.comp_apply]
  change actual_shape_translation GT _ (Quotient.mk _ _) = _
  rw [actual_shape_translation_formula]
  rfl

private theorem pinnedCrossTransition_continuous
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S T : Subgroup (KPCuspArithmetic.PGL2 F)}
    {DS : KPCuspCharts.ParabolicData F S} {DT : KPCuspCharts.ParabolicData F T}
    (GS : KPCuspCharts.ChartOutput F hF S DS)
    (GT : KPCuspCharts.ChartOutput F hF T DT)
    (w : NumberField.InfinitePlace F)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (u : Fˣ)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (h : S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom ≤ T) :
    Continuous (pinnedCrossTransition GS GT w A hA u hr h) :=
  (actual_shape_translation GT _).continuous.comp
    (crossTransition_continuous GS GT A hA u hr h)

private theorem actual_shifted_pinned_chart_commutes
    {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (j : CuspIndex AV) (k : CuspIndex AU)
    (δ : KPCuspArithmetic.PGL2 F)
    (η : KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k.1))
    (ε : rootsOfUnity 3 F) (v : U.toOpenSubgroup)
    (hc : AU.representative k.1 = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ *
      KPCuspGenuineMonodromy.central F ζ hζ ε * AV.representative j.1 * v)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (ht : Matrix.ProjGenLinGroup.mk A = ((AU.cuspAtlas k.1).representative k.2)⁻¹ *
      (η.val⁻¹ * δ) * (AV.cuspAtlas j.1).representative j.2)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (u : Fˣ)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (hpar : (KPCuspArithmetic.conjugatedStabilizer F
      (KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative j.1))
      ((AV.cuspAtlas j.1).cusp j.2) ((AV.cuspAtlas j.1).representative j.2)).map
        (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom ≤
      KPCuspArithmetic.conjugatedStabilizer F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k.1))
        ((AU.cuspAtlas k.1).cusp k.2) ((AU.cuspAtlas k.1).representative k.2))
    (w : NumberField.InfinitePlace F) (YV YU : ℝ) (hYV : 0 < YV) (hYU : 0 < YU)
    (x : KPCuspCharts.CrossQuotient F
      (KPCuspArithmetic.conjugatedStabilizer F
        (KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative j.1))
        ((AV.cuspAtlas j.1).cusp j.2) ((AV.cuspAtlas j.1).representative j.2)))
    (r : Set.Ioi YV) (hhigh : YU < radiusMultiplier u * r.val) :
    P.forget V U h (pinned_cusp_chart AV w YV hYV (⟨j,x⟩,r)) =
      pinned_cusp_chart AU w YU hYU
        (⟨k,pinnedCrossTransition (Geometry AV j) (Geometry AU k) w A hA u hr hpar x⟩,
          ⟨radiusMultiplier u * r.val,hhigh⟩) := by
  induction x using Quotient.inductionOn with
  | h p =>
    rw [pinnedCrossTransition_formula, pinned_cusp_chart_formula, pinned_cusp_chart_formula]
    have he := actual_full_chart_commutes P h AV AU j k δ η ε v hc
      ((p.1, p.2 + sectionShape F hF w ⟨r.val, lt_trans hYV r.property⟩),
        logHeight (F := F) r.val)
    rw [← ht, coordinate_transition_formula,
      pinnedCoordinate_action hF (Geometry AV j).positive_dimension w A hA u hr p
        ⟨r.val,lt_trans hYV r.property⟩] at he
    exact he

 def crossCoordinateHomeomorph (hd : 0 < KPCuspLogShape.dimension F)
    (u : Fˣ) (v : F) :
    KPCuspCharts.Cross F ≃ₜ KPCuspCharts.Cross F where
  toFun := crossCoordinate hd u v
  invFun := fun p =>
    (fun i => (p.1 i - (KPCusp.complexPlace F i).embedding v) /
      (KPCusp.complexPlace F i).embedding (u : F), p.2 - shapeShift hd u)
  left_inv := by
    intro p
    apply Prod.ext
    · funext i
      dsimp [crossCoordinate]
      rw [add_sub_cancel_right, mul_div_cancel_left₀ _
        ((map_ne_zero _).mpr (Units.ne_zero u))]
    · exact add_sub_cancel_right p.2 (shapeShift hd u)
  right_inv := by
    intro p
    apply Prod.ext
    · funext i
      dsimp [crossCoordinate]
      rw [mul_div_cancel₀ _ ((map_ne_zero _).mpr (Units.ne_zero u)), sub_add_cancel]
    · exact sub_add_cancel p.2 (shapeShift hd u)
  continuous_toFun := by
    unfold crossCoordinate
    fun_prop
  continuous_invFun :=
    (continuous_pi fun i =>
      (((continuous_apply i).comp continuous_fst).sub continuous_const).div_const _).prodMk
        (continuous_snd.sub continuous_const)

private theorem crossCoordinate_map_product (hd : 0 < KPCuspLogShape.dimension F)
    (u : Fˣ) (v : F) (μ : Measure (KPCuspCharts.Shape F)) [μ.IsAddHaarMeasure] :
    Measure.map (crossCoordinate hd u v) (volume.prod μ) =
      ENNReal.ofReal (radiusMultiplier u)⁻¹ • (volume.prod μ) := by
  change Measure.map (Prod.map
    (fun x : KPCuspCharts.Horizontal F => fun i =>
      (KPCusp.complexPlace F i).embedding (u : F) * x i +
        (KPCusp.complexPlace F i).embedding v)
    (fun b : KPCuspCharts.Shape F => b + shapeShift hd u)) (volume.prod μ) = _
  rw [← Measure.map_prod_map volume μ (by fun_prop) (by fun_prop),
    horizontal_map_volume, map_add_right_eq_self, Measure.prod_smul_left]

private theorem crossCoordinate_map_restrict (hd : 0 < KPCuspLogShape.dimension F)
    (u : Fˣ) (v : F) (μ : Measure (KPCuspCharts.Shape F)) [μ.IsAddHaarMeasure]
    (E : Set (KPCuspCharts.Cross F)) :
    Measure.map (crossCoordinate hd u v) ((volume.prod μ).restrict E) =
      ENNReal.ofReal (radiusMultiplier u)⁻¹ •
        (volume.prod μ).restrict (crossCoordinate hd u v '' E) := by
  have he := (crossCoordinateHomeomorph hd u v).measurableEmbedding.restrict_map
    (volume.prod μ) (crossCoordinate hd u v '' E)
  change (Measure.map (crossCoordinate hd u v) (volume.prod μ)).restrict
    (crossCoordinate hd u v '' E) =
    Measure.map (crossCoordinate hd u v) ((volume.prod μ).restrict
      ((crossCoordinate hd u v) ⁻¹' (crossCoordinate hd u v '' E))) at he
  rw [Set.preimage_image_eq E (show Function.Injective (crossCoordinate hd u v) from
      (crossCoordinateHomeomorph hd u v).injective),
    crossCoordinate_map_product, Measure.restrict_smul] at he
  exact he.symm

open _root_.DedekindZetaZeroFree.KPMsFixedHaar.NormOneTransition renaming shapeMeasure_eq → shapeMeasure_eq
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.NormOneTransition renaming crossAction_toArch → crossAction_toArch
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.NormOneTransition.IndexPort renaming integral_index → integral_index

private theorem crossAction_toArch_height
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) (g : S) (p : KPCuspCharts.Cross F) (t : ℝ) :
    g.val • KPCuspCharts.toArch F (p,t) = KPCuspCharts.toArch F (G.crossAction g p,t) := by
  obtain ⟨M,hM,hc⟩ := D.upper g.val g.property
  change KPCuspSiegel.action F g.val _ = _
  rw [G.actual_action g M hM hc, G.crossAction_formula g M hM hc]
  rfl

private theorem crossTransition_section_measure
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S T : Subgroup (KPCuspArithmetic.PGL2 F)}
    {DS : KPCuspCharts.ParabolicData F S}
    (GS : KPCuspCharts.ChartOutput F hF S DS)
    {DT : KPCuspCharts.ParabolicData F T}
    (GT : KPCuspCharts.ChartOutput F hF T DT)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (u : Fˣ)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (h : S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom ≤ T) :
    Measure.map (crossTransition GS GT A hA u hr h) GS.sectionMeasure =
      ENNReal.ofReal (radiusMultiplier u)⁻¹ •
        Measure.map (Quotient.mk (KPCuspCharts.crossRelation F T))
        ((volume.prod GS.shapeMeasure).restrict
          (crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1) '' GS.fundamentalDomain)) := by
  letI := GS.haar_shapeMeasure
  have hm : Measurable (crossTransition GS GT A hA u hr h) := by
    apply measurable_from_quotient.mpr
    exact measurable_quotient_mk''.comp (crossCoordinateHomeomorph GS.positive_dimension u _).continuous.measurable
  rw [GS.sectionMeasure_formula, Measure.map_map hm measurable_quotient_mk'']
  have he : crossTransition GS GT A hA u hr h ∘
      Quotient.mk (KPCuspCharts.crossRelation F S) =
      Quotient.mk (KPCuspCharts.crossRelation F T) ∘
        crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1) := rfl
  rw [he]
  change Measure.map (Quotient.mk (KPCuspCharts.crossRelation F T) ∘
    crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1)) _ = _
  rw [← Measure.map_map measurable_quotient_mk''
    (show Measurable (crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1)) from
      (crossCoordinateHomeomorph GS.positive_dimension u _).continuous.measurable),
    crossCoordinate_map_restrict GS.positive_dimension u _ GS.shapeMeasure,
    Measure.map_smul _ measurable_quotient_mk''.aemeasurable]

private theorem inclusion_image_fd
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S T : Subgroup (KPCuspArithmetic.PGL2 F)}
    {DS : KPCuspCharts.ParabolicData F S} {DT : KPCuspCharts.ParabolicData F T}
    (GS : KPCuspCharts.ChartOutput F hF S DS) (GT : KPCuspCharts.ChartOutput F hF T DT)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (u : Fˣ)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (h : S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom ≤ T) :
    letI := KPCuspCharts.homeomorphAction GT.crossAction
    IsFundamentalDomain
      ((S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom).subgroupOf T)
      (crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1) '' GS.fundamentalDomain)
      (volume.prod GT.shapeMeasure) := by
  letI := KPCuspCharts.homeomorphAction GS.crossAction
  letI := KPCuspCharts.homeomorphAction GT.crossAction
  letI := GS.haar_shapeMeasure
  let t := Matrix.ProjGenLinGroup.mk A
  let C := S.map (MulAut.conj t).toMonoidHom
  let H := C.subgroupOf T
  let e : S ≃* H := ((MulAut.conj t).subgroupMap S).trans
    (Subgroup.subgroupOfEquivOfLe h).symm
  let f := (crossCoordinateHomeomorph GS.positive_dimension u (A 0 1 / A 1 1)).toMeasurableEquiv
  rw [← shapeMeasure_eq GS GT]
  have hq := f.quasiMeasurePreserving_symm (volume.prod GS.shapeMeasure)
  rw [show Measure.map f (volume.prod GS.shapeMeasure) =
    ENNReal.ofReal (radiusMultiplier u)⁻¹ • (volume.prod GS.shapeMeasure) from
      crossCoordinate_map_product GS.positive_dimension u _ GS.shapeMeasure] at hq
  have hq' := hq.mono_left (Measure.absolutelyContinuous_smul
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (radiusMultiplier_pos u))).ne')
  refine GS.isFundamentalDomain.image_of_equiv f.toEquiv hq' e.symm.toEquiv ?_
  intro g p
  change crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1) (GS.crossAction (e.symm g) p) =
    GT.crossAction g.val (crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1) p)
  have hp : (crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1)
        (GS.crossAction (e.symm g) p),
        logRatio u / (KPCuspLogShape.dimension F : ℝ)) =
      (GT.crossAction g.val (crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1) p),
        logRatio u / (KPCuspLogShape.dimension F : ℝ)) := by
    apply (KPCuspCharts.toArchHomeomorph F GS.positive_dimension).injective
    change KPCuspCharts.toArch F (_,_) = KPCuspCharts.toArch F (_,_)
    have ha (p' : KPCuspCharts.Cross F) :=
      crossCoordinate_action GS.positive_dimension A hA u hr p' 0
    simp only [zero_add] at ha
    rw [← ha, ← crossAction_toArch_height GT, ← crossAction_toArch_height GS, ← ha]
    have he : t * (e.symm g).val * t⁻¹ = g.val.val := by
      have hx := congrArg (fun x : H => x.val.val) (e.apply_symm_apply g)
      exact hx
    change t • ((e.symm g).val • _) = g.val.val • (t • _)
    rw [← he]
    simp only [mul_smul, inv_smul_smul]
  exact congrArg Prod.fst hp

private theorem crossTransition_section_measure_index
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S T : Subgroup (KPCuspArithmetic.PGL2 F)}
    {DS : KPCuspCharts.ParabolicData F S} {DT : KPCuspCharts.ParabolicData F T}
    (GS : KPCuspCharts.ChartOutput F hF S DS) (GT : KPCuspCharts.ChartOutput F hF T DT)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (u : Fˣ)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (h : S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom ≤ T)
    [((S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom).subgroupOf T).FiniteIndex] :
    Measure.map (crossTransition GS GT A hA u hr h) GS.sectionMeasure =
      ENNReal.ofReal (radiusMultiplier u)⁻¹ •
        (((S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom).subgroupOf T).index •
          GT.sectionMeasure) := by
  letI : Countable F := (Module.finBasis ℚ F).repr.injective.countable
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  letI : Countable (KPCuspArithmetic.PGL2 F) := Matrix.ProjGenLinGroup.mk_surjective.countable
  letI := KPCuspCharts.homeomorphAction GT.crossAction
  letI : MeasurableConstSMul T (KPCuspCharts.Cross F) :=
    ⟨fun g => (GT.crossAction g).continuous.measurable⟩
  letI : SMulInvariantMeasure T (KPCuspCharts.Cross F) (volume.prod GT.shapeMeasure) :=
    ⟨fun g E hE => by
      change (volume.prod GT.shapeMeasure) ((GT.crossAction g) ⁻¹' E) = _
      rw [← Measure.map_apply (GT.crossAction g).continuous.measurable hE, GT.measure_invariant]⟩
  rw [crossTransition_section_measure GS GT A hA u hr h, shapeMeasure_eq GS GT]
  congr 1
  rw [GT.sectionMeasure_formula]
  ext E hE
  have hm : Measurable (Quotient.mk (KPCuspCharts.crossRelation F T)) := measurable_quotient_mk''
  rw [Measure.smul_apply, Measure.map_apply hm hE, Measure.map_apply hm hE,
    Measure.restrict_apply (hm hE), Measure.restrict_apply (hm hE)]
  have hi := integral_index (volume.prod GT.shapeMeasure)
    ((S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom).subgroupOf T)
    (inclusion_image_fd GS GT A hA u hr h) GT.isFundamentalDomain
    (((Quotient.mk (KPCuspCharts.crossRelation F T)) ⁻¹' E).indicator (fun _ => (1 : ℝ≥0∞)))
    (by
      classical
      intro g p
      have hq : Quotient.mk (KPCuspCharts.crossRelation F T) (GT.crossAction g p) =
          Quotient.mk (KPCuspCharts.crossRelation F T) p := by
        apply Quotient.sound
        apply MulAction.orbitRel_apply.mpr
        exact MulAction.mem_orbit_iff.mpr ⟨g, crossAction_toArch GT g p⟩
      change ((Quotient.mk (KPCuspCharts.crossRelation F T)) ⁻¹' E).indicator (fun _ => (1 : ℝ≥0∞))
        (GT.crossAction g p) = _
      unfold Set.indicator
      change (if Quotient.mk (KPCuspCharts.crossRelation F T) (GT.crossAction g p) ∈ E
        then 1 else 0) = (if Quotient.mk (KPCuspCharts.crossRelation F T) p ∈ E then 1 else 0)
      rw [hq])
  simpa only [lintegral_indicator (hm hE), setLIntegral_one,
    Measure.restrict_apply (hm hE), Set.inter_comm, nsmul_eq_mul] using hi

 theorem logLattice_refinement
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S T : Subgroup (KPCuspArithmetic.PGL2 F)}
    {DS : KPCuspCharts.ParabolicData F S} {DT : KPCuspCharts.ParabolicData F T}
    (GS : KPCuspCharts.ChartOutput F hF S DS) (GT : KPCuspCharts.ChartOutput F hF T DT)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (u : Fˣ)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (h : S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom ≤ T) :
    (KPCuspLogShape.logLattice F hF DS.E DS.integralUnits).toAddSubgroup ≤
      (KPCuspLogShape.logLattice F hF DT.E DT.integralUnits).toAddSubgroup := by
  rintro b ⟨v,rfl⟩
  let z : KPCuspCharts.Torus F DS.L := QuotientAddGroup.mk 0
  obtain ⟨x,hx⟩ := QuotientAddGroup.mk_surjective (GS.torusAction v.toMul z)
  have he := (GS.atlas.orbit_equivalence z (GS.torusAction v.toMul z) 0
    (KPCuspLogShape.logarithm F hF DS.E DS.integralUnits v)).mpr
      ⟨v.toMul,rfl,by simp⟩
  rw [← hx] at he
  have he' : (Quotient.mk (KPCuspCharts.crossRelation F S)
      (0, (0 : KPCuspCharts.Shape F))) =
      Quotient.mk _ (x, KPCuspLogShape.logarithm F hF DS.E DS.integralUnits v) := by
    simpa only [z, GS.atlas.lift_formula] using he
  have hp := congrArg (fun y => GT.atlas.projection (crossTransition GS GT A hA u hr h y)) he'
  change GT.atlas.projection (Quotient.mk _ (crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1) (0,0))) =
    GT.atlas.projection (Quotient.mk _ (crossCoordinate GS.positive_dimension u (A 0 1 / A 1 1)
      (x, KPCuspLogShape.logarithm F hF DS.E DS.integralUnits v))) at hp
  rw [GT.atlas.projection_formula, GT.atlas.projection_formula] at hp
  change (QuotientAddGroup.mk ((0 : KPCuspCharts.Shape F) + shapeShift GS.positive_dimension u) :
      KPCuspCharts.Base F hF DT.E DT.integralUnits) =
    QuotientAddGroup.mk (KPCuspLogShape.logarithm F hF DS.E DS.integralUnits v + shapeShift GS.positive_dimension u) at hp
  simp only [zero_add, QuotientAddGroup.mk_add] at hp
  have hb : (QuotientAddGroup.mk (KPCuspLogShape.logarithm F hF DS.E DS.integralUnits v) :
      KPCuspCharts.Base F hF DT.E DT.integralUnits) = 0 := by
    exact add_right_cancel (show _ + QuotientAddGroup.mk (shapeShift GS.positive_dimension u) =
      0 + QuotientAddGroup.mk (shapeShift GS.positive_dimension u) from hp.symm.trans (zero_add _).symm)
  exact (QuotientAddGroup.eq_zero_iff _).mp hb

 def angularTransition
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S T : Subgroup (KPCuspArithmetic.PGL2 F)}
    {DS : KPCuspCharts.ParabolicData F S} {DT : KPCuspCharts.ParabolicData F T}
    (GS : KPCuspCharts.ChartOutput F hF S DS) (GT : KPCuspCharts.ChartOutput F hF T DT)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (u : Fˣ)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (h : S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom ≤ T) :
    KPCuspCharts.Base F hF DS.E DS.integralUnits → KPCuspCharts.Base F hF DT.E DT.integralUnits :=
  fun b => QuotientAddGroup.map _ _ (AddMonoidHom.id _)
    (logLattice_refinement GS GT A hA u hr h) b + QuotientAddGroup.mk (shapeShift GS.positive_dimension u)

private theorem angularTransition_continuous
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S T : Subgroup (KPCuspArithmetic.PGL2 F)}
    {DS : KPCuspCharts.ParabolicData F S} {DT : KPCuspCharts.ParabolicData F T}
    (GS : KPCuspCharts.ChartOutput F hF S DS) (GT : KPCuspCharts.ChartOutput F hF T DT)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (u : Fˣ)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (h : S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom ≤ T) :
    Continuous (angularTransition GS GT A hA u hr h) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  change Continuous (fun b : KPCuspCharts.Shape F =>
    (QuotientAddGroup.mk b : KPCuspCharts.Base F hF DT.E DT.integralUnits) +
      QuotientAddGroup.mk (shapeShift GS.positive_dimension u))
  have hc : Continuous (fun b : KPCuspCharts.Shape F =>
      (QuotientAddGroup.mk b : KPCuspCharts.Base F hF DT.E DT.integralUnits)) :=
    continuous_quotient_mk'
  exact hc.add continuous_const

open _root_.DedekindZetaZeroFree.KPMsFixedHaar.PinnedRadialCharts renaming actual_shape_translation → actual_shape_translation
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.PinnedRadialCharts renaming actual_shape_translation_formula → actual_shape_translation_formula
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.NormOneTransition renaming sectionMeasure_alt_domain → sectionMeasure_alt_domain

private theorem actual_shape_translation_measurable
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) (b : KPCuspCharts.Shape F) :
    Measurable (actual_shape_translation G b) := by
  apply measurable_from_quotient.mpr
  exact measurable_quotient_mk''.comp
    ((Homeomorph.prodCongr (Homeomorph.refl (KPCuspCharts.Horizontal F))
      (Homeomorph.addRight b)).continuous.measurable)

private theorem sectionMeasure_shape_translation
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) (b : KPCuspCharts.Shape F) :
    Measure.map (actual_shape_translation G b) G.sectionMeasure = G.sectionMeasure := by
  letI := G.haar_shapeMeasure
  letI : Countable F := (Module.finBasis ℚ F).repr.injective.countable
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  letI : Countable (KPCuspArithmetic.PGL2 F) := Matrix.ProjGenLinGroup.mk_surjective.countable
  letI := KPCuspCharts.homeomorphAction G.crossAction
  let e : KPCuspCharts.Cross F ≃ₜ KPCuspCharts.Cross F :=
    Homeomorph.prodCongr (Homeomorph.refl _) (Homeomorph.addRight b)
  have hmap : Measure.map e (volume.prod G.shapeMeasure) = volume.prod G.shapeMeasure := by
    change Measure.map (Prod.map (fun x : KPCuspCharts.Horizontal F => x)
      (fun y : KPCuspCharts.Shape F => y + b)) (volume.prod G.shapeMeasure) = _
    rw [← Measure.map_prod_map volume G.shapeMeasure (by fun_prop) (by fun_prop),
      map_add_right_eq_self]
    exact congrArg (fun μ : Measure (KPCuspCharts.Horizontal F) => μ.prod G.shapeMeasure)
      (Measure.map_id (μ := volume))
  have hfd : IsFundamentalDomain S (e '' G.fundamentalDomain)
      (volume.prod G.shapeMeasure) := by
    apply G.isFundamentalDomain.image_of_equiv e.toEquiv
      (MeasurePreserving.symm e.toMeasurableEquiv
        ⟨e.continuous.measurable, hmap⟩).quasiMeasurePreserving
      (MulEquiv.refl S).toEquiv
    intro g p
    obtain ⟨A,hA,hc⟩ := D.upper g.val g.property
    have hf := G.crossAction_formula g A hA hc
    change e (G.crossAction g p) = G.crossAction g (e p)
    rw [hf, G.crossAction_formula g A hA hc]
    apply Prod.ext
    · rfl
    · change p.2 + KPCuspLogShape.logarithm F hF D.E D.integralUnits
        (Additive.ofMul (D.ratio g)) + b =
        (p.2 + b) + KPCuspLogShape.logarithm F hF D.E D.integralUnits
        (Additive.ofMul (D.ratio g))
      abel
  rw [G.sectionMeasure_formula, Measure.map_map
    (actual_shape_translation_measurable G b) measurable_quotient_mk'']
  have hc : actual_shape_translation G b ∘ Quotient.mk (KPCuspCharts.crossRelation F S) =
      Quotient.mk (KPCuspCharts.crossRelation F S) ∘ e := by
    funext x
    exact actual_shape_translation_formula G b x
  rw [hc, ← Measure.map_map measurable_quotient_mk'' e.continuous.measurable]
  have he := e.measurableEmbedding.restrict_map (volume.prod G.shapeMeasure) (e '' G.fundamentalDomain)
  change (Measure.map e (volume.prod G.shapeMeasure)).restrict (e '' G.fundamentalDomain) =
    Measure.map e ((volume.prod G.shapeMeasure).restrict (e ⁻¹' (e '' G.fundamentalDomain))) at he
  rw [Set.preimage_image_eq G.fundamentalDomain e.injective, hmap] at he
  rw [he.symm]
  exact (sectionMeasure_alt_domain G _ hfd).trans G.sectionMeasure_formula

private theorem pinnedCrossTransition_section_measure_index
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S T : Subgroup (KPCuspArithmetic.PGL2 F)}
    {DS : KPCuspCharts.ParabolicData F S} {DT : KPCuspCharts.ParabolicData F T}
    (GS : KPCuspCharts.ChartOutput F hF S DS) (GT : KPCuspCharts.ChartOutput F hF T DT)
    (w : NumberField.InfinitePlace F) (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (u : Fˣ)
    (hr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1)
    (h : S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom ≤ T)
    [((S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom).subgroupOf T).FiniteIndex] :
    Measure.map (pinnedCrossTransition GS GT w A hA u hr h) GS.sectionMeasure =
      ENNReal.ofReal (radiusMultiplier u)⁻¹ •
        (((S.map (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom).subgroupOf T).index •
          GT.sectionMeasure) := by
  rw [pinnedCrossTransition, ← Measure.map_map
    (actual_shape_translation_measurable GT _)
    (by
      apply measurable_from_quotient.mpr
      exact measurable_quotient_mk''.comp
        (crossCoordinateHomeomorph GS.positive_dimension u _).continuous.measurable),
    crossTransition_section_measure_index GS GT A hA u hr h,
    Measure.map_smul _ (actual_shape_translation_measurable GT _).aemeasurable,
    Measure.map_smul _ (actual_shape_translation_measurable GT _).aemeasurable,
    sectionMeasure_shape_translation]

namespace Globalization
open WeightedSectionGlobalization
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.WeightedSectionGlobalization renaming transition_properties → transition_properties
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.WeightedSectionGlobalization renaming regroup_smul → regroup_smul
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.ActualCuspLabelPort renaming actual_label_transition → actual_label_transition
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.PinnedRadialCharts renaming pinned_cusp_chart → pinned_cusp_chart
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.PinnedRadialCharts renaming pinned_cusp_chart_formula → pinned_cusp_chart_formula
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming weighted_section_measure → weighted_section_measure
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming cross_section_inclusion_measurable → cross_section_inclusion_measurable
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming angular_measurable → angular_measurable
open _root_.DedekindZetaZeroFree.KPCuspArithmetic renaming fixes_infinity_upper → fixes_infinity_upper

variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
  {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
  {AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V} {AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U}

 structure UpperMatrix (M : ComponentMatching AV AU) (j : CuspIndex AV) where
  matrix : Matrix.GeneralLinearGroup (Fin 2) F
  ratio : Fˣ
  upper : (matrix : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  ratio_formula : (matrix : Matrix (Fin 2) (Fin 2) F) 0 0 =
    (ratio : F) * (matrix : Matrix (Fin 2) (Fin 2) F) 1 1
  projective_formula : Matrix.ProjGenLinGroup.mk matrix = transition M j

 theorem exists_upperMatrix
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (j : CuspIndex AV) : Nonempty (UpperMatrix M j) := by
  have ht := (actual_label_transition h AV AU M.component M.rational
    M.central M.level M.formula j).1
  obtain ⟨A,hA,hup⟩ := fixes_infinity_upper F (transition M j) ht
  have hn : A 0 0 ≠ 0 ∧ A 1 1 ≠ 0 := by
    constructor <;> intro hz <;>
      exact A.det_ne_zero (by simp [Matrix.det_fin_two, hup, hz])
  let u : Fˣ := Units.mk0 (A 0 0 / A 1 1) (div_ne_zero hn.1 hn.2)
  refine ⟨⟨A,u,hup,?_,hA⟩⟩
  exact (div_mul_cancel₀ _ hn.2).symm

 def upperMatrix
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (j : CuspIndex AV) : UpperMatrix M j :=
  Classical.choice (exists_upperMatrix h M j)

 abbrev cuspGroup (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF V) (j : CuspIndex A) :=
  KPCuspArithmetic.conjugatedStabilizer F
    (KPCuspGenuineMonodromy.Component F ζ hζ V (A.representative j.1))
    ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2)

 theorem matrix_inclusion
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (j : CuspIndex AV) (N : UpperMatrix M j) :
    (cuspGroup AV j).map (MulAut.conj (Matrix.ProjGenLinGroup.mk N.matrix)).toMonoidHom ≤
      (cuspGroup AU (cuspLabel M j)) := by
  rw [N.projective_formula]
  exact (transition_properties h M j).1

 def crossMap
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (w : NumberField.InfinitePlace F) :
    CrossSection AV → CrossSection AU := fun x =>
  let N := upperMatrix h M x.1
  ⟨cuspLabel M x.1, pinnedCrossTransition (Geometry AV x.1) (Geometry AU (cuspLabel M x.1))
    w N.matrix N.upper N.ratio N.ratio_formula (matrix_inclusion h M x.1 N) x.2⟩

private theorem crossMap_continuous
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (w : NumberField.InfinitePlace F) :
    Continuous (crossMap h M w) := by
  apply continuous_sigma
  intro j
  exact (continuous_sigmaMk (i := cuspLabel M j)).comp
    (pinnedCrossTransition_continuous (Geometry AV j) (Geometry AU (cuspLabel M j)) w
      (upperMatrix h M j).matrix (upperMatrix h M j).upper (upperMatrix h M j).ratio
      (upperMatrix h M j).ratio_formula (matrix_inclusion h M j _))

 def scale
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (j : CuspIndex AV) : ℝ :=
  radiusMultiplier (upperMatrix h M j).ratio

 theorem scale_pos
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (j : CuspIndex AV) : 0 < scale h M j :=
  radiusMultiplier_pos _

private theorem crossMap_section_index
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (w : NumberField.InfinitePlace F) (j : CuspIndex AV) :
    Measure.map (fun x => crossMap h M w (⟨j,x⟩ : CrossSection AV)) (Geometry AV j).sectionMeasure =
      (ENNReal.ofReal (scale h M j))⁻¹ • ((degree M j : ℝ≥0∞) • Measure.map
        (fun x => (⟨cuspLabel M j,x⟩ : CrossSection AU)) (Geometry AU (cuspLabel M j)).sectionMeasure) := by
  let N := upperMatrix h M j
  have hidx := (transition_properties h M j).2
  rw [← N.projective_formula] at hidx
  letI := hidx
  have he := pinnedCrossTransition_section_measure_index (Geometry AV j)
    (Geometry AU (cuspLabel M j)) w N.matrix N.upper N.ratio N.ratio_formula
    (matrix_inclusion h M j N)
  have hdeg : (((cuspGroup AV j).map (MulAut.conj
      (Matrix.ProjGenLinGroup.mk N.matrix)).toMonoidHom).subgroupOf
        (cuspGroup AU (cuspLabel M j))).index = degree M j := by
    rw [N.projective_formula]
    rfl
  rw [hdeg, ENNReal.ofReal_inv_of_pos (radiusMultiplier_pos N.ratio)] at he
  have hm : Measurable (pinnedCrossTransition (Geometry AV j) (Geometry AU (cuspLabel M j))
      w N.matrix N.upper N.ratio N.ratio_formula (matrix_inclusion h M j N)) := by
    apply measurable_from_quotient.mpr
    have hp : pinnedCrossTransition (Geometry AV j) (Geometry AU (cuspLabel M j))
      w N.matrix N.upper N.ratio N.ratio_formula (matrix_inclusion h M j N) ∘
      Quotient.mk (KPCuspCharts.crossRelation F (cuspGroup AV j)) =
        Quotient.mk (KPCuspCharts.crossRelation F (cuspGroup AU (cuspLabel M j))) ∘
          pinnedCrossCoordinate hF (Geometry AV j).positive_dimension w N.ratio
            (N.matrix 0 1 / N.matrix 1 1) := by
      funext p
      exact pinnedCrossTransition_formula _ _ _ _ _ _ _ _ _
    rw [hp]
    apply measurable_quotient_mk''.comp
    unfold pinnedCrossCoordinate crossCoordinate
    fun_prop
  change Measure.map ((fun x => (⟨cuspLabel M j,x⟩ : CrossSection AU)) ∘
    pinnedCrossTransition (Geometry AV j) (Geometry AU (cuspLabel M j)) w N.matrix
      N.upper N.ratio N.ratio_formula (matrix_inclusion h M j N)) _ = _
  rw [← Measure.map_map (cross_section_inclusion_measurable AU (cuspLabel M j)) hm, he,
    Measure.map_smul _ (cross_section_inclusion_measurable AU (cuspLabel M j)).aemeasurable,
    Measure.map_smul _ (cross_section_inclusion_measurable AU (cuspLabel M j)).aemeasurable]
  ext E hE
  simp only [Measure.smul_apply, smul_eq_mul, nsmul_eq_mul]
  rfl

 def scaledSectionMeasure
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (wV : Fin AV.componentCount → ℝ≥0∞) :
    Measure (CrossSection AV) :=
  ∑ j : CuspIndex AV,
    (ENNReal.ofReal (scale h M j) * wV j.1 /
      ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) •
      Measure.map (fun x => (⟨j,x⟩ : CrossSection AV)) (Geometry AV j).sectionMeasure

private theorem crossMap_scaled_section
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (w : NumberField.InfinitePlace F)
    (wV : Fin AV.componentCount → ℝ≥0∞) (wU : Fin AU.componentCount → ℝ≥0∞)
    (hbalance : ∀ k : CuspIndex AU, (∑ j : CuspIndex AV, if cuspLabel M j = k then
      wV j.1 * (degree M j : ℝ≥0∞) else 0) = wU k.1) :
    Measure.map (crossMap h M w) (scaledSectionMeasure h M wV) =
      weighted_section_measure AU wU := by
  have hc := (crossMap_continuous h M w).measurable
  unfold scaledSectionMeasure weighted_section_measure
  rw [Measure.map_finset_sum hc.aemeasurable]
  have he : (∑ j : CuspIndex AV, Measure.map (crossMap h M w)
      ((ENNReal.ofReal (scale h M j) * wV j.1 /
        ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) •
        Measure.map (fun x => (⟨j,x⟩ : CrossSection AV)) (Geometry AV j).sectionMeasure)) =
      ∑ j : CuspIndex AV,
        (wV j.1 * (degree M j : ℝ≥0∞) /
          ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) •
          Measure.map (fun x => (⟨cuspLabel M j,x⟩ : CrossSection AU))
            (Geometry AU (cuspLabel M j)).sectionMeasure := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Measure.map_smul _ hc.aemeasurable,
      Measure.map_map hc (cross_section_inclusion_measurable AV j)]
    dsimp only [Function.comp_def]
    rw [crossMap_section_index, smul_smul, smul_smul]
    congr 1
    simp only [div_eq_mul_inv]
    have hcancel : ENNReal.ofReal (scale h M j) * (ENNReal.ofReal (scale h M j))⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (scale_pos h M j)).ne' ENNReal.ofReal_ne_top
    calc
      _ = (ENNReal.ofReal (scale h M j) * (ENNReal.ofReal (scale h M j))⁻¹) *
        (wV j.1 * (degree M j : ℝ≥0∞) *
          (ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ)))⁻¹) := by ring
      _ = _ := by rw [hcancel, one_mul]
  rw [he, regroup_smul (cuspLabel M)
    (fun j => wV j.1 * (degree M j : ℝ≥0∞) /
      ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ)))
    (fun k => Measure.map (fun x => (⟨k,x⟩ : CrossSection AU))
      (Geometry AU k).sectionMeasure)]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [← hbalance k, ENNReal.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

 def angularMap
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (w : NumberField.InfinitePlace F) : Omega AV → Omega AU := fun ω =>
  let N := upperMatrix h M ω.1
  ⟨cuspLabel M ω.1,
    angularTransition (Geometry AV ω.1) (Geometry AU (cuspLabel M ω.1))
      N.matrix N.upper N.ratio N.ratio_formula (matrix_inclusion h M ω.1 N) ω.2 -
      QuotientAddGroup.mk (sectionShape F hF w ⟨scale h M ω.1,scale_pos h M ω.1⟩)⟩

private theorem angularMap_continuous
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (w : NumberField.InfinitePlace F) :
    Continuous (angularMap h M w) := by
  apply continuous_sigma
  intro j
  have hc := (angularTransition_continuous (Geometry AV j) (Geometry AU (cuspLabel M j))
    (upperMatrix h M j).matrix (upperMatrix h M j).upper (upperMatrix h M j).ratio
    (upperMatrix h M j).ratio_formula (matrix_inclusion h M j _)).sub
      (continuous_const (y := (QuotientAddGroup.mk (sectionShape F hF w
        ⟨scale h M j,scale_pos h M j⟩) : KPCuspCharts.Base F hF
          (Parabolic AU (cuspLabel M j)).E (Parabolic AU (cuspLabel M j)).integralUnits)))
  exact (continuous_sigmaMk (i := cuspLabel M j)).comp hc

private theorem projection_commutes
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (w : NumberField.InfinitePlace F) (x : CrossSection AV) :
    angularProjection AU (crossMap h M w x) = angularMap h M w (angularProjection AV x) := by
  rcases x with ⟨j,x⟩
  induction x using Quotient.inductionOn with
  | h p =>
    apply congrArg (Sigma.mk (cuspLabel M j))
    change (Geometry AU (cuspLabel M j)).atlas.projection
      (pinnedCrossTransition (Geometry AV j) (Geometry AU (cuspLabel M j)) w
        (upperMatrix h M j).matrix (upperMatrix h M j).upper (upperMatrix h M j).ratio
        (upperMatrix h M j).ratio_formula (matrix_inclusion h M j _) (Quotient.mk _ p)) = _
    dsimp only [angularProjection, Sigma.fst, Sigma.snd]
    rw [pinnedCrossTransition_formula, (Geometry AU (cuspLabel M j)).atlas.projection_formula,
      (Geometry AV j).atlas.projection_formula]
    let B := KPCuspCharts.Base F hF (Parabolic AU (cuspLabel M j)).E
      (Parabolic AU (cuspLabel M j)).integralUnits
    let s := shapeShift (Geometry AV j).positive_dimension (upperMatrix h M j).ratio
    let z := sectionShape F hF w ⟨scale h M j,scale_pos h M j⟩
    change (QuotientAddGroup.mk ((p.2 + s) - z) : B) =
      ((QuotientAddGroup.mk p.2 : B) + (QuotientAddGroup.mk s : B)) -
        (QuotientAddGroup.mk z : B)
    rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add]

private theorem chart_commutes
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (w : NumberField.InfinitePlace F)
    (YV YU : ℝ) (hV : 0 < YV) (hU : 0 < YU) (x : CrossSection AV)
    (r : Set.Ioi YV) (hr : YU < scale h M x.1 * r.val) :
    P.forget V U h (pinned_cusp_chart AV w YV hV (x,r)) =
      pinned_cusp_chart AU w YU hU
        (crossMap h M w x,⟨scale h M x.1 * r.val,hr⟩) := by
  exact actual_shifted_pinned_chart_commutes P h AV AU x.1 (cuspLabel M x.1)
    (M.rational x.1.1) (correction M x.1) (M.central x.1.1) (M.level x.1.1)
    (M.formula x.1.1) (upperMatrix h M x.1).matrix (upperMatrix h M x.1).projective_formula
    (upperMatrix h M x.1).upper (upperMatrix h M x.1).ratio
    (upperMatrix h M x.1).ratio_formula (matrix_inclusion h M x.1 _) w YV YU hV hU x.2 r hr

private theorem scale_cross_measurable
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) : Measurable (fun x : CrossSection AV => ENNReal.ofReal (scale h M x.1)) := by
  have hc : Continuous (fun x : CrossSection AV => ENNReal.ofReal (scale h M x.1)) := by
    apply continuous_sigma
    intro j
    exact (continuous_const (y := ENNReal.ofReal (scale h M j)) :
      Continuous (fun _ : KPCuspCharts.CrossQuotient F (cuspGroup AV j) =>
        ENNReal.ofReal (scale h M j)))
  exact hc.measurable

private theorem scale_angular_measurable
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) : Measurable (fun ω : Omega AV => ENNReal.ofReal (scale h M ω.1)) := by
  have hc : Continuous (fun ω : Omega AV => ENNReal.ofReal (scale h M ω.1)) := by
    apply continuous_sigma
    intro j
    exact (continuous_const (y := ENNReal.ofReal (scale h M j)) :
      Continuous (fun _ : KPCuspCharts.Base F hF (Parabolic AV j).E
        (Parabolic AV j).integralUnits => ENNReal.ofReal (scale h M j)))
  exact hc.measurable

private theorem scaledSectionMeasure_eq_density
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (wV : Fin AV.componentCount → ℝ≥0∞) :
    scaledSectionMeasure h M wV = (weighted_section_measure AV wV).withDensity
      (fun x => ENNReal.ofReal (scale h M x.1)) := by
  ext E hE
  rw [withDensity_apply _ hE]
  rw [← lintegral_indicator hE]
  simp only [scaledSectionMeasure, weighted_section_measure, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, lintegral_finsetSum_measure, lintegral_smul_measure]
  apply Finset.sum_congr rfl
  intro j _
  rw [lintegral_map (by exact (scale_cross_measurable h M).indicator hE)
    (cross_section_inclusion_measurable AV j)]
  have hi : (fun x => E.indicator (fun x => ENNReal.ofReal (scale h M x.1))
      (⟨j,x⟩ : CrossSection AV)) =
    (fun x => ENNReal.ofReal (scale h M j) *
      (((fun x => (⟨j,x⟩ : CrossSection AV)) ⁻¹' E).indicator (fun _ => 1)) x) := by
    funext x
    by_cases hx : (⟨j,x⟩ : CrossSection AV) ∈ E <;> simp [hx]
  rw [hi, lintegral_const_mul _ (by
    exact (measurable_const (a := (1 : ℝ≥0∞))).indicator
      ((cross_section_inclusion_measurable AV j) hE)), lintegral_indicator
      ((cross_section_inclusion_measurable AV j) hE), setLIntegral_one,
    Measure.map_apply (cross_section_inclusion_measurable AV j) hE]
  simp only [div_eq_mul_inv]
  ring

open _root_.DedekindZetaZeroFree.KPMsFixedHaar.AllLevelMeasureTransport renaming beta_eq_marginal → beta_eq_marginal
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming weighted_angular_measure → weighted_angular_measure

private theorem scaledAngular_eq_marginal
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (DV : GeometricDisintegration AV R P) :
    Measure.map (angularProjection AV) (scaledSectionMeasure h M DV.componentWeight) =
      DV.beta.withDensity (fun ω => ENNReal.ofReal (scale h M ω.1)) := by
  rw [scaledSectionMeasure_eq_density, ← beta_eq_marginal AV DV]
  unfold weighted_angular_measure
  ext E hE
  rw [Measure.map_apply (angular_measurable AV) hE, withDensity_apply _ ((angular_measurable AV) hE),
    withDensity_apply _ hE]
  rw [← lintegral_indicator hE, lintegral_map
    ((scale_angular_measurable h M).indicator hE) (angular_measurable AV)]
  rw [← lintegral_indicator ((angular_measurable AV) hE)]
  apply lintegral_congr
  intro x
  by_cases hx : angularProjection AV x ∈ E
  · rw [Set.indicator_of_mem (show x ∈ angularProjection AV ⁻¹' E from hx),
      Set.indicator_of_mem hx]
    rfl
  · rw [Set.indicator_of_notMem (show x ∉ angularProjection AV ⁻¹' E from hx),
      Set.indicator_of_notMem hx]

private theorem angularMap_scaled_beta
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (w : NumberField.InfinitePlace F)
    (DV : GeometricDisintegration AV R P) (DU : GeometricDisintegration AU R P)
    (hbalance : ∀ k : CuspIndex AU, (∑ j : CuspIndex AV, if cuspLabel M j = k then
      DV.componentWeight j.1 * (degree M j : ℝ≥0∞) else 0) = DU.componentWeight k.1) :
    Measure.map (angularMap h M w)
      (DV.beta.withDensity (fun ω => ENNReal.ofReal (scale h M ω.1))) = DU.beta := by
  rw [← scaledAngular_eq_marginal R P h M DV,
    Measure.map_map (angularMap_continuous h M w).measurable (angular_measurable AV)]
  have hc : angularMap h M w ∘ angularProjection AV = angularProjection AU ∘ crossMap h M w := by
    funext x
    exact (projection_commutes h M w x).symm
  rw [hc, ← Measure.map_map (angular_measurable AU) (crossMap_continuous h M w).measurable,
    crossMap_scaled_section h M w _ _ hbalance]
  exact beta_eq_marginal AU DU

open _root_.DedekindZetaZeroFree.KPMsFixedHaar.AllLevelMeasureTransport renaming section_lintegral → section_lintegral
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming probability_map → probability_map
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming kernel_angular_lintegral → kernel_angular_lintegral

private theorem fiber_label_ae
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (DV : GeometricDisintegration AV R P) (ω : Omega AV) :
    ∀ᵐ x ∂DV.unipotent ω, x.1 = ω.1 := by
  letI := DV.probability_unipotent ω
  have hm : Measurable (fun z : Omega AV => if z.1 = ω.1 then (1 : ℝ≥0∞) else 0) := by
    have hc : Continuous (fun z : Omega AV => if z.1 = ω.1 then (1 : ℝ≥0∞) else 0) := by
      apply continuous_sigma
      intro j
      exact (continuous_const (y := if j = ω.1 then (1 : ℝ≥0∞) else 0) :
        Continuous (fun _ : KPCuspCharts.Base F hF (Parabolic AV j).E
          (Parabolic AV j).integralUnits => if j = ω.1 then (1 : ℝ≥0∞) else 0))
    exact hc.measurable
  have hmc := hm.comp (angular_measurable AV)
  have hs : MeasurableSet {x : CrossSection AV | x.1 = ω.1} := by
    have hp := hmc (measurableSet_singleton (1 : ℝ≥0∞))
    convert hp using 1
    ext x
    by_cases hx : x.1 = ω.1 <;> simp [angularProjection, hx]
  have he := kernel_angular_lintegral AV DV.toFiberKernel ω
    (fun z => if z.1 = ω.1 then (1 : ℝ≥0∞) else 0) hm
  have hfun : (fun x : CrossSection AV =>
      if (angularProjection AV x).1 = ω.1 then (1 : ℝ≥0∞) else 0) =
    {x : CrossSection AV | x.1 = ω.1}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x.1 = ω.1
    · rw [Set.indicator_of_mem (show x ∈ {x : CrossSection AV | x.1 = ω.1} from hx)]
      simp only [angularProjection, hx, if_true]
    · rw [Set.indicator_of_notMem (show x ∉ {x : CrossSection AV | x.1 = ω.1} from hx)]
      simp only [angularProjection, hx, if_false]
  change (∫⁻ x, (if (angularProjection AV x).1 = ω.1 then (1 : ℝ≥0∞) else 0)
    ∂DV.unipotent ω) = _ at he
  rw [hfun, lintegral_indicator hs, setLIntegral_one] at he
  have hprob : (DV.unipotent ω) {x : CrossSection AV | x.1 = ω.1} = 1 := by
    simpa using he
  exact (mem_ae_iff_prob_eq_one hs).mpr hprob

private theorem kernel_scaled_section
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (DV : GeometricDisintegration AV R P)
    (f : CrossSection AV → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂scaledSectionMeasure h M DV.componentWeight) =
      ∫⁻ ω, ENNReal.ofReal (scale h M ω.1) * ∫⁻ x, f x ∂DV.unipotent ω ∂DV.beta := by
  rw [scaledSectionMeasure_eq_density,
    lintegral_withDensity_eq_lintegral_mul _ (scale_cross_measurable h M) hf]
  rw [section_lintegral AV DV _ ((scale_cross_measurable h M).mul hf)]
  apply lintegral_congr
  intro ω
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [fiber_label_ae R P DV ω] with x hx
  dsimp only [Pi.mul_apply]
  rw [hx]

private theorem induced_kernel
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (w : NumberField.InfinitePlace F)
    (DV : GeometricDisintegration AV R P) (DU : GeometricDisintegration AU R P)
    (hbalance : ∀ k : CuspIndex AU, (∑ j : CuspIndex AV, if cuspLabel M j = k then
      DV.componentWeight j.1 * (degree M j : ℝ≥0∞) else 0) = DU.componentWeight k.1)
    (f : CrossSection AU → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ENNReal.ofReal (scale h M ω.1) *
      ∫⁻ x, f (crossMap h M w x) ∂DV.unipotent ω ∂DV.beta) =
      ∫⁻ ω, ∫⁻ x, f x ∂DU.unipotent ω ∂DU.beta := by
  have hf' : Measurable (fun x : CrossSection AV => f (crossMap h M w x)) :=
    hf.comp (crossMap_continuous h M w).measurable
  have hk := kernel_scaled_section R P h M DV (fun x => f (crossMap h M w x)) hf'
  rw [← hk,
    ← section_lintegral AU DU, ← crossMap_scaled_section h M w _ _ hbalance,
    lintegral_map hf (crossMap_continuous h M w).measurable]
  exact hf

private theorem induced_probability
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (w : NumberField.InfinitePlace F)
    (DV : GeometricDisintegration AV R P) (DU : GeometricDisintegration AU R P)
    (hbalance : ∀ k : CuspIndex AU, (∑ j : CuspIndex AV, if cuspLabel M j = k then
      DV.componentWeight j.1 * (degree M j : ℝ≥0∞) else 0) = DU.componentWeight k.1) :
    Measure.map (angularMap h M w)
      (probability AV (DV.beta.withDensity (fun ω => ENNReal.ofReal (scale h M ω.1)))) =
      probability AU DU.beta := by
  exact probability_map AV AU _ _ _ (angularMap_continuous h M w).measurable
    (angularMap_scaled_beta R P h M w DV DU hbalance)

private theorem coefficient
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU) (w : NumberField.InfinitePlace F)
    (DV : GeometricDisintegration AV R P) (DU : GeometricDisintegration AU R P)
    (hbalance : ∀ k : CuspIndex AU, (∑ j : CuspIndex AV, if cuspLabel M j = k then
      DV.componentWeight j.1 * (degree M j : ℝ≥0∞) else 0) = DU.componentWeight k.1) :
    kappa AU R P DU =
      ((DV.beta.withDensity (fun ω => ENNReal.ofReal (scale h M ω.1))) Set.univ).toReal := by
  have he := angularMap_scaled_beta R P h M w DV DU hbalance
  have hm : (DV.beta.withDensity (fun ω => ENNReal.ofReal (scale h M ω.1))) Set.univ = DU.beta Set.univ := by
    rw [← he, Measure.map_apply (angularMap_continuous h M w).measurable
      MeasurableSet.univ, Set.preimage_univ]
  exact congrArg ENNReal.toReal hm.symm

private theorem geometric_chart_eq_pinned
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (DV : GeometricDisintegration AV R P)
    (Y : ℝ) (hY : AdmissibleCutoff AV Y) (x : CrossSection AV) (r : Set.Ioi Y) :
    DV.chart Y hY (x,r) = pinned_cusp_chart AV DV.radial.slot Y hY.1 (x,r) := by
  rcases x with ⟨j,x⟩
  induction x using Quotient.inductionOn with
  | h p =>
    rw [DV.chart_formula Y hY j p r]
    exact (pinned_cusp_chart_formula AV DV.radial.slot Y hY.1 j p r).symm

private theorem actual_chart_commutes
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (M : ComponentMatching AV AU)
    (DV : GeometricDisintegration AV R P) (DU : GeometricDisintegration AU R P)
    (hslot : DV.radial.slot = DU.radial.slot)
    (YV YU : ℝ) (hV : AdmissibleCutoff AV YV) (hU : AdmissibleCutoff AU YU)
    (x : CrossSection AV) (r : Set.Ioi YV) (hr : YU < scale h M x.1 * r.val) :
    P.forget V U h (DV.chart YV hV (x,r)) =
      DU.chart YU hU (crossMap h M DV.radial.slot x,⟨scale h M x.1 * r.val,hr⟩) := by
  rw [geometric_chart_eq_pinned R P DV, geometric_chart_eq_pinned R P DU, ← hslot]
  exact chart_commutes P h M DV.radial.slot YV YU hV.1 hU.1 x r hr

 theorem exists_actual_compatibility_laws
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (DV : GeometricDisintegration AV R P) (DU : GeometricDisintegration AU R P)
    (hslot : DV.radial.slot = DU.radial.slot) :
    ∃ (l : CuspIndex AV → CuspIndex AU) (rho : CuspIndex AV → Radius)
      (c : CrossSection AV → CrossSection AU) (a : Omega AV → Omega AU),
      Measurable c ∧ Measurable a ∧
      (∀ x, (c x).1 = l x.1) ∧ (∀ ω, (a ω).1 = l ω.1) ∧
      (∀ x, angularProjection AU (c x) = a (angularProjection AV x)) ∧
      (Measure.map a (DV.beta.withDensity (fun ω => ENNReal.ofReal (rho ω.1).val)) = DU.beta) ∧
      (Measure.map a (probability AV (DV.beta.withDensity
        (fun ω => ENNReal.ofReal (rho ω.1).val))) = probability AU DU.beta) ∧
      (kappa AU R P DU = ((DV.beta.withDensity
        (fun ω => ENNReal.ofReal (rho ω.1).val)) Set.univ).toReal) ∧
      (∀ f : CrossSection AU → ℝ≥0∞, Measurable f →
        (∫⁻ ω, ENNReal.ofReal (rho ω.1).val * ∫⁻ x, f (c x) ∂DV.unipotent ω ∂DV.beta) =
          ∫⁻ ω, ∫⁻ x, f x ∂DU.unipotent ω ∂DU.beta) ∧
      (∀ YV YU (hV : AdmissibleCutoff AV YV) (hU : AdmissibleCutoff AU YU)
        (x : CrossSection AV) (r : Set.Ioi YV) (hr : YU < (rho x.1).val * r.val),
        P.forget V U h (DV.chart YV hV (x,r)) = DU.chart YU hU
          (c x,⟨(rho x.1).val * r.val,hr⟩)) := by
  obtain ⟨M,hbalance⟩ := exists_matching_degree_balance R P h DV DU
  refine ⟨cuspLabel M,fun j => ⟨scale h M j,scale_pos h M j⟩,
    crossMap h M DV.radial.slot,angularMap h M DV.radial.slot,
    (crossMap_continuous h M DV.radial.slot).measurable,(angularMap_continuous h M DV.radial.slot).measurable,
    fun _ => rfl,fun _ => rfl,projection_commutes h M DV.radial.slot,
    angularMap_scaled_beta R P h M DV.radial.slot DV DU hbalance,
    induced_probability R P h M DV.radial.slot DV DU hbalance,
    coefficient R P h M DV.radial.slot DV DU hbalance,?_,?_⟩
  · exact induced_kernel R P h M DV.radial.slot DV DU hbalance
  · exact actual_chart_commutes R P h M DV DU hslot

end Globalization

end DedekindZetaZeroFree.KPMsFixedHaar.RadiusShift

end

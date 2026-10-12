module

public import DedekindZetaZeroFree.Adeles.Haar.FiniteRestrictedProductMeasure
public import DedekindZetaZeroFree.Metaplectic.Torus.AdelicSmoothFunctionTopology
public import DedekindZetaZeroFree.LFunctions.Tate.ArchimedeanAdditiveHaarScaling

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
abbrev Adeles := KPGlobalTorusFunctionData.Adeles F

 def archSlot (u : InfinitePlace F → ℝ) (w : InfinitePlace F) : w.Completionˣ :=
  Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toMonoidHom
    (Units.mk0 (Real.exp (u w) : ℂ) (by exact_mod_cast Real.exp_ne_zero (u w)))

def archDiagonalIdele (u : InfinitePlace F → ℝ) : KPAdelicCoverRestrictedProduct.Ideles F where
  val := (fun w => (archSlot F ζ hζ u w).val, 1)
  inv := (fun w => (archSlot F ζ hζ u w).inv, 1)
  val_inv := by
    apply Prod.ext
    · funext w; exact (archSlot F ζ hζ u w).val_inv
    · exact one_mul _
  inv_val := by
    apply Prod.ext
    · funext w; exact (archSlot F ζ hζ u w).inv_val
    · exact one_mul _

theorem archDiagonalIdele_neg (u : InfinitePlace F → ℝ) :
    archDiagonalIdele F ζ hζ (fun w => -u w) = (archDiagonalIdele F ζ hζ u)⁻¹ := by
  apply Units.ext
  apply Prod.ext
  · funext w
    change (archSlot F ζ hζ (fun w => -u w) w).val = ((archSlot F ζ hζ u w)⁻¹).val
    unfold archSlot
    simp only [Units.val_inv_eq_inv_val, Units.coe_map, Units.val_mk0]
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm (Real.exp (-u w) : ℂ) =
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm (Real.exp (u w) : ℂ))⁻¹
    rw [Real.exp_neg, Complex.ofReal_inv, map_inv₀]
  · rfl

private theorem arch_norm (u : InfinitePlace F → ℝ) :
    ‖(archDiagonalIdele F ζ hζ u).val.1‖ = Real.exp (2 * ∑ w, u w) := by
  rw [InfiniteAdeleRing.norm_def]
  have hv : ∀ w : InfinitePlace F, ‖(archDiagonalIdele F ζ hζ u).val.1 w‖ = Real.exp (u w) := by
    intro w
    let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)
    have he := e.isometry.dist_eq ((archDiagonalIdele F ζ hζ u).val.1 w) 0
    have he0 : e 0 = 0 := (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).map_zero
    rw [he0, dist_zero_right, dist_zero_right] at he
    rw [← he]
    change ‖(InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w))
      ((archDiagonalIdele F ζ hζ u).val.1 w)‖ = _
    have hcoord : (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w))
        ((archDiagonalIdele F ζ hζ u).val.1 w) = (Real.exp (u w) : ℂ) := by
      change (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w))
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm (Real.exp (u w) : ℂ)) = _
      exact RingEquiv.apply_symm_apply _ _
    rw [hcoord, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp_rw [hv, (KPHilbert.infinite_isComplex F ζ hζ _).mult_eq_two,
    ← Real.exp_nat_mul]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  simp

 def archMul (d : (InfiniteAdeleRing F)ˣ) (x : Adeles F) : Adeles F :=
  (d.val * x.1, x.2)

private theorem map_arch_mul (d : (InfiniteAdeleRing F)ˣ) :
    Measure.map (archMul F d) (KPAdditiveHaar.adelicMeasure F) =
      (ENNReal.ofReal ‖d.val‖)⁻¹ • KPAdditiveHaar.adelicMeasure F := by
  let μa := KPAdditiveHaar.archMeasure F
  let μf := KPAdditiveHaar.finiteMeasure F
  letI : μa.IsAddHaarMeasure := KPAdditiveHaar.archMeasure_isAddHaarMeasure F
  letI : μf.IsAddHaarMeasure := KPAdditiveHaar.finiteMeasure_isAddHaarMeasure F
  let cast : InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F → Adeles F := fun x => x
  have hc : Measurable cast := by
    have heq : (MeasurableSpace.prod inferInstance inferInstance :
      MeasurableSpace (InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) =
      borel (Adeles F) := BorelSpace.measurable_eq
    change @Measurable _ _ (MeasurableSpace.prod inferInstance inferInstance) (borel _) _
    rw [heq]
    exact measurable_id
  letI : SigmaCompactSpace (InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  have hm : Measurable (archMul F d) := by
    have hh := ((continuous_const.mul continuous_fst).prodMk continuous_snd :
      Continuous (fun x : Adeles F => ((d.val * x.1, x.2) : Adeles F))).borel_measurable
    exact hh
  have hp : Measurable (Prod.map (fun x : InfiniteAdeleRing F => d.val * x)
      (id : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F → _)) :=
    (continuous_const.mul continuous_id).measurable.prodMap measurable_id
  have harch : Measure.map (fun x : InfiniteAdeleRing F => d.val * x) μa =
      (ENNReal.ofReal ‖d.val‖)⁻¹ • μa := TateSLocalMeasurability.archimedean_map_mul F d
  have hprod : Measure.map (Prod.map (fun x : InfiniteAdeleRing F => d.val * x)
      (id : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F → _)) (μa.prod μf) =
      (ENNReal.ofReal ‖d.val‖)⁻¹ • (μa.prod μf) := by
    rw [← Measure.map_prod_map (f := fun x : InfiniteAdeleRing F => d.val * x) (g := id) μa μf (continuous_const.mul continuous_id).measurable measurable_id,
      Measure.map_id, harch, Measure.prod_smul_left]
  change Measure.map _ (Measure.map cast (μa.prod μf)) =
    (ENNReal.ofReal ‖d.val‖)⁻¹ • Measure.map cast (μa.prod μf)
  rw [Measure.map_map hm hc]
  have he : archMul F d ∘ cast =
      cast ∘ Prod.map (fun x : InfiniteAdeleRing F => d.val * x) id := rfl
  rw [he, ← Measure.map_map hc hp, hprod, Measure.map_smul _ hc.aemeasurable]

theorem integral_arch_mul (u : InfinitePlace F → ℝ) (h : Adeles F → ℂ)
    (hh : Measurable h) :
    (∫ x, h (x * ((archDiagonalIdele F ζ hζ u)⁻¹).val) ∂KPAdditiveHaar.adelicMeasure F) =
      (Real.exp (2 * ∑ w, u w) : ℂ) * ∫ x, h x ∂KPAdditiveHaar.adelicMeasure F := by
  let d : (InfiniteAdeleRing F)ˣ := Units.map (RingHom.fst _ _).toMonoidHom
    (archDiagonalIdele F ζ hζ (fun w => -u w))
  have hn : ‖d.val‖ = Real.exp (-(2 * ∑ w, u w)) := by
    change ‖(archDiagonalIdele F ζ hζ (fun w => -u w)).val.1‖ = _
    simpa only [Finset.sum_neg_distrib, mul_neg] using arch_norm F ζ hζ (fun w => -u w)
  have he : (fun x : Adeles F => x * ((archDiagonalIdele F ζ hζ u)⁻¹).val) = archMul F d := by
    funext x
    rw [← archDiagonalIdele_neg]
    apply Prod.ext
    · exact mul_comm _ _
    · exact mul_one _
  simp_rw [congrFun he]
  have hm : Measurable (archMul F d) := ((continuous_const.mul continuous_fst).prodMk continuous_snd).borel_measurable
  rw [← integral_map hm.aemeasurable hh.aestronglyMeasurable,
    map_arch_mul F d, integral_smul_measure, hn]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]
  simp only [Real.exp_neg, inv_inv]
  rfl

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end

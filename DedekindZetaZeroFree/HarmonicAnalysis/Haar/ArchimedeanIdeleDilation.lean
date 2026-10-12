module

public import DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries
public import DedekindZetaZeroFree.Adeles.Haar.FiniteRestrictedProductMeasure
public import DedekindZetaZeroFree.LFunctions.Tate.ArchimedeanAdditiveHaarScaling

@[expose] public section

noncomputable section
open MeasureTheory NumberField
open scoped Classical NumberField ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.ArchHaar
variable {F : Type} [Field F] [NumberField F]

private theorem map_arch_mul_full (a : (KPGlobalTorusFunctionData.Adeles F)ˣ)
    (ha : a.val.2 = 1) :
    Measure.map (fun x : KPGlobalTorusFunctionData.Adeles F => a.val * x)
      (KPAdditiveHaar.adelicMeasure F) =
      (ENNReal.ofReal ‖a.val.1‖)⁻¹ • KPAdditiveHaar.adelicMeasure F := by
  let μa := KPAdditiveHaar.archMeasure F
  let μf := KPAdditiveHaar.finiteMeasure F
  let : μa.IsAddHaarMeasure := KPAdditiveHaar.archMeasure_isAddHaarMeasure F
  let : μf.IsAddHaarMeasure := KPAdditiveHaar.finiteMeasure_isAddHaarMeasure F
  let d : (InfiniteAdeleRing F)ˣ := Units.map (RingHom.fst _ _).toMonoidHom a
  let cast : InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F →
    KPGlobalTorusFunctionData.Adeles F := fun x => x
  have hc : Measurable cast := by
    have heq : (MeasurableSpace.prod inferInstance inferInstance :
      MeasurableSpace (InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) =
      borel (KPGlobalTorusFunctionData.Adeles F) := BorelSpace.measurable_eq
    change @Measurable _ _ (MeasurableSpace.prod inferInstance inferInstance) (borel _) _
    rw [heq]
    exact measurable_id
  let : SigmaCompactSpace (InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  have hm : Measurable (fun x : KPGlobalTorusFunctionData.Adeles F => a.val * x) := by fun_prop
  have hp : Measurable (Prod.map (fun x : InfiniteAdeleRing F => d.val * x)
      (id : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F → _)) :=
    (continuous_const.mul continuous_id).measurable.prodMap measurable_id
  have harch : Measure.map (fun x : InfiniteAdeleRing F => d.val * x) μa =
      (ENNReal.ofReal ‖d.val‖)⁻¹ • μa := TateSLocalMeasurability.archimedean_map_mul F d
  have hprod : Measure.map (Prod.map (fun x : InfiniteAdeleRing F => d.val * x)
      (id : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F → _)) (μa.prod μf) =
      (ENNReal.ofReal ‖d.val‖)⁻¹ • (μa.prod μf) := by
    rw [← Measure.map_prod_map (f := fun x : InfiniteAdeleRing F => d.val * x) (g := id)
      μa μf (continuous_const.mul continuous_id).measurable measurable_id,
      Measure.map_id, harch, Measure.prod_smul_left]
  change Measure.map _ (Measure.map cast (μa.prod μf)) =
    (ENNReal.ofReal ‖d.val‖)⁻¹ • Measure.map cast (μa.prod μf)
  rw [Measure.map_map hm hc]
  have he : (fun x : KPGlobalTorusFunctionData.Adeles F => a.val * x) ∘ cast =
      cast ∘ Prod.map (fun x : InfiniteAdeleRing F => d.val * x) id := by
    funext x
    exact Prod.ext rfl (by change a.val.2 * x.2 = x.2; rw [ha, one_mul])
  rw [he, ← Measure.map_map hc hp, hprod, Measure.map_smul _ hc.aemeasurable]

theorem arch_idele_intrinsicHaarChar (a : (KPGlobalTorusFunctionData.Adeles F)ˣ)
    (ha : a.val.2 = 1) :
    (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft a) : ℝ) = ‖a.val.1‖ := by
  let μ := KPAdditiveHaar.adelicMeasure F
  let := KPAdditiveHaar.adelicMeasure_isAddHaarMeasure F
  let m := addEquivAddHaarChar (ContinuousAddEquiv.mulLeft a)
  have hm := addEquivAddHaarChar_smul_map μ (ContinuousAddEquiv.mulLeft a)
  change m • Measure.map (fun x => a.val * x) μ = μ at hm
  rw [map_arch_mul_full a ha] at hm
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : KPGlobalTorusFunctionData.Adeles F)
  let k : KPGlobalTorusFunctionData.Adeles F → ℂ := K.indicator (fun _ => 1)
  have hi : (∫ x, k x ∂μ) ≠ 0 := by
    rw [show k = K.indicator (fun _ => (1 : ℂ)) from rfl,
      integral_indicator_const _ hK.measurableSet]
    simpa only [Complex.real_smul, mul_one, Complex.ofReal_ne_zero, measureReal_def] using
      (ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds μ hKn).ne' hK.measure_ne_top).ne'
  have hn : 0 < ‖a.val.1‖ := by
    rw [InfiniteAdeleRing.norm_def]
    apply Finset.prod_pos
    intro w _
    apply pow_pos
    apply norm_pos_iff.mpr
    have hu := congrArg (fun x : KPGlobalTorusFunctionData.Adeles F => x.1 w) a.val_inv
    change a.val.1 w * a.inv.1 w = 1 at hu
    exact left_ne_zero_of_mul_eq_one hu
  have hh := congrArg (fun ν : Measure (KPGlobalTorusFunctionData.Adeles F) => ∫ x, k x ∂ν) hm
  rw [integral_smul_nnreal_measure, integral_smul_measure,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hn.le] at hh
  have he : (m : ℂ) * (‖a.val.1‖ : ℂ)⁻¹ = 1 := by
    apply mul_right_cancel₀ hi
    simpa [NNReal.smul_def, RCLike.real_smul_eq_coe_mul, mul_assoc, μ] using hh
  have he' : (m : ℂ) = (‖a.val.1‖ : ℂ) := by
    have he'' := congrArg (fun x : ℂ => x * (‖a.val.1‖ : ℂ)) he
    simpa [mul_assoc, Complex.ofReal_ne_zero.mpr hn.ne'] using he''
  exact_mod_cast he'

theorem arch_idele_integral_mul_inv
    (μ : Measure (KPGlobalTorusFunctionData.Adeles F)) [μ.IsAddHaarMeasure]
    (a : (KPGlobalTorusFunctionData.Adeles F)ˣ) (ha : a.val.2 = 1)
    (k : KPGlobalTorusFunctionData.Adeles F → ℂ) (_hi : Integrable k μ) :
    (∫ x, k (x * (↑a⁻¹ : KPGlobalTorusFunctionData.Adeles F)) ∂μ) =
      (‖a.val.1‖ : ℂ) * ∫ x, k x ∂μ := by
  let T := ContinuousAddEquiv.mulLeft a
  let m := addEquivAddHaarChar T
  have hm := addEquivAddHaarChar_smul_map μ T.symm
  rw [addEquivAddHaarChar_symm] at hm
  have hmap : μ.map T.symm = m • μ := by
    have hh := congrArg (fun ν : Measure (KPGlobalTorusFunctionData.Adeles F) => m • ν) hm
    simpa [m, smul_smul, mul_inv_cancel₀ (addEquivAddHaarChar_pos T).ne'] using hh
  have he : ⇑T.symm.toMeasurableEquiv = fun x : KPGlobalTorusFunctionData.Adeles F =>
      x * (↑a⁻¹ : KPGlobalTorusFunctionData.Adeles F) := by
    ext x
    apply T.injective
    change T (T.symm x) = (↑a : KPGlobalTorusFunctionData.Adeles F) * (x * ↑a⁻¹)
    rw [T.apply_symm_apply, mul_left_comm, Units.mul_inv, mul_one]
  have hh := integral_map_equiv (μ := μ) T.symm.toMeasurableEquiv k
  rw [he] at hh
  have heT : ⇑T.symm = fun x : KPGlobalTorusFunctionData.Adeles F => x * ↑a⁻¹ := he
  rw [heT] at hmap
  rw [← hh, hmap, integral_smul_nnreal_measure]
  change ((addEquivAddHaarChar (ContinuousAddEquiv.mulLeft a) : ℝ) : ℂ) * _ = _
  rw [arch_idele_intrinsicHaarChar a ha]
end DedekindZetaZeroFree.CompactPeriodAnalyticity.ArchHaar

end

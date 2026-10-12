module

public import DedekindZetaZeroFree.Adeles.Haar.FiniteRestrictedProductMeasure
public import DedekindZetaZeroFree.Metaplectic.Torus.CubicHeisenbergInducingData
public import DedekindZetaZeroFree.LFunctions.Tate.ArchimedeanAdditiveHaarScaling
public import DedekindZetaZeroFree.Metaplectic.Intertwining.TorusCovariance.AdelicDilationJacobian

@[expose] public section

noncomputable section
open MeasureTheory NumberField IsDedekindDomain
open scoped Classical NumberField ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ScatteringResidue
variable {F : Type} [Field F] [NumberField F]

private theorem integral_preimage (a : FiniteIdeleGroup F)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ha : a ∈ FiniteIdeleGroup.supportedAt (S : Set _)) :
    (fun x : FiniteHaarCharts.Adeles F =>
      (IdeleGroup.finiteEquivFiniteAdeleUnits a).val * x) ⁻¹'
      FiniteHaarNormalization.integralCompact F =
      FiniteHaarCharts.cylinder F S
        (fun v => (fun x => (a v.val).val * x) ⁻¹' v.val.adicCompletionIntegers F) := by
  rw [FiniteHaarNormalization.integralCompact_eq_coordinatewise]
  ext x
  change (∀ v, (a v).val * x v ∈ v.adicCompletionIntegers F) ↔
    ((∀ v : S, (a v.val).val * x v.val ∈ v.val.adicCompletionIntegers F) ∧
      ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F)
  constructor
  · intro hx
    refine ⟨fun v => hx v.val, ?_⟩
    intro v hv
    have hu := (Submonoid.mem_units_iff _ _).mp (ha v hv)
    have hh := (v.adicCompletionIntegers F).mul_mem _ _ hu.2 (hx v)
    simpa [← mul_assoc] using hh
  · rintro ⟨hx, ht⟩ v
    by_cases hv : v ∈ S
    · exact hx ⟨v, hv⟩
    · have hu := (Submonoid.mem_units_iff _ _).mp (ha v hv)
      exact (v.adicCompletionIntegers F).mul_mem _ _ hu.1 (ht v hv)

private theorem local_preimage_mass (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) :
    (localNormalizedHaar F v ((fun x => a.val * x) ⁻¹' v.adicCompletionIntegers F)).toReal =
      ‖a.val‖⁻¹ * FiniteHaarCharts.localMass F v := by
  have hs : MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    (KPAdelicTopology.completionIntegers_isOpen F v).measurableSet
  have he := congrArg (fun μ : Measure (v.adicCompletion F) =>
    (μ (v.adicCompletionIntegers F)).toReal)
    (CompletionHaarModule.map_mul F v (localNormalizedHaar F v) a)
  rw [Measure.map_apply (by fun_prop) hs, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (norm_nonneg _)] at he
  exact he

private theorem finite_intrinsic_char (a : FiniteIdeleGroup F)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ha : a ∈ FiniteIdeleGroup.supportedAt (S : Set _)) :
    (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft
      (IdeleGroup.finiteEquivFiniteAdeleUnits a)) : ℝ) =
      ∏ v : S, ‖(a v.val).val‖ := by
  let μ := FiniteHaarNormalization.measure F
  let e := ContinuousAddEquiv.mulLeft (IdeleGroup.finiteEquivFiniteAdeleUnits a)
  have hm := addEquivAddHaarChar_smul_preimage μ
    (X := FiniteHaarNormalization.integralCompact F) e
  have hmass := congrArg ENNReal.toReal hm
  rw [ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal] at hmass
  have hc := FiniteHaarCharts.measure_cylinder F S
    (fun v => (fun x => (a v.val).val * x) ⁻¹' v.val.adicCompletionIntegers F)
    (fun v => (KPAdelicTopology.completionIntegers_isOpen F v.val).measurableSet.preimage
      (by fun_prop))
  have hp : (μ (e ⁻¹' FiniteHaarNormalization.integralCompact F)).toReal =
      (∏ v : S, ‖(a v.val).val‖)⁻¹ * FiniteHaarNormalization.kappa F := by
    change (FiniteHaarNormalization.measure F ((fun x =>
      (IdeleGroup.finiteEquivFiniteAdeleUnits a).val * x) ⁻¹'
      FiniteHaarNormalization.integralCompact F)).toReal = _
    rw [integral_preimage a S ha, hc, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (FiniteHaarCharts.tailMass_pos F S).le, ENNReal.toReal_prod]
    simp_rw [local_preimage_mass]
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      FiniteHaarCharts.tailMass_eq_kappa_div]
    have hn : (∏ v : S, FiniteHaarCharts.localMass F v) ≠ 0 :=
      (Finset.prod_pos (fun v _ => FiniteHaarCharts.localMass_pos F v.val)).ne'
    have he : (∏ v ∈ S, FiniteHaarCharts.localMass F v) =
        ∏ v : S, FiniteHaarCharts.localMass F v.val :=
      Finset.prod_subtype S (p := fun v => v ∈ S) (by simp) _
    rw [he]
    field_simp
  rw [hp, FiniteHaarNormalization.measure_integralCompact_toReal] at hmass
  have hk := (FiniteHaarNormalization.kappa_pos F).ne'
  have hn : (∏ v : S, ‖(a v.val).val‖) ≠ 0 :=
    (Finset.prod_pos (fun v _ => norm_pos_iff.mpr (a v.val).ne_zero)).ne'
  have hh : (addEquivAddHaarChar e : ℝ) * (∏ v : S, ‖(a v.val).val‖)⁻¹ = 1 := by
    apply (mul_right_cancel₀ hk)
    simpa [mul_assoc] using hmass
  have hh' := congrArg (fun x : ℝ => x * (∏ v : S, ‖(a v.val).val‖)) hh
  rw [mul_assoc, inv_mul_cancel₀ hn, mul_one, one_mul] at hh'
  exact hh'

private theorem finite_arithmetic_norm (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : FiniteIdeleGroup F) (ha : a ∈ FiniteIdeleGroup.supportedAt (S : Set _)) :
    (∏ v : S, ‖(a v.val).val‖) = (((FiniteIdeleGroup.absoluteNorm a : ℝ≥0) : ℝ))⁻¹ := by
  have hlocal (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
      ‖x.val‖ = ((FiniteIdeleGroup.primeNorm v : ℝ≥0) : ℝ) ^
        (-(FiniteIdeleGroup.localOrder v x).toAdd) := by
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
    simp [FiniteIdeleGroup.localOrder_apply, FiniteIdeleGroup.primeNorm]
  have hs : (FiniteIdeleGroup.valuationVector a).toAdd.support ⊆ S := by
    intro v hv
    by_contra h
    exact (Finsupp.mem_support_iff.mp hv)
      ((FiniteIdeleGroup.localOrder_eq_zero_iff v (a v)).mpr (ha v h))
  rw [FiniteIdeleGroup.absoluteNorm_apply, Finsupp.prod]
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, NNReal.coe_prod, NNReal.coe_zpow]
  simp_rw [hlocal, zpow_neg]
  rw [← Finset.prod_subtype S (p := fun v => v ∈ S) (by simp)
    (fun v => (((FiniteIdeleGroup.primeNorm v : ℝ≥0) : ℝ) ^
      (FiniteIdeleGroup.localOrder v (a v)).toAdd)⁻¹)]
  rw [Finset.prod_inv_distrib]
  congr 1
  symm
  apply Finset.prod_subset hs
  intro v hv hvs
  simp [Finsupp.notMem_support_iff.mp hvs]

theorem finite_idele_intrinsicHaarChar (a : FiniteIdeleGroup F) :
    (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft
      (IdeleGroup.finiteEquivFiniteAdeleUnits a)) : ℝ) =
      (((FiniteIdeleGroup.absoluteNorm a : ℝ≥0) : ℝ))⁻¹ := by
  obtain ⟨S, hS⟩ := FiniteIdeleGroup.exists_finset_supportedAt a
  rw [finite_intrinsic_char a S hS, finite_arithmetic_norm S a hS]

theorem finite_idele_map_mul (a : FiniteIdeleGroup F)
    (μ : Measure (FiniteAdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] :
    Measure.map (fun x => (IdeleGroup.finiteEquivFiniteAdeleUnits a).val * x) μ =
      (ENNReal.ofReal (((FiniteIdeleGroup.absoluteNorm a : ℝ≥0) : ℝ))) • μ := by
  have h := addEquivAddHaarChar_smul_map μ
    (ContinuousAddEquiv.mulLeft (IdeleGroup.finiteEquivFiniteAdeleUnits a))
  have hc : addEquivAddHaarChar (ContinuousAddEquiv.mulLeft
      (IdeleGroup.finiteEquivFiniteAdeleUnits a)) = (FiniteIdeleGroup.absoluteNorm a : ℝ≥0)⁻¹ := by
    apply NNReal.coe_injective
    simpa using finite_idele_intrinsicHaarChar a
  rw [hc] at h
  have hn : (FiniteIdeleGroup.absoluteNorm a : ℝ≥0) ≠ 0 := Units.ne_zero _
  have hh := congrArg (fun ν => (FiniteIdeleGroup.absoluteNorm a : ℝ≥0) • ν) h
  rw [smul_smul, mul_inv_cancel₀ hn, one_smul] at hh
  change Measure.map (fun x => (IdeleGroup.finiteEquivFiniteAdeleUnits a).val * x) μ =
    (FiniteIdeleGroup.absoluteNorm a : ℝ≥0) • μ at hh
  simpa only [ENNReal.ofReal_coe_nnreal, ENNReal.smul_def] using hh

private theorem global_map_arithmetic (a : (KPGlobalTorusFunctionData.Adeles F)ˣ) :
    Measure.map (fun x : KPGlobalTorusFunctionData.Adeles F => a.val * x)
      (KPAdditiveHaar.adelicMeasure F) =
      ((ENNReal.ofReal ‖a.val.1‖)⁻¹ * ENNReal.ofReal
        (((FiniteIdeleGroup.absoluteNorm
          ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm a).2 : ℝ≥0) : ℝ))) •
      KPAdditiveHaar.adelicMeasure F := by
  let μa := KPAdditiveHaar.archMeasure F
  let μf := KPAdditiveHaar.finiteMeasure F
  let : μa.IsAddHaarMeasure := KPAdditiveHaar.archMeasure_isAddHaarMeasure F
  let : μf.IsAddHaarMeasure := KPAdditiveHaar.finiteMeasure_isAddHaarMeasure F
  let d : (InfiniteAdeleRing F)ˣ := Units.map (RingHom.fst _ _).toMonoidHom a
  let b := ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm a).2
  have hb : (IdeleGroup.finiteEquivFiniteAdeleUnits b).val = a.val.2 := by
    exact congrArg (fun u : KPAdelicCoverRestrictedProduct.Ideles F => u.val.2)
      ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).apply_symm_apply a)
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
      (fun x : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F => a.val.2 * x)) :=
    (continuous_const.mul continuous_id).measurable.prodMap
      (continuous_const.mul continuous_id).measurable
  have harch : Measure.map (fun x : InfiniteAdeleRing F => d.val * x) μa =
      (ENNReal.ofReal ‖d.val‖)⁻¹ • μa := TateSLocalMeasurability.archimedean_map_mul F d
  have hfinite : Measure.map (fun x => a.val.2 * x) μf =
      ENNReal.ofReal (((FiniteIdeleGroup.absoluteNorm b : ℝ≥0) : ℝ)) • μf := by
    simpa only [hb] using finite_idele_map_mul b μf
  have hprod : Measure.map (Prod.map (fun x : InfiniteAdeleRing F => d.val * x)
      (fun x : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F => a.val.2 * x)) (μa.prod μf) =
      ((ENNReal.ofReal ‖d.val‖)⁻¹ *
        ENNReal.ofReal (((FiniteIdeleGroup.absoluteNorm b : ℝ≥0) : ℝ))) • (μa.prod μf) := by
    rw [← Measure.map_prod_map μa μf (by fun_prop) (by fun_prop),
      harch, hfinite, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  change Measure.map _ (Measure.map cast (μa.prod μf)) =
    _ • Measure.map cast (μa.prod μf)
  rw [Measure.map_map hm hc]
  have he : (fun x : KPGlobalTorusFunctionData.Adeles F => a.val * x) ∘ cast =
      cast ∘ Prod.map (fun x : InfiniteAdeleRing F => d.val * x)
        (fun x : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F => a.val.2 * x) := rfl
  rw [he, ← Measure.map_map hc hp, hprod, Measure.map_smul _ hc.aemeasurable]
  rfl

private theorem global_ideleAbs (a : (KPGlobalTorusFunctionData.Adeles F)ˣ) :
    (((KPGlobalTorusFunctionData.ideleAbs F a : ℝ≥0) : ℝ)) =
      ‖a.val.1‖ / (((FiniteIdeleGroup.absoluteNorm
        ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm a).2 : ℝ≥0) : ℝ)) := by
  have hw (w : NumberField.InfinitePlace F) :
      ((InfiniteIdeleGroup.component w
        ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm a).1 : w.Completionˣ) : w.Completion) =
        a.val.1 w := by
    exact congrArg (fun u : KPAdelicCoverRestrictedProduct.Ideles F => u.val.1 w)
      ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).apply_symm_apply a)
  have harch : (((InfiniteIdeleGroup.archimedeanNorm
      ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm a).1 : ℝ≥0) : ℝ)) =
      ‖a.val.1‖ := by
    rw [InfiniteIdeleGroup.archimedeanNorm_apply, InfiniteAdeleRing.norm_def]
    simp only [Units.coe_prod, Units.val_pow_eq_pow_val, nnnormUnitHom_val,
      NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm, hw]
  change (((IdeleGroup.absoluteNorm
    ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm a))⁻¹ : ℝ≥0ˣ) : ℝ) = _
  rw [IdeleGroup.absoluteNorm_apply]
  simp only [Units.val_inv_eq_inv_val, Units.val_mul, NNReal.coe_inv, NNReal.coe_mul]
  rw [mul_inv_rev, inv_inv, harch]
  simp only [div_eq_mul_inv]

theorem idele_intrinsicHaarChar_eq_ideleAbs (a : (KPGlobalTorusFunctionData.Adeles F)ˣ) :
    (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft a) : ℝ) =
      (((KPGlobalTorusFunctionData.ideleAbs F a : ℝ≥0) : ℝ)) := by
  let μ := KPAdditiveHaar.adelicMeasure F
  let := KPAdditiveHaar.adelicMeasure_isAddHaarMeasure F
  let m := addEquivAddHaarChar (ContinuousAddEquiv.mulLeft a)
  let b := ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm a).2
  let q : ℝ := ((FiniteIdeleGroup.absoluteNorm b : ℝ≥0) : ℝ)
  have hm := addEquivAddHaarChar_smul_map μ (ContinuousAddEquiv.mulLeft a)
  change m • Measure.map (fun x => a.val * x) μ = μ at hm
  rw [global_map_arithmetic a] at hm
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
  have hq : 0 < q := by
    exact_mod_cast (show (0 : ℝ≥0) < (FiniteIdeleGroup.absoluteNorm b : ℝ≥0) from
      pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hh := congrArg (fun ν : Measure (KPGlobalTorusFunctionData.Adeles F) => ∫ x, k x ∂ν) hm
  rw [integral_smul_nnreal_measure, integral_smul_measure,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hn.le,
    ENNReal.toReal_ofReal hq.le] at hh
  have he : (m : ℂ) * ((‖a.val.1‖ : ℂ)⁻¹ * (q : ℂ)) = 1 := by
    apply mul_right_cancel₀ hi
    simpa [NNReal.smul_def, RCLike.real_smul_eq_coe_mul, mul_assoc, μ, q, b] using hh
  have he' : (m : ℂ) = (‖a.val.1‖ : ℂ) / (q : ℂ) := by
    have hh' := congrArg (fun x : ℂ => x * ((‖a.val.1‖ : ℂ) / (q : ℂ))) he
    have hn' : (‖a.val.1‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
    have hq' : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
    field_simp [hn', hq'] at hh' ⊢
    exact hh'
  rw [global_ideleAbs a]
  exact_mod_cast he'

theorem idele_integral_mul_inv
    (μ : Measure (KPGlobalTorusFunctionData.Adeles F)) [μ.IsAddHaarMeasure]
    (a : (KPGlobalTorusFunctionData.Adeles F)ˣ) (k : KPGlobalTorusFunctionData.Adeles F → ℂ) :
    (∫ x, k (x * (↑a⁻¹ : KPGlobalTorusFunctionData.Adeles F)) ∂μ) =
      (((KPGlobalTorusFunctionData.ideleAbs F a : ℝ≥0) : ℝ) : ℂ) * ∫ x, k x ∂μ := by
  rw [adelic_integral_mul_idele_inv μ a k, idele_intrinsicHaarChar_eq_ideleAbs a]

end DedekindZetaZeroFree.KPGlobalResidualKernel.ScatteringResidue

end

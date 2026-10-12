module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.TensorLogarithmicDerivativeEnvelopes
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.TensorSheetBounds

@[expose] public section

namespace DedekindZetaZeroFree.ProbeSheetFourierMellinBounds
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory
variable {F : Type} [Field F] [NumberField F]

lemma raw_radial_envelope_nonneg (A : SArithmeticData F) (N : ℕ) (R : ℝ)
    (x : SLocalProduct F A.Sf) : 0 ≤ radialFiniteEnvelopeRaw A N R x := by
  unfold radialFiniteEnvelopeRaw
  apply mul_nonneg
  · exact Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (by positivity) _
  · split_ifs <;> norm_num

namespace EnvelopeSheetPrivate
open Set

private lemma scalar_integrable (σ : ℝ) (N : ℕ) (hs : 0 < σ) (hN : σ < N) :
    IntegrableOn (fun r : ℝ => r ^ (2*σ-1) * (1+r^2)^(-(N:ℝ))) (Ioi 0) := by
  have hm : Measurable (fun r : ℝ => r ^ (2*σ-1) * (1+r^2)^(-(N:ℝ))) := by fun_prop
  have hn : IntegrableOn (fun r : ℝ => r ^ (2*σ-1) * (1+r^2)^(-(N:ℝ))) (Ioc 0 1) := by
    have hi : IntegrableOn (fun r : ℝ => r ^ (2*σ-1)) (Ioo 0 1) := by
      rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ) < 1)]
      linarith
    have hi' : IntegrableOn (fun r : ℝ => r ^ (2*σ-1)) (Ioc 0 1) := hi.congr_set_ae Ioo_ae_eq_Ioc.symm
    apply hi'.mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 < r := hr.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ r ^ (2*σ-1) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg r]) (neg_nonpos.mpr (Nat.cast_nonneg N))
      _ = _ := mul_one _
  have hf : IntegrableOn (fun r : ℝ => r ^ (2*σ-1) * (1+r^2)^(-(N:ℝ))) (Ioi 1) := by
    have hi := integrableOn_Ioi_rpow_of_lt (a := 2*σ-1-2*N) (c := 1) (by linarith) (by norm_num)
    apply hi.mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := lt_trans (by norm_num) hr
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ r ^ (2*σ-1) * (r^2)^(-(N:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (neg_nonpos.mpr (Nat.cast_nonneg N))
      _ = r ^ (2*σ-1-2*N) := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr0.le, ← Real.rpow_add hr0]
        congr 1
        ring
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)] using hn.union hf

private lemma complex_integrable (σ : ℝ) (N : ℕ) (hs : 0 < σ) (hN : σ < N) :
    Integrable (fun z : ℂ => (1+‖z‖^2)^(-(N:ℝ)) * (‖z‖^2)^σ)
      (volume.withDensity (fun z : ℂ => ENNReal.ofReal ((Real.pi*‖z‖^2)⁻¹))) := by
  have hd : Measurable (fun z : ℂ => ENNReal.ofReal ((Real.pi*‖z‖^2)⁻¹)) := by fun_prop
  rw [integrable_withDensity_iff_integrable_smul₀' hd.aemeasurable
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  have hi : Integrable (fun z : ℂ => ‖z‖ ^ (2*σ-2) * (1+‖z‖^2)^(-(N:ℝ))) volume := by
    apply (integrable_fun_norm_addHaar (E := ℂ) (f := fun r : ℝ => r ^ (2*σ-2) * (1+r^2)^(-(N:ℝ))) volume).mpr
    have h := scalar_integrable σ N hs hN
    apply h.congr_fun _ measurableSet_Ioi
    intro r hr
    simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul]
    rw [← mul_assoc]
    conv_rhs => lhs; lhs; rw [← Real.rpow_one r]
    rw [← Real.rpow_add hr]
    congr 2
    ring
  apply (hi.const_mul Real.pi⁻¹).congr
  filter_upwards [(volume : Measure ℂ).ae_ne 0] with z hz
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul]
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hp : (‖z‖^2)^σ / (‖z‖^2) = ‖z‖ ^ (2*σ-2) := by
    rw [← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul hz0.le,
      ← Real.rpow_sub hz0]
    norm_num

  rw [mul_inv_rev]
  calc
    _ = Real.pi⁻¹ * (((‖z‖^2)^σ / (‖z‖^2)) * (1+‖z‖^2)^(-(N:ℝ))) := by rw [hp]
    _ = _ := by ring

 def cutoff (v : HeightOneSpectrum (𝓞 F)) (R : ℝ) (z : v.adicCompletion F) : ℝ :=
  if ‖z‖ ≤ R then 1 else 0
private lemma cutoff_lc (v : HeightOneSpectrum (𝓞 F)) (R : ℝ) (hR : 0 < R) :
    IsLocallyConstant (cutoff v R) := by
  have hc := IsUltrametricDist.isClopen_closedBall (0 : v.adicCompletion F) hR.ne'
  have hl := ((LocallyConstant.const (v.adicCompletion F) (1 : ℝ)).indicator hc).isLocallyConstant
  convert hl using 1
  funext z
  change cutoff v R z = (Metric.closedBall (0 : v.adicCompletion F) R).indicator (fun _ => (1 : ℝ)) z
  simp [Set.indicator, Metric.mem_closedBall, dist_zero_right, cutoff]
set_option maxHeartbeats 800000 in
private lemma cutoff_integrable (v : HeightOneSpectrum (𝓞 F)) (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
    (ν : Measure (v.adicCompletion F)ˣ) [ν.IsHaarMeasure] :
    Integrable (fun z : (v.adicCompletion F)ˣ => cutoff v R z.val * ‖z.val‖ ^ σ) ν := by
  let g : v.adicCompletion F → ℂ := fun z => (cutoff v R z : ℂ)
  have hl : IsLocallyConstant g := by
    exact (cutoff_lc v R hR).comp Complex.ofReal
  have hc : HasCompactSupport g := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : v.adicCompletion F) R)
    intro z hz
    change (cutoff v R z : ℂ) = 0
    simp [cutoff, show ¬ ‖z‖ ≤ R from by simpa [Metric.mem_closedBall, dist_zero_right] using hz]
  have hi := (DedekindZetaZeroFree.ProbeSheetGlobalIntegrability.finiteUnitsMellin_integrable F v g hl hc ν (σ : ℂ) (by simpa using hσ)).norm
  convert hi using 1
  funext z
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr z.ne_zero)]
  simp only [Complex.ofReal_re, g, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by dsimp [cutoff]; split_ifs <;> norm_num)]

private lemma complex_units_integrable (σ : ℝ) (N : ℕ) (hs : 0 < σ) (hN : σ < N)
    (ν : Measure ℂˣ) [ν.IsHaarMeasure] :
    Integrable (fun z : ℂˣ => (1+‖z.val‖^2)^(-(N:ℝ)) * (‖z.val‖^2)^σ) ν := by
  letI : BorelSpace ℂˣ := ⟨by
    change (borel ℂ).comap Units.val = borel _
    rw [← borel_comap, ← Units.isOpenEmbedding_val.isEmbedding.isInducing.eq_induced]⟩
  letI : SecondCountableTopology ℂˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  let μ₀ : Measure ℂˣ := Measure.comap Units.val
    (volume.withDensity (fun z : ℂ => ENNReal.ofReal ((Real.pi*‖z‖^2)⁻¹)))
  letI : μ₀.IsHaarMeasure := complexUnits_density_isHaarMeasure volume
  have hi : Integrable (fun z : ℂˣ => (1+‖z.val‖^2)^(-(N:ℝ)) * (‖z.val‖^2)^σ) μ₀ :=
    IsOpenUnits.isOpenEmbedding_unitsVal.measurableEmbedding.integrableOn_range_iff_comap.mp
      (complex_integrable σ N hs hN).integrableOn
  rw [Measure.isMulLeftInvariant_eq_smul ν μ₀]
  exact hi.smul_measure ENNReal.coe_ne_top

private lemma weighted_bound (σ : ℝ) (N : ℕ) (hs : 0 < σ) (hN : σ < N) (r : ℝ) (hr : 0 ≤ r) :
    (1+r)^(-(N:ℝ)) * r^σ ≤ 1 := by
  by_cases hr1 : r ≤ 1
  · calc
      _ ≤ 1 * 1 := mul_le_mul
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (neg_nonpos.mpr (Nat.cast_nonneg N)))
        (Real.rpow_le_one hr hr1 hs.le) (by positivity) (by norm_num)
      _ = _ := one_mul _
  · have hr0 : 0 < r := lt_trans (by norm_num) (lt_of_not_ge hr1)
    calc
      _ ≤ r^(-(N:ℝ)) * r^σ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hr0 (by linarith) (neg_nonpos.mpr (Nat.cast_nonneg N))) (by positivity)
      _ = r^(-(N:ℝ)+σ) := (Real.rpow_add hr0 _ _).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt (lt_of_not_ge hr1)) (by linarith)

private lemma weighted_identity (A : SArithmeticData F) (N : ℕ) (R σ : ℝ)
    (y : (SLocalProduct F A.Sf)ˣ) :
    radialFiniteEnvelopeRaw A N R y.val * (ProbeWeight.modulus F A.Sf y)^σ =
      (∏ v : {v : InfinitePlace F // v.IsComplex},
        (1+‖((InfiniteAdeleRing.ringEquiv_mixedSpace F y.val.1).2 v)‖^2)^(-(N:ℝ)) *
        (‖((InfiniteAdeleRing.ringEquiv_mixedSpace F y.val.1).2 v)‖^2)^σ) *
      ∏ v : ↥A.Sf, cutoff v.val R (y.val.2 v) * ‖y.val.2 v‖^σ := by
  have hc : (if ∀ v : ↥A.Sf, ‖y.val.2 v‖ ≤ R then (1 : ℝ) else 0) =
      ∏ v : ↥A.Sf, cutoff v.val R (y.val.2 v) := by
    by_cases h : ∀ v : ↥A.Sf, ‖y.val.2 v‖ ≤ R
    · simp [h, cutoff]
    · obtain ⟨v, hv⟩ := not_forall.mp h
      rw [if_neg h]
      exact (Finset.prod_eq_zero (Finset.mem_univ v) (by simp [cutoff, hv])).symm
  have he : (∏ v : InfinitePlace F, (1+‖y.val.1 v‖^2)^(-(N:ℝ))) =
      ∏ v : {v : InfinitePlace F // v.IsComplex},
        (1+‖((InfiniteAdeleRing.ringEquiv_mixedSpace F y.val.1).2 v)‖^2)^(-(N:ℝ)) := by
    apply Fintype.prod_equiv (Equiv.subtypeUnivEquiv A.complex_place).symm
    intro v
    have hn := (InfinitePlace.Completion.isometry_extensionEmbedding v).dist_eq (y.val.1 v) 0
    change (1+‖y.val.1 v‖^2)^(-(N:ℝ)) =
      (1+‖InfinitePlace.Completion.extensionEmbedding v (y.val.1 v)‖^2)^(-(N:ℝ))
    have hn' : ‖InfinitePlace.Completion.extensionEmbedding v (y.val.1 v)‖ = ‖y.val.1 v‖ := by
      simpa only [map_zero, dist_zero_right] using hn
    rw [hn']
  unfold radialFiniteEnvelopeRaw
  rw [hc, he, SchwartzNormSheetEnvelope.complex_product_modulus,
    Real.mul_rpow (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)),
    ← Real.finsetProd_rpow _ _ (fun _ _ => sq_nonneg _),
    ← Real.finsetProd_rpow _ _ (fun _ _ => norm_nonneg _)]
  simp only [Finset.prod_mul_distrib]
  ring

end EnvelopeSheetPrivate

set_option maxHeartbeats 1000000 in

theorem raw_radial_envelope_sheet_bounds
    (A : SArithmeticData F)
    (dt : @Measure A.G1 (borel _))
    (hdt : @Measure.IsHaarMeasure A.G1 _ _ (borel _) dt)
    (σ : ℝ) (N : ℕ) (R : ℝ)
    (hσ : 0 < σ) (hN : σ < (N : ℝ)) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      Integrable (fun t => radialFiniteEnvelopeRaw A N R
        (sheetPointRaw A T t).val) dt ∧
      (∫ t, radialFiniteEnvelopeRaw A N R (sheetPointRaw A T t).val ∂dt) ≤
        C * T ^ (-σ) := by
  letI : MeasurableSpace A.G1 := borel _
  letI : BorelSpace A.G1 := ⟨rfl⟩
  letI : BorelSpace ℂˣ := ⟨by
    change (borel ℂ).comap Units.val = borel _
    rw [← borel_comap, ← Units.isOpenEmbedding_val.isEmbedding.isInducing.eq_induced]⟩
  letI (v : ↥A.Sf) : BorelSpace (v.val.adicCompletion F)ˣ := ⟨by
    change (borel (v.val.adicCompletion F)).comap Units.val = borel _
    rw [← borel_comap, ← Units.isOpenEmbedding_val.isEmbedding.isInducing.eq_induced]⟩
  let w : {v : InfinitePlace F // v.IsComplex} :=
    ⟨Classical.arbitrary _, A.complex_place _⟩
  let ac := fun (_ : {v : InfinitePlace F // v.IsComplex}) (z : ℂ) =>
    (1+‖z‖^2)^(-(N:ℝ)) * (‖z‖^2)^σ
  let af := fun (v : ↥A.Sf) (z : v.val.adicCompletion F) =>
    EnvelopeSheetPrivate.cutoff v.val R z * ‖z‖^σ
  have hcc : ∀ v, Continuous (ac v) := by
    intro v
    exact ((continuous_const.add (continuous_norm.pow 2)).rpow_const (fun z : ℂ => Or.inl (ne_of_gt (show 0 < (1 : ℝ) + ‖z‖^2 by positivity)))).mul
      ((continuous_norm.pow 2).rpow_const (fun _ => Or.inr hσ.le))
  have hfc : ∀ v, Continuous (af v) := by
    intro v
    exact (EnvelopeSheetPrivate.cutoff_lc v.val R hR).continuous.mul
      (continuous_norm.rpow_const (fun _ => Or.inr hσ.le))
  have hcpos : ∀ v z, 0 ≤ ac v z := by intros; positivity
  have hfpos : ∀ v z, 0 ≤ af v z := by
    intro v z
    dsimp [af, EnvelopeSheetPrivate.cutoff]
    split_ifs <;> positivity
  obtain ⟨B, hB, hmass⟩ := NormSheetRemainingCoordinates.raw_remaining_tensor_integral_bound
    A w dt hdt ac af hcc hfc hcpos hfpos
    (fun _ => Measure.haar) (by intro v; infer_instance)
    (fun _ => Measure.haar) (by intro v; infer_instance)
    (fun _ => EnvelopeSheetPrivate.complex_units_integrable σ N hσ hN Measure.haar)
    (fun v => EnvelopeSheetPrivate.cutoff_integrable v.val R σ hR hσ Measure.haar)
  let M := fun T (t : A.G1) =>
    (∏ v ∈ Finset.univ.erase w, ac v
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F (sheetPointRaw A T t).val.1).2 v)) *
    ∏ v : ↥A.Sf, af v ((sheetPointRaw A T t).val.2 v)
  have hMpos : ∀ T t, 0 ≤ M T t := by
    intro T t
    exact mul_nonneg (Finset.prod_nonneg fun v _ => hcpos v _)
      (Finset.prod_nonneg fun v _ => hfpos v _)
  have hbound : ∀ T, 0 < T → ∀ t : A.G1,
      radialFiniteEnvelopeRaw A N R (sheetPointRaw A T t).val ≤ T^(-σ) * M T t := by
    intro T hT t
    have he := EnvelopeSheetPrivate.weighted_identity A N R σ (sheetPointRaw A T t)
    rw [SchwartzNormSheetEnvelope.raw_sheet_modulus A T hT t] at he
    change radialFiniteEnvelopeRaw A N R (sheetPointRaw A T t).val * T^σ =
      (∏ v, ac v ((InfiniteAdeleRing.ringEquiv_mixedSpace F
        (sheetPointRaw A T t).val.1).2 v)) * ∏ v, af v ((sheetPointRaw A T t).val.2 v) at he
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)] at he
    have hw : ac w ((InfiniteAdeleRing.ringEquiv_mixedSpace F
      (sheetPointRaw A T t).val.1).2 w) ≤ 1 :=
      EnvelopeSheetPrivate.weighted_bound σ N hσ hN _ (sq_nonneg _)
    have hh : radialFiniteEnvelopeRaw A N R (sheetPointRaw A T t).val * T^σ ≤ M T t := by
      rw [he]
      calc
        _ = ac w ((InfiniteAdeleRing.ringEquiv_mixedSpace F
          (sheetPointRaw A T t).val.1).2 w) * M T t := by dsimp [M]; ring
        _ ≤ 1 * M T t := mul_le_mul_of_nonneg_right hw (hMpos T t)
        _ = _ := one_mul _
    have hd := (le_div_iff₀ (Real.rpow_pos_of_pos hT σ)).mpr hh
    simpa only [div_eq_mul_inv, Real.rpow_neg hT.le, mul_comm] using hd
  have hmeas : ∀ T, 0 < T → AEStronglyMeasurable
      (fun t : A.G1 => radialFiniteEnvelopeRaw A N R (sheetPointRaw A T t).val) dt := by
    intro T hT
    apply Measurable.aestronglyMeasurable
    have hs := SchwartzNormSheetEnvelope.raw_sheet_continuous A T hT
    have ha (v : InfinitePlace F) : Continuous (fun t : A.G1 => ‖(sheetPointRaw A T t).val.1 v‖) :=
      ((continuous_apply v).comp (continuous_fst.comp hs)).norm
    have hf (v : ↥A.Sf) : Continuous (fun t : A.G1 => ‖(sheetPointRaw A T t).val.2 v‖) :=
      ((continuous_apply v).comp (continuous_snd.comp hs)).norm
    unfold radialFiniteEnvelopeRaw
    apply Measurable.mul
    · exact Finset.measurable_prod _ (fun v _ =>
        (continuous_const.add ((ha v).pow 2)).measurable.pow_const _)
    · apply measurable_const.ite _ measurable_const
      simpa only [Set.setOf_forall] using (MeasurableSet.iInter (fun v : ↥A.Sf =>
        measurableSet_le (hf v).measurable (measurable_const (a := R))))
  refine ⟨B, hB, ?_⟩
  intro T hT
  have hi : Integrable (fun t => T^(-σ) * M T t) dt := (hmass T hT).1.const_mul _
  have hf : Integrable (fun t => radialFiniteEnvelopeRaw A N R (sheetPointRaw A T t).val) dt :=
    hi.mono' (hmeas T hT) (Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (raw_radial_envelope_nonneg A N R _)]
      exact hbound T hT t))
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ t, T^(-σ) * M T t ∂dt := integral_mono hf hi (hbound T hT)
    _ = T^(-σ) * ∫ t, M T t ∂dt := integral_const_mul _ _
    _ ≤ T^(-σ) * B := mul_le_mul_of_nonneg_left (hmass T hT).2 (Real.rpow_nonneg hT.le _)
    _ = _ := mul_comm _ _

end
end DedekindZetaZeroFree.ProbeSheetFourierMellinBounds

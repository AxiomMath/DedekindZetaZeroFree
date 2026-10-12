module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PowerEnvelopes.ComplexIntegrability
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PowerEnvelopes.NonarchimedeanIntegrability
public import DedekindZetaZeroFree.Theta.Profiles.ProductPowerMajorant
public import DedekindZetaZeroFree.Adeles.Quotients.NormSheets.RemainingCoordinateIntegrals

@[expose] public section

namespace DedekindZetaZeroFree.ThetaRawSheetEnvelope.WeightedWhittakerSheets
noncomputable section
open MeasureTheory NumberField
open scoped Classical
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

theorem archPowerMajorant_le_rpow_neg (B s r : ℝ) (hr : 0 < r)
    (hs : -(1 / 4 : ℝ) < s) (hBs : s < B) :
    archPowerMajorant B r ≤ (r ^ (-s)) := by
  rw [archPowerMajorant, min_le_iff]
  by_cases h1 : r ≤ 1
  · exact Or.inl (Real.rpow_le_rpow_of_exponent_ge hr h1 (by linarith))
  · exact Or.inr (Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge h1)) (by linarith))

theorem productPowerMajorant_le_sheet_bound (A : SArithmeticData F)
    (v₀ : InfinitePlace F) (M B s : ℝ) (hM : 0 < M)
    (hs : -(1 / 4 : ℝ) < s) (hBs : s < B)
    (x : ThetaProfileHaarSheets.PositiveAxis) (y : A.G) (hy : A.norm y = (x : ℝ)) :
    productPowerMajorant A M B y ≤
      ((x : ℝ) ^ (-s)) *
        ((∏ w ∈ Finset.univ.erase v₀,
            ((‖(y.1 w : w.Completion)‖ ^ 2) ^ s) *
              archPowerMajorant B (‖(y.1 w : w.Completion)‖ ^ 2)) *
          ∏ v : A.Sf, (‖(y.2 v : v.val.adicCompletion F)‖ ^ s) *
            finitePowerMajorant M ‖(y.2 v : v.val.adicCompletion F)‖) := by
  classical
  have hnorm : (∏ w : InfinitePlace F, ‖(y.1 w : w.Completion)‖ ^ 2) *
      (∏ v : A.Sf, ‖(y.2 v : v.val.adicCompletion F)‖) = (x : ℝ) := hy
  set R : ℝ := (∏ w ∈ Finset.univ.erase v₀, ‖(y.1 w : w.Completion)‖ ^ 2) *
    (∏ v : A.Sf, ‖(y.2 v : v.val.adicCompletion F)‖) with hR
  have hsplit : (∏ w : InfinitePlace F, ‖(y.1 w : w.Completion)‖ ^ 2) =
      ‖(y.1 v₀ : v₀.Completion)‖ ^ 2 *
        ∏ w ∈ Finset.univ.erase v₀, ‖(y.1 w : w.Completion)‖ ^ 2 :=
    (Finset.mul_prod_erase Finset.univ
      (fun w : InfinitePlace F => ‖(y.1 w : w.Completion)‖ ^ 2) (Finset.mem_univ v₀)).symm
  have hRpos : 0 < R := by
    rw [hR]
    exact mul_pos
      (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (Units.ne_zero _)) 2)
      (Finset.prod_pos fun v _ => norm_pos_iff.mpr (Units.ne_zero _))
  have hrpos : 0 < ‖(y.1 v₀ : v₀.Completion)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (Units.ne_zero _)) 2
  have hxpos : (0 : ℝ) < (x : ℝ) := x.property
  have hkey : ‖(y.1 v₀ : v₀.Completion)‖ ^ 2 * R = (x : ℝ) := by
    rw [hR, ← mul_assoc, ← hsplit]
    exact hnorm
  have hmul : ((x : ℝ) ^ (-s)) =
      ((‖(y.1 v₀ : v₀.Completion)‖ ^ 2) ^ (-s)) * (R ^ (-s)) := by
    rw [← hkey]
    exact Real.mul_rpow hrpos.le hRpos.le
  have hcancel : (R ^ (-s)) * (R ^ s) = 1 := by
    have h := Real.rpow_add hRpos (-s) s
    rw [neg_add_cancel, Real.rpow_zero] at h
    exact h.symm
  have hdist : ((‖(y.1 v₀ : v₀.Completion)‖ ^ 2) ^ (-s)) =
      ((x : ℝ) ^ (-s)) * (R ^ s) := by
    calc ((‖(y.1 v₀ : v₀.Completion)‖ ^ 2) ^ (-s))
        = ((‖(y.1 v₀ : v₀.Completion)‖ ^ 2) ^ (-s)) * 1 := (mul_one _).symm
      _ = ((‖(y.1 v₀ : v₀.Completion)‖ ^ 2) ^ (-s)) *
            ((R ^ (-s)) * (R ^ s)) := by rw [hcancel]
      _ = (((‖(y.1 v₀ : v₀.Completion)‖ ^ 2) ^ (-s)) * (R ^ (-s))) *
            (R ^ s) := by ring
      _ = ((x : ℝ) ^ (-s)) * (R ^ s) := by rw [← hmul]
  have hRs : (R ^ s) =
      (∏ w ∈ Finset.univ.erase v₀, ((‖(y.1 w : w.Completion)‖ ^ 2) ^ s)) *
        ∏ v : A.Sf, (‖(y.2 v : v.val.adicCompletion F)‖ ^ s) := by
    have hP : ((∏ w ∈ Finset.univ.erase v₀, ‖(y.1 w : w.Completion)‖ ^ 2) ^ s) =
        ∏ w ∈ Finset.univ.erase v₀, ((‖(y.1 w : w.Completion)‖ ^ 2) ^ s) :=
      (Real.finsetProd_rpow _ (fun w : InfinitePlace F => ‖(y.1 w : w.Completion)‖ ^ 2)
        (fun w _ => pow_nonneg (norm_nonneg _) 2) s).symm
    have hQ : ((∏ v : A.Sf, ‖(y.2 v : v.val.adicCompletion F)‖) ^ s) =
        ∏ v : A.Sf, (‖(y.2 v : v.val.adicCompletion F)‖ ^ s) :=
      (Real.finsetProd_rpow _ (fun v : A.Sf => ‖(y.2 v : v.val.adicCompletion F)‖)
        (fun v _ => norm_nonneg _) s).symm
    have hm := Real.mul_rpow
      (x := ∏ w ∈ Finset.univ.erase v₀, ‖(y.1 w : w.Completion)‖ ^ 2)
      (y := ∏ v : A.Sf, ‖(y.2 v : v.val.adicCompletion F)‖) (z := s)
      (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 2)
      (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    rw [hR, hm, hP, hQ]
  have hg0 : archPowerMajorant B (‖(y.1 v₀ : v₀.Completion)‖ ^ 2) ≤
      ((x : ℝ) ^ (-s)) *
        ((∏ w ∈ Finset.univ.erase v₀, ((‖(y.1 w : w.Completion)‖ ^ 2) ^ s)) *
          ∏ v : A.Sf, (‖(y.2 v : v.val.adicCompletion F)‖ ^ s)) := by
    rw [← hRs]
    exact (archPowerMajorant_le_rpow_neg B s _ hrpos hs hBs).trans_eq hdist
  have hAf : 0 ≤ ∏ v : A.Sf,
      finitePowerMajorant M ‖(y.2 v : v.val.adicCompletion F)‖ :=
    Finset.prod_nonneg fun v _ => finitePowerMajorant_nonneg M _ (norm_nonneg _)
  have hAg : 0 ≤ ∏ w ∈ Finset.univ.erase v₀,
      archPowerMajorant B (‖(y.1 w : w.Completion)‖ ^ 2) :=
    Finset.prod_nonneg fun w _ =>
      archPowerMajorant_nonneg B _ (pow_nonneg (norm_nonneg _) 2)
  rw [productPowerMajorant, ← Finset.mul_prod_erase Finset.univ
    (fun w : InfinitePlace F => archPowerMajorant B (‖(y.1 w : w.Completion)‖ ^ 2))
    (Finset.mem_univ v₀)]
  calc (∏ v : A.Sf, finitePowerMajorant M ‖(y.2 v : v.val.adicCompletion F)‖) *
        (archPowerMajorant B (‖(y.1 v₀ : v₀.Completion)‖ ^ 2) *
          ∏ w ∈ Finset.univ.erase v₀,
            archPowerMajorant B (‖(y.1 w : w.Completion)‖ ^ 2))
      ≤ (∏ v : A.Sf, finitePowerMajorant M ‖(y.2 v : v.val.adicCompletion F)‖) *
        ((((x : ℝ) ^ (-s)) *
          ((∏ w ∈ Finset.univ.erase v₀, ((‖(y.1 w : w.Completion)‖ ^ 2) ^ s)) *
            ∏ v : A.Sf, (‖(y.2 v : v.val.adicCompletion F)‖ ^ s))) *
          ∏ w ∈ Finset.univ.erase v₀,
            archPowerMajorant B (‖(y.1 w : w.Completion)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg0 hAg) hAf
    _ = ((x : ℝ) ^ (-s)) *
        ((∏ w ∈ Finset.univ.erase v₀,
            ((‖(y.1 w : w.Completion)‖ ^ 2) ^ s) *
              archPowerMajorant B (‖(y.1 w : w.Completion)‖ ^ 2)) *
          ∏ v : A.Sf, (‖(y.2 v : v.val.adicCompletion F)‖ ^ s) *
            finitePowerMajorant M ‖(y.2 v : v.val.adicCompletion F)‖) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        ring

theorem sheetHaar_integral_eq (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (x : ThetaProfileHaarSheets.PositiveAxis)
    (F : A.G → ℝ) :
    (∫ y : ThetaProfileHaarSheets.Sheet A x, F y.val
        ∂ThetaProfileHaarSheets.sheetHaar A v₀ μG x) =
      ∫ z : A.G1,
        F (ThetaProfileHaarSheets.normSection A v₀ x * z.val)
          ∂ThetaProfileHaarSheets.kernelHaar A v₀ μG := by
  rw [ThetaProfileHaarSheets.sheetHaar]
  exact MeasureTheory.integral_map_equiv
    (ThetaProfileHaarSheets.sheetTranslation A v₀ x).toMeasurableEquiv
    (fun y : ThetaProfileHaarSheets.Sheet A x => F y.val)

set_option maxHeartbeats 1000000 in

theorem product_power_majorant_sheet_bound (A : SArithmeticData F)
    (v₀ : InfinitePlace F) (μG : Measure A.G) [μG.IsHaarMeasure]
    (M B s : ℝ) (hM : 0 < M) (hs : -(1 / 4 : ℝ) < s) (hBs : s < B) :
    ∃ E : ℝ, 0 < E ∧ ∀ x : ThetaProfileHaarSheets.PositiveAxis,
      Integrable (fun y : ThetaProfileHaarSheets.Sheet A x =>
        productPowerMajorant A M B y.val)
        (ThetaProfileHaarSheets.sheetHaar A v₀ μG x) ∧
      (∫ y : ThetaProfileHaarSheets.Sheet A x,
        productPowerMajorant A M B y.val
          ∂ThetaProfileHaarSheets.sheetHaar A v₀ μG x) ≤
        E * Real.rpow (x : ℝ) (-s) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : ∀ v : A.Sf, TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    fun v => TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI : ∀ v : A.Sf, SecondCountableTopology (v.val.adicCompletion F) := fun v => inferInstance
  letI : ∀ v : A.Sf, SecondCountableTopology (v.val.adicCompletion F)ᵐᵒᵖ :=
    fun v => MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI : ∀ v : A.Sf, SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    fun v => Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology ℂˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  letI : LocallyCompactSpace A.G1 := (NormSheetsCoordinates.normOne_geometry A).1
  letI : SecondCountableTopology A.G1 := (NormSheetsCoordinates.normOne_geometry A).2
  letI : BorelSpace ℂˣ := ⟨by
    change (borel ℂ).comap Units.val = borel _
    rw [← borel_comap, ← Units.isOpenEmbedding_val.isEmbedding.isInducing.eq_induced]⟩
  letI (v : A.Sf) : BorelSpace (v.val.adicCompletion F)ˣ := ⟨by
    change (borel (v.val.adicCompletion F)).comap Units.val = borel _
    rw [← borel_comap, ← Units.isOpenEmbedding_val.isEmbedding.isInducing.eq_induced]⟩
  let w : {v : InfinitePlace F // v.IsComplex} := ⟨v₀, A.complex_place v₀⟩
  let νC : NormSheetRemainingCoordinates.RemainingComplex w → Measure ℂˣ :=
    fun _ => Measure.haar
  let νF : (v : A.Sf) → Measure (v.val.adicCompletion F)ˣ := fun _ => Measure.haar
  let ν := NormSheetRemainingCoordinates.remainingProductMeasure A w νC νF
  let dt := ThetaProfileHaarSheets.kernelHaar A v₀ μG
  let P := NormSheetRemainingCoordinates.remainingProjection A w
  let f : NormSheetRemainingCoordinates.RemainingUnits A w → ℝ := fun z =>
    (∏ v, ((‖(z.1 v).val‖ ^ 2) ^ s) * archPowerMajorant B (‖(z.1 v).val‖ ^ 2)) *
      ∏ v : A.Sf, (‖(z.2 v).val‖ ^ s) * finitePowerMajorant M ‖(z.2 v).val‖
  have hf : Integrable f ν :=
    (Integrable.fintype_prod (fun v => weighted_archPowerMajorant_integrable
      (νC v) B s hs hBs)).mul_prod
      (Integrable.fintype_prod_dep (fun v => weighted_finitePowerMajorant_integrable
        v.val (νF v) M s hM hs))
  have hmb : (inferInstance : MeasurableSpace A.G1) = borel A.G1 :=
    BorelSpace.measurable_eq
  have hraw := NormSheetRemainingCoordinates.raw_remaining_projection_haar A w
  rw [← hmb] at hraw
  obtain ⟨hP, _, _, _, c, hc, hmap, _⟩ := hraw dt
    inferInstance νC (fun _ => inferInstance) νF (fun _ => inferInstance)
  have hmap' : Measure.map P dt = c • ν := hmap
  have hfi : Integrable (f ∘ P) dt := by
    apply Integrable.comp_measurable _ hP.measurable
    rw [hmap']
    exact hf.smul_measure_nnreal
  have hnonneg : ∀ z, 0 ≤ f z := by
    intro z
    exact mul_nonneg
      (Finset.prod_nonneg fun v _ => mul_nonneg (Real.rpow_nonneg (sq_nonneg _) _)
        (archPowerMajorant_nonneg B _ (sq_nonneg _)))
      (Finset.prod_nonneg fun v _ => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (finitePowerMajorant_nonneg M _ (norm_nonneg _)))
  let E := (∫ t, f (P t) ∂dt) + 1
  have hE : 0 < E := by
    have : 0 ≤ ∫ t, f (P t) ∂dt := integral_nonneg fun t => hnonneg _
    dsimp [E]
    linarith
  refine ⟨E, hE, ?_⟩
  intro x
  let g : ThetaProfileHaarSheets.Sheet A x → ℝ := fun y => productPowerMajorant A M B y.val
  let T := ThetaProfileHaarSheets.sheetTranslation A v₀ x
  have hbound : ∀ t : A.G1, g (T t) ≤ (x : ℝ) ^ (-s) * f (P t) := by
    intro t
    have hb := productPowerMajorant_le_sheet_bound A v₀ M B s hM hs hBs x
      (T t).val (T t).property
    have hv (v : InfinitePlace F) (hvv : v ≠ v₀) : (T t).val.1 v = t.val.1 v := by
      change (ThetaProfileHaarSheets.normSection A v₀ x).1 v * t.val.1 v = _
      rw [ThetaProfileHaarSheets.normSection_at_other_place A v₀ v hvv, one_mul]
    have hfin (v : A.Sf) : (T t).val.2 v = t.val.2 v := by
      change (ThetaProfileHaarSheets.normSection A v₀ x).2 v * t.val.2 v = _
      rw [ThetaProfileHaarSheets.normSection_at_finite_place, one_mul]
    have hcn (v : NormSheetRemainingCoordinates.RemainingComplex w) :
        ‖((P t).1 v).val‖ = ‖(t.val.1 v.val.val : v.val.val.Completion)‖ := by
      change ‖InfinitePlace.Completion.ringEquivComplexOfIsComplex v.val.property
        (t.val.1 v.val.val : v.val.val.Completion)‖ = _
      exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex v.val.property).isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex v.val.property)) _
    let e : NormSheetRemainingCoordinates.RemainingComplex w ≃
        {v : InfinitePlace F // v ≠ v₀} :=
      { toFun := fun v => ⟨v.val.val, fun h => v.property (Subtype.ext h)⟩
        invFun := fun v => ⟨⟨v.val, A.complex_place v.val⟩,
          fun h => v.property (congrArg Subtype.val h)⟩
        left_inv := fun v => by apply Subtype.ext; apply Subtype.ext; rfl
        right_inv := fun v => by rfl }
    have hprod : (∏ v : NormSheetRemainingCoordinates.RemainingComplex w,
        ((‖((P t).1 v).val‖ ^ 2) ^ s) * archPowerMajorant B (‖((P t).1 v).val‖ ^ 2)) =
        ∏ v ∈ Finset.univ.erase v₀, ((‖((T t).val.1 v : v.Completion)‖ ^ 2) ^ s) *
          archPowerMajorant B (‖((T t).val.1 v : v.Completion)‖ ^ 2) := by
      rw [Finset.prod_subtype (p := fun v : InfinitePlace F => v ≠ v₀)
        (Finset.univ.erase v₀)
        (fun v => by simp only [Finset.mem_erase, Finset.mem_univ, and_true])]
      apply Fintype.prod_equiv e
      intro v
      rw [hcn, hv _ (e v).property]
      rfl
    have heq : f (P t) =
        (∏ v ∈ Finset.univ.erase v₀, ((‖((T t).val.1 v : v.Completion)‖ ^ 2) ^ s) *
          archPowerMajorant B (‖((T t).val.1 v : v.Completion)‖ ^ 2)) *
        ∏ v : A.Sf, (‖((T t).val.2 v : v.val.adicCompletion F)‖ ^ s) *
          finitePowerMajorant M ‖((T t).val.2 v : v.val.adicCompletion F)‖ := by
      dsimp only [f]
      rw [hprod]
      congr 1
      apply Finset.prod_congr rfl
      intro v hv
      rw [hfin]
      rfl
    rw [heq]
    exact hb
  have hgmeas : AEStronglyMeasurable g (ThetaProfileHaarSheets.sheetHaar A v₀ μG x) := by
    apply Measurable.aestronglyMeasurable
    dsimp [g, productPowerMajorant]
    apply Measurable.mul
    · apply Finset.measurable_prod
      intro v hv
      unfold finitePowerMajorant
      apply Measurable.ite
      · exact measurableSet_le (by fun_prop) measurable_const
      · exact (show Continuous (fun y : ThetaProfileHaarSheets.Sheet A x =>
          ‖(y.val.2 v : v.val.adicCompletion F)‖ ^ (1 / 4 : ℝ)) from
          ((show Continuous (fun y : ThetaProfileHaarSheets.Sheet A x =>
            ‖(y.val.2 v : v.val.adicCompletion F)‖) by fun_prop).rpow_const
              (fun _ => Or.inr (by norm_num)))).measurable
      · exact measurable_const
    · apply Finset.measurable_prod
      intro v hv
      apply Continuous.measurable
      apply Continuous.min
      · exact (show Continuous (fun y : ThetaProfileHaarSheets.Sheet A x =>
          ‖(y.val.1 v : v.Completion)‖ ^ 2) by fun_prop).rpow_const
          (fun y => Or.inl (ne_of_gt (pow_pos (norm_pos_iff.mpr (Units.ne_zero _)) 2)))
      · exact (show Continuous (fun y : ThetaProfileHaarSheets.Sheet A x =>
          ‖(y.val.1 v : v.Completion)‖ ^ 2) by fun_prop).rpow_const
          (fun y => Or.inl (ne_of_gt (pow_pos (norm_pos_iff.mpr (Units.ne_zero _)) 2)))
  have hgT : AEStronglyMeasurable (g ∘ T) dt := by
    exact hgmeas.comp_measurable T.measurable
  have hiT : Integrable (g ∘ T) dt := by
    apply (hfi.const_mul ((x : ℝ) ^ (-s))).mono' hgT
    filter_upwards [] with t
    change ‖productPowerMajorant A M B (T t).val‖ ≤ (x : ℝ) ^ (-s) * f (P t)
    rw [Real.norm_eq_abs, abs_of_nonneg (productPowerMajorant_nonneg A M B _)]
    exact hbound t
  have hi : Integrable g (ThetaProfileHaarSheets.sheetHaar A v₀ μG x) := by
    exact (integrable_map_measure hgmeas T.measurable.aemeasurable).2 hiT
  refine ⟨hi, ?_⟩
  have heq : (∫ y, g y ∂ThetaProfileHaarSheets.sheetHaar A v₀ μG x) =
      ∫ t, g (T t) ∂dt := integral_map T.measurable.aemeasurable hgmeas
  rw [heq]
  calc (∫ t, g (T t) ∂dt)
      ≤ ∫ t, (x : ℝ) ^ (-s) * f (P t) ∂dt :=
        integral_mono hiT (hfi.const_mul _) hbound
    _ = (x : ℝ) ^ (-s) * (∫ t, f (P t) ∂dt) := integral_const_mul _ _
    _ ≤ E * (x : ℝ) ^ (-s) := by
      have : (∫ t, f (P t) ∂dt) ≤ E := by dsimp [E]; linarith
      simpa [mul_comm] using mul_le_mul_of_nonneg_left this (Real.rpow_nonneg x.property.le _)

end
end DedekindZetaZeroFree.ThetaRawSheetEnvelope.WeightedWhittakerSheets

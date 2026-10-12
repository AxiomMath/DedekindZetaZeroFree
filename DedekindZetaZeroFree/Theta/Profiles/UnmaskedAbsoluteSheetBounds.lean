module

public import DedekindZetaZeroFree.Theta.Profiles.AbsoluteSheetBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem sheet_class_norm {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (P : Packet R Q) (v : R.A.UnitQuotient) (y : R.A.G) :
    ‖T.sheetIntegrand P v (QuotientGroup.mk' R.A.sixthPowers y) y‖ =
      ‖MomentSources.fourier R Q.dq (T.theta v)
        (diagonal R y * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)‖ := by
  have hself : R.probe.correction.H (QuotientGroup.mk' R.A.sixthPowers y)
      (QuotientGroup.mk' R.A.sixthPowers y) = 1 := by
    rw [R.probe.correction.H_actual, ← R.A.H_S6_on_representatives,
      R.A.H_S6_alternating]
    rfl
  simp only [Realization.sheetIntegrand, mul_inv_cancel,
    if_pos R.probe.correction.B.one_mem, hself, Units.val_one, map_one,
    one_pow, inv_one, one_mul, norm_mul, DigitMasks.branch_norm, one_mul]

theorem unmasked_full_sheet_integrable (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (H : SameResidueProfiles R Q T P) (v : R.A.UnitQuotient) (x : PositiveAxis) :
    letI := N.groupHaar_isHaar;
    Integrable (fun y : Sheet R.A x => MomentSources.fourier R Q.dq (T.theta v)
      (diagonal R y.val * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12))
      (sheetHaar R.A P.v₀ N.groupHaar x) := by
  letI := N.groupHaar_isHaar
  letI := H.finite_classes
  letI : Fintype R.A.V := Fintype.ofFinite _
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  have hc : Continuous (fun y : Sheet R.A x => MomentSources.fourier R Q.dq (T.theta v)
      (diagonal R y.val * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)) :=
    (SheetRescaling.fourier_continuous T v).comp
      (((DigitMasks.diagonal_selected_continuous R).comp continuous_subtype_val).mul continuous_const)
  have hi := integrable_finset_sum Finset.univ (fun κ _ =>
    (selected_full_sheet_integrable R N T P H v κ x).norm)
  apply hi.mono' hc.aestronglyMeasurable
  filter_upwards [] with y
  rw [← sheet_class_norm R T P v y.val]
  exact Finset.single_le_sum (fun κ _ => norm_nonneg (T.sheetIntegrand P v κ y.val))
    (Finset.mem_univ (QuotientGroup.mk' R.A.sixthPowers y.val))

theorem unmasked_full_sheet_norm_bound (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (H : SameResidueProfiles R Q T P) (B : ℝ) (hB : 0 < B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v (x : PositiveAxis),
      letI := N.groupHaar_isHaar;
      (∫ y : Sheet R.A x, ‖MomentSources.fourier R Q.dq (T.theta v)
        (diagonal R y.val * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)‖
        ∂sheetHaar R.A P.v₀ N.groupHaar x) ≤
      K * min (Real.rpow x.val (1 / 8)) (Real.rpow x.val (-B)) := by
  letI := H.finite_classes
  letI : Fintype R.A.V := Fintype.ofFinite _
  obtain ⟨K, hK, hb⟩ := selected_full_sheet_norm_bound R N T P H B hB
  refine ⟨Fintype.card R.A.V * K, mul_nonneg (Nat.cast_nonneg _) hK, ?_⟩
  intro v x
  letI := N.groupHaar_isHaar
  have hs := integrable_finset_sum Finset.univ (fun κ _ =>
    (selected_full_sheet_integrable R N T P H v κ x).norm)
  calc
    _ ≤ ∫ y : Sheet R.A x, ∑ κ : R.A.V, ‖T.sheetIntegrand P v κ y.val‖
        ∂sheetHaar R.A P.v₀ N.groupHaar x := by
      apply integral_mono (unmasked_full_sheet_integrable R N T P H v x).norm hs
      intro y
      dsimp only
      rw [← sheet_class_norm R T P v y.val]
      exact Finset.single_le_sum (fun κ _ => norm_nonneg (T.sheetIntegrand P v κ y.val))
        (Finset.mem_univ _)
    _ = ∑ κ : R.A.V, ∫ y : Sheet R.A x, ‖T.sheetIntegrand P v κ y.val‖
        ∂sheetHaar R.A P.v₀ N.groupHaar x :=
      integral_finset_sum _ (fun κ _ => (selected_full_sheet_integrable R N T P H v κ x).norm)
    _ ≤ ∑ κ : R.A.V, K * min (Real.rpow x.val (1 / 8)) (Real.rpow x.val (-B)) :=
      Finset.sum_le_sum (fun κ _ => hb v κ x)
    _ = _ := by simp [mul_assoc]

end DedekindZetaZeroFree.OrbitFrequencies

end

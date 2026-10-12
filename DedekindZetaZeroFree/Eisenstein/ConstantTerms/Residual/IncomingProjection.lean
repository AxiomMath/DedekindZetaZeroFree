module

public import DedekindZetaZeroFree.Eisenstein.Induction.Cusps.IncomingSheetEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
namespace DedekindZetaZeroFree.FourierContinuation.ResidualIncomingProjection
open KPContFlatCuspIncomingEvaluation
open _root_.DedekindZetaZeroFree.KPContFlatCuspIncomingEvaluation renaming central_comm → central_comm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (a : Cusps F ζ hζ C R P H U)
variable {S : Type*} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContFlatCommonLevelKernel.CommonSphericalStage F ζ hζ U)

private theorem inverse_fix (a z : ℂ) (ha : a ≠ 0) (h : a * z = z) : a⁻¹ * z = z := by
  calc
    a⁻¹ * z = a⁻¹ * (a * z) := congrArg (a⁻¹ * ·) h.symm
    _ = z := by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]

private theorem average_fix {T : Type*} [Fintype T] [Nonempty T]
    (c : T → ℂ) (z : ℂ) (h : ∀ t, c t * z = z) :
    ((Fintype.card T : ℂ)⁻¹ * ∑ t, c t) * z = z := by
  rw [mul_assoc, Finset.sum_mul]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

private theorem sheet_central_level (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (v : S)
    (ε : KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
      (atlasLevel F ζ hζ C R P H U)) :
    (KPCuspGenuineMonodromy.chi F ζ hζ ε.val : ℂ) *
      sheetEvaluation F ζ hζ C R P H U a ι s v 1 =
    sheetEvaluation F ζ hζ C R P H U a ι s v 1 := by
  have hphase := sheetEvaluation_phase F ζ hζ C R P H U a ι s v ε.val 1
  have hf := (KPContFlatCommonLevelKernel.stage_properties F ζ hζ U ι s hs).1 v
    (finiteRepresentative F ζ hζ C R P H U a 1).val
    ⟨(KPCuspGenuineMonodromy.central F ζ hζ ε.val).val,
      atlasLevel_mem_globalLevel F ζ hζ C R P H U
        ⟨KPCuspGenuineMonodromy.central F ζ hζ ε.val, ε.property⟩⟩
  have hc := congrArg (fun x : KPFiniteCuspAtlas.FiniteCover F ζ hζ => x.val)
    (central_comm F ζ hζ ε.val (finiteRepresentative F ζ hζ C R P H U a 1))
  have he : (finiteRepresentative F ζ hζ C R P H U a ε.val).val =
      (finiteRepresentative F ζ hζ C R P H U a 1).val *
        (KPCuspGenuineMonodromy.central F ζ hζ ε.val).val := by
    simp only [finiteRepresentative, map_one, one_mul, Subgroup.coe_mul]
    simpa only [finiteRepresentative, map_one, one_mul, Subgroup.coe_mul, mul_assoc] using hc
  rw [mul_one] at hphase
  rw [← hphase]
  change KPContFlatCommonLevelKernel.L F ζ hζ U ι s v
    (finiteRepresentative F ζ hζ C R P H U a ε.val).val = _
  rw [he]
  exact hf

theorem projected_sheet_evaluation (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (v : S) :
    (zeroProjection F ζ hζ C R P H U a
      (sheetEvaluation F ζ hζ C R P H U a ι s v)).val 0 =
      sheetEvaluation F ζ hζ C R P H U a ι s v 1 := by
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  letI : Finite (TranslationDeck F ζ hζ C R P H U a) :=
    (monodromy F ζ hζ C R P H U a).finite_deck
  letI : Fintype (TranslationDeck F ζ hζ C R P H U a) := Fintype.ofFinite _
  letI : Fintype (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
    (atlasLevel F ζ hζ C R P H U)) := Fintype.ofFinite _
  let z := sheetEvaluation F ζ hζ C R P H U a ι s v 1
  have hsheets : (Fintype.card (rootsOfUnity 3 F) : ℂ)⁻¹ *
      ∑ ε : rootsOfUnity 3 F, (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)⁻¹ *
        sheetEvaluation F ζ hζ C R P H U a ι s v ε = z := by
    have hp (ε : rootsOfUnity 3 F) :
        (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)⁻¹ *
          sheetEvaluation F ζ hζ C R P H U a ι s v ε = z := by
      have he := sheetEvaluation_phase F ζ hζ C R P H U a ι s v ε 1
      rw [mul_one] at he
      rw [he, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
    simp only [hp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
  have hcentral := average_fix
    (fun ε : KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
      (atlasLevel F ζ hζ C R P H U) => (KPCuspGenuineMonodromy.chi F ζ hζ ε.val : ℂ)⁻¹) z
    (fun ε => inverse_fix _ _ (Units.ne_zero _)
      (sheet_central_level F ζ hζ C R P H U a ι s hs v ε))
  have hdeck := average_fix (deckCoefficient F ζ hζ C R P H U a) z (fun q =>
    inverse_fix _ _ (Units.ne_zero _)
      (sheetEvaluation_stabilizer F ζ hζ C R P H U a ι s hs v
        ((parabolic F ζ hζ C R P H U a).inclusion (Multiplicative.ofAdd (Quotient.out q))) 1))
  change projectedScalar F ζ hζ C R P H U a _ = z
  dsimp only [projectedScalar]
  rw [hsheets, mul_assoc, hcentral, hdeck]
end DedekindZetaZeroFree.FourierContinuation.ResidualIncomingProjection

end

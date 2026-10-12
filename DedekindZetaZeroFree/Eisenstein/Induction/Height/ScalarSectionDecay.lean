module

public import DedekindZetaZeroFree.Eisenstein.Induction.Height.TorusRootCoordinates

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField Matrix
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue
open KPLiteralRaw KPChamberHeight
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem actual_root_projection (x : KPAdeles F) :
    KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (KPGlobalTorusFunctionData.N F ζ hζ x) =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
        (Matrix.GeneralLinearGroup.transvection 0 1 (by decide) x) := by
  change QuotientGroup.mk' _
    (KPAdelicCoverRestrictedProduct.projection F ζ hζ (KPRationalAdelicSplitting.N F ζ hζ x)) = _
  congr 1
  have ht (v : KPHilbert.Place F) :
      KPAdelicCoverRestrictedProduct.matrixEval F v
        (Matrix.GeneralLinearGroup.transvection 0 1 (by decide) x) =
      KubotaRankTwo.n (KPHilbert.Completion F v) (KPAdelicCoverRestrictedProduct.adeleEval F v x) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPAdelicCoverRestrictedProduct.matrixEval, Matrix.GeneralLinearGroup.transvection,
        Matrix.transvection, Matrix.single, KubotaRankTwo.n]
  apply Units.ext
  ext i j
  apply Prod.ext
  · funext w
    exact congrArg (fun M : KPLocalCover.LocalGL2 F (Sum.inl w) => M i j)
      ((KPRationalAdelicSplitting.projection_N F ζ hζ x (Sum.inl w)).trans (ht (Sum.inl w)).symm)
  · apply Subtype.ext
    funext q
    exact congrArg (fun M : KPLocalCover.LocalGL2 F (Sum.inr q) => M i j)
      ((KPRationalAdelicSplitting.projection_N F ζ hζ x (Sum.inr q)).trans (ht (Sum.inr q)).symm)

theorem covered_torus_root_upper (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F) :
    ∃ B : KPChamberHeight.AdelGL F, B 1 0 = 0 ∧
      Matrix.ProjGenLinGroup.mk B = coveredHeightProjection F ζ hζ
        (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) := by
  obtain ⟨A, hA, h10, h01⟩ := t.property
  let B := A * Matrix.GeneralLinearGroup.transvection 0 1 (by decide) x
  have hB : B 1 0 = 0 := by
    simp [B, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection, h10]
  refine ⟨B, hB, ?_⟩
  have he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
        (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) := by
    simp only [B, map_mul, actual_root_projection F ζ hζ x, hA]
  change _ = adelicHeightProjection F (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ _)
  rw [← he]
  rfl

theorem actualScalarHeightDecay (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g : G F ζ hζ,
      ‖f.val s g‖ ≤ B * (KPChamberHeight.height F (actualBaseRowLine F)
        (coveredHeightProjection F ζ hζ g)) ^ (-2 * (2 / 3 + s.re)) := by
  obtain ⟨B, hB, hb⟩ := norm_val_iwasawa_bound F ζ hζ K hK f
  obtain ⟨m, M, hm, hmM, hdist⟩ := actualBaseRowHeight_compact_upper_bounds F ζ hζ K hK.1
  have hM : 0 < M := hm.trans_le hmM
  let a : ℝ := 2 / 3 + s.re
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hq : -2 * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by norm_num) ha
  refine ⟨B * (M⁻¹) ^ (-2 * a), mul_nonneg hB (Real.rpow_nonneg (inv_nonneg.mpr hM.le) _), fun g => ?_⟩
  obtain ⟨t, x, k, hg⟩ := hK.2.1 g
  obtain ⟨A, hA, hproj⟩ := covered_torus_root_upper F ζ hζ t x
  have hd := (hdist A k hA).2
  rw [hproj, ← map_mul, ← hg] at hd
  let H := KPChamberHeight.height F (actualBaseRowLine F) (coveredHeightProjection F ζ hζ g)
  let Ht := KPChamberHeight.height F (actualBaseRowLine F)
    (coveredHeightProjection F ζ hζ (t.val * KPGlobalTorusFunctionData.N F ζ hζ x))
  have hH : 0 < H := height_pos F _ _
  have hHt : 0 < Ht := height_pos F _ _
  have hlow : M⁻¹ * H ≤ Ht := by
    have hd' : H ≤ M * Ht := hd
    exact (inv_mul_le_iff₀ hM).mpr hd'
  have hpow : Ht ^ (-2 * a) ≤ (M⁻¹ * H) ^ (-2 * a) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos (inv_pos.mpr hM) hH) hlow hq
  have hdelta : (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) ^ a = Ht ^ (-2 * a) := by
    rw [← actualBaseRowHeight_torus_root_modulus F ζ hζ t x]
    simpa only [Int.cast_neg, Int.cast_ofNat] using (Real.rpow_intCast_mul hHt.le (-2) a).symm
  calc
    ‖f.val s g‖ ≤ B * (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) ^ a := by
      rw [hg]; exact hb s t x k
    _ = B * Ht ^ (-2 * a) := by rw [hdelta]
    _ ≤ B * (M⁻¹ * H) ^ (-2 * a) := mul_le_mul_of_nonneg_left hpow hB
    _ = (B * (M⁻¹) ^ (-2 * a)) * H ^ (-2 * a) := by
      rw [Real.mul_rpow (inv_nonneg.mpr hM.le) hH.le]; ring
end DedekindZetaZeroFree.KPLiteralExceptionalResidue

end

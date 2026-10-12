module

public import DedekindZetaZeroFree.Metaplectic.Torus.RationalQuotientCompactnessAndProfiles

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue
open KPGlobalTorusFunctionData KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem N_eq_pglN (x : KPAdeles F) :
    KPGlobalTorusFunctionData.N F ζ hζ x = KPRationalAdelicSplitting.pglN F ζ hζ x := by
  rfl

private theorem projection_pglA (y : KPGlobalTorusFunctionData.Ideles F) :
    pglProjection F ζ hζ (KPRationalAdelicSplitting.pglA F ζ hζ y) =
      KPGlobalCubicIdelePairing.diagonalPGL F y := by
  change QuotientGroup.mk' (scalarSubgroup F)
    (projection F ζ hζ (KPRationalAdelicSplitting.A F ζ hζ y)) = _
  change QuotientGroup.mk' (scalarSubgroup F) _ = QuotientGroup.mk' (scalarSubgroup F) _
  congr 1
  have hd (v : KPHilbert.Place F) : matrixEval F v (KPGlobalCubicIdelePairing.diagonalHom F y) =
      KubotaRankTwo.d (KPHilbert.Completion F v) (Units.map (adeleEval F v) y) 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixEval, KPGlobalCubicIdelePairing.diagonalHom,
        KPGlobalCubicIdelePairing.diagonalMatrix, KubotaRankTwo.d]
  apply Units.ext
  ext i j
  apply Prod.ext
  · funext w
    have h := (KPRationalAdelicSplitting.projection_A F ζ hζ y (Sum.inl w)).trans (hd (Sum.inl w)).symm
    exact congrArg (fun M : KPLocalCover.LocalGL2 F (Sum.inl w) => M i j) h
  · apply Subtype.ext
    funext q
    have h := (KPRationalAdelicSplitting.projection_A F ζ hζ y (Sum.inr q)).trans (hd (Sum.inr q)).symm
    exact congrArg (fun M : KPLocalCover.LocalGL2 F (Sum.inr q) => M i j) h

private theorem torus_projection_diagonal (t : E F ζ hζ) :
    pglProjection F ζ hζ t.val = KPGlobalCubicIdelePairing.diagonalPGL F (p F ζ hζ t) := by
  obtain ⟨A, hA, h10, h01⟩ := t.property
  have hf : p F ζ hζ t = (diagonal_entries_units F A h10 h01).1.unit *
      ((diagonal_entries_units F A h10 h01).2.unit)⁻¹ := by
    apply Units.ext
    exact ratio_formula F _ A hA h10 h01
  rw [hf, ← hA]
  symm
  apply (QuotientGroup.mk'_eq_mk' _).mpr
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2)
    (diagonal_entries_units F A h10 h01).2.unit, ⟨_, rfl⟩, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KPGlobalCubicIdelePairing.diagonalMatrix,
      KPGlobalCubicIdelePairing.diagonalPGL, KPGlobalCubicIdelePairing.diagonalHom,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar, Matrix.diagonal, h10, h01, IsUnit.unit_spec]
  rw [mul_assoc]
  have hc := (diagonal_entries_units F A h10 h01).2.unit.inv_mul
  rw [IsUnit.unit_spec] at hc
  rw [hc, mul_one]

theorem actual_torus_root_reorder (t : E F ζ hζ) (x : KPAdeles F) :
    ∃ y : KPAdeles F, t.val * KPGlobalTorusFunctionData.N F ζ hζ x =
      KPGlobalTorusFunctionData.N F ζ hζ y * t.val := by
  let a := KPRationalAdelicSplitting.pglA F ζ hζ (p F ζ hζ t)
  have hc : t.val * a⁻¹ ∈ Subgroup.center (G F ζ hζ) := by
    apply pglCentralInjection_central F ζ hζ
    rw [pglCentralInjection_kernel]
    change pglProjection F ζ hζ (t.val * a⁻¹) = 1
    rw [map_mul, map_inv, torus_projection_diagonal F ζ hζ t,
      projection_pglA F ζ hζ]
    exact mul_inv_cancel _
  refine ⟨x * (p F ζ hζ t : KPAdeles F), ?_⟩
  have hn := KPRationalAdelicSplitting.quotient_upper_diagonal F ζ hζ
    (x * (p F ζ hζ t : KPAdeles F)) (p F ζ hζ t)
  have hp : (x * (p F ζ hζ t : KPAdeles F)) * (↑(p F ζ hζ t)⁻¹ : KPAdeles F) = x := by
    rw [mul_assoc]
    have hu : (p F ζ hζ t : KPAdeles F) * (↑(p F ζ hζ t)⁻¹ : KPAdeles F) = 1 :=
      (p F ζ hζ t).mul_inv
    rw [hu, mul_one]
  rw [hp, ← N_eq_pglN, ← N_eq_pglN] at hn
  have hcomm := Subgroup.mem_center_iff.mp hc (KPGlobalTorusFunctionData.N F ζ hζ
    (x * (p F ζ hζ t : KPAdeles F)))
  calc
    t.val * KPGlobalTorusFunctionData.N F ζ hζ x =
      (t.val * a⁻¹) * (a * KPGlobalTorusFunctionData.N F ζ hζ x) := by group
    _ = (t.val * a⁻¹) * (KPGlobalTorusFunctionData.N F ζ hζ
      (x * (p F ζ hζ t : KPAdeles F)) * a) := by rw [← hn]
    _ = KPGlobalTorusFunctionData.N F ζ hζ (x * (p F ζ hζ t : KPAdeles F)) * t.val := by
      rw [← mul_assoc, ← hcomm]
      group

theorem val_torus_root_compact (K : Subgroup (G F ζ hζ))
    (f : KPLiteralRaw.Flat F ζ hζ K) (s : ℂ) (t : E F ζ hζ)
    (x : KPAdeles F) (k : K) :
    f.val s ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val) =
      f.val s (t.val * k.val) := by
  obtain ⟨y, hy⟩ := actual_torus_root_reorder F ζ hζ t x
  rw [hy, mul_assoc, val_N_invariant]

theorem norm_val_iwasawa_bound (K : Subgroup (G F ζ hζ))
    (hK : KPLiteralRaw.IwasawaCompact F ζ hζ K) (f : KPLiteralRaw.Flat F ζ hζ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (s : ℂ) (t : E F ζ hζ) (x : KPAdeles F) (k : K),
      ‖f.val s ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val)‖ ≤
        B * (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) ^
          ((2 : ℝ) / 3 + s.re) := by
  obtain ⟨B, hB, hb⟩ := normalizedTorusProfile_bounded F ζ hζ K hK f
  refine ⟨B, hB, fun s t x k => ?_⟩
  rw [val_torus_root_compact F ζ hζ K f s t x k, norm_val_torus_compact]
  rw [mul_comm B]
  apply mul_le_mul_of_nonneg_left (hb t k)
  exact Real.rpow_nonneg (NNReal.coe_nonneg _) _
end DedekindZetaZeroFree.KPLiteralExceptionalResidue

end

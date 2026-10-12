module

public import DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries

@[expose] public section

noncomputable section
open scoped NumberField Classical Matrix
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
private lemma eval_ext (a b : Adeles F)
    (h : ∀ v, adeleEval F v a = adeleEval F v b) : a = b := by
  apply Prod.ext
  · funext w
    exact h (Sum.inl w)
  · apply Subtype.ext
    funext q
    exact h (Sum.inr q)
private lemma projection_A_entry (y : Ideles F) (i j : Fin 2) :
    (projection F ζ hζ (KPRationalAdelicSplitting.A F ζ hζ y)) i j =
      (!![(y : Adeles F), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (Adeles F)) i j := by
  apply eval_ext F
  intro v
  have h := congrArg (fun M : KPLocalCover.LocalGL2 F v => M i j)
    (KPRationalAdelicSplitting.projection_A F ζ hζ y v)
  fin_cases i <;> fin_cases j <;>
    simpa [matrixEval, Matrix.GeneralLinearGroup.map_apply, KubotaRankTwo.d] using h
private lemma same_torus_projection (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    pglProjection F ζ hζ (KPRationalAdelicSplitting.pglA F ζ hζ
      (KPGlobalTorusFunctionData.p F ζ hζ t)) = pglProjection F ζ hζ t.val := by
  obtain ⟨A, hA, h10, h01⟩ := t.property
  let a := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit
  let d := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit
  let y := KPGlobalTorusFunctionData.p F ζ hζ t
  have hy : y = a * d⁻¹ := by
    apply Units.ext
    exact KPGlobalTorusFunctionData.ratio_formula F
      ⟨pglProjection F ζ hζ t.val, t.property⟩ A hA h10 h01
  have ha : (a : Adeles F) = A 0 0 := by simp [a]
  have hd : (d : Adeles F) = A 1 1 := by simp [d]
  have hm : projection F ζ hζ (KPRationalAdelicSplitting.A F ζ hζ y) *
      Matrix.GeneralLinearGroup.scalar (Fin 2) d = A := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal]
    simp only [projection_A_entry]
    fin_cases i <;> fin_cases j <;> simp [hy, h10, h01, ← hd, ha, mul_assoc]
  change QuotientGroup.mk' (scalarSubgroup F)
      (projection F ζ hζ (KPRationalAdelicSplitting.A F ζ hζ y)) = _
  rw [← hA, ← hm, map_mul]
  have hs : QuotientGroup.mk' (scalarSubgroup F)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) d) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨d, rfl⟩
  rw [hs, mul_one]

theorem coveredTorus_normalizes_upperRoot
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F) :
    t.val * KPGlobalTorusFunctionData.N F ζ hζ x =
      KPGlobalTorusFunctionData.N F ζ hζ
        ((KPGlobalTorusFunctionData.p F ζ hζ t : KPAdeles F) * x) * t.val := by
  let y := KPGlobalTorusFunctionData.p F ζ hζ t
  let a := KPRationalAdelicSplitting.pglA F ζ hζ y
  have hk : t.val * a⁻¹ ∈ (pglProjection F ζ hζ).ker := by
    change pglProjection F ζ hζ (t.val * a⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [same_torus_projection F ζ hζ t, mul_inv_cancel]
  have hc : t.val * a⁻¹ ∈ Subgroup.center (CubicPGL2Adelic F ζ hζ) := by
    apply pglCentralInjection_central F ζ hζ
    rwa [pglCentralInjection_kernel]
  have hn : a * KPGlobalTorusFunctionData.N F ζ hζ x =
      KPGlobalTorusFunctionData.N F ζ hζ ((y : KPAdeles F) * x) * a := by
    have h := KPRationalAdelicSplitting.quotient_upper_diagonal F ζ hζ
      ((y : KPAdeles F) * x) y
    have he : (y : KPAdeles F) * x * (↑y⁻¹ : KPAdeles F) = x := by
      calc
        _ = x * ((y : KPAdeles F) * (↑y⁻¹ : KPAdeles F)) := by ring
        _ = x := by simp
    rw [he] at h
    exact h.symm
  have hcomm := Subgroup.mem_center_iff.mp hc
    (KPGlobalTorusFunctionData.N F ζ hζ ((y : KPAdeles F) * x))
  calc
    t.val * KPGlobalTorusFunctionData.N F ζ hζ x =
        (t.val * a⁻¹) * (a * KPGlobalTorusFunctionData.N F ζ hζ x) := by group
    _ = (t.val * a⁻¹) *
        (KPGlobalTorusFunctionData.N F ζ hζ ((y : KPAdeles F) * x) * a) := by rw [hn]
    _ = KPGlobalTorusFunctionData.N F ζ hζ ((y : KPAdeles F) * x) * t.val := by
      rw [← mul_assoc, ← hcomm]
      group
end DedekindZetaZeroFree.KPLiteralChamber

end

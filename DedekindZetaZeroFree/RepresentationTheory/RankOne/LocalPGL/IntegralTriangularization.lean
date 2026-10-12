module

public import DedekindZetaZeroFree.Metaplectic.Kubota.RankOne.CartanDecomposition
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LocalPGLCoverModules

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ActualFiniteBorel.IwasawaProof
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (q : HeightOneSpectrum (𝓞 F))
local instance : ValuativeRel (q.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F q
local instance : IsNonarchimedeanLocalField (q.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q

local instance : (Valued.v : Valuation (q.adicCompletion F)
    (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _

private theorem mem_integer (x : q.adicCompletion F) :
    x ∈ KPTameCompact.O F q ↔ Valued.v x ≤ 1 := by
  rw [Valuation.mem_integer_iff]
  exact ((ValuativeRel.isEquiv (Valued.v : Valuation (q.adicCompletion F)
    (WithZero (Multiplicative ℤ))) (ValuativeRel.valuation (q.adicCompletion F))).le_iff_le
    (x := x) (y := 1)).symm.trans (by simp)

private theorem triangularize_pivot (g : KPLocalCover.LocalGL2 F (Sum.inr q))
    (h : Valued.v (g 1 0) ≤ Valued.v (g 1 1)) :
    ∃ k : KPTameCompact.K0 F q, (g * KPTameCompact.inclusion F q k) 1 0 = 0 := by
  have hd : g 1 1 ≠ 0 := by
    intro hd
    have hc : g 1 0 = 0 := by
      apply (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ))).map_eq_zero_iff.mp
      exact le_antisymm (by simpa [hd] using h) zero_le
    exact Matrix.GeneralLinearGroup.det_ne_zero g (by simp [Matrix.det_fin_two, hd, hc])
  have ht : Valued.v (-(g 1 0 / g 1 1)) ≤ 1 := by
    rw [Valuation.map_neg, Valuation.map_div, div_le_one₀ (Valued.v.pos_iff.mpr hd)]
    exact h
  let t : KPTameCompact.O F q := ⟨-(g 1 0 / g 1 1), (mem_integer F q _).mpr ht⟩
  refine ⟨KPStandardLocalRootLifts.integralLowerN F q t, ?_⟩
  simp [KPTameCompact.inclusion, KPLocalCube.integerInclusion,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.GeneralLinearGroup.map_apply, KPStandardLocalRootLifts.integralLowerN,
    Matrix.GeneralLinearGroup.val_mk'', t]
  field_simp
  ring

theorem triangularize (g : KPLocalCover.LocalGL2 F (Sum.inr q)) :
    ∃ k : KPTameCompact.K0 F q, (g * KPTameCompact.inclusion F q k) 1 0 = 0 := by
  by_cases h : Valued.v (g 1 0) ≤ Valued.v (g 1 1)
  · exact triangularize_pivot F q g h
  · let W := KPStandardLocalRootLifts.integralW F q
    have entry (i j : Fin 2) : KPTameCompact.inclusion F q W i j =
        (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (q.adicCompletion F)) i j := by
      fin_cases i <;> fin_cases j <;>
        simp [W, KPTameCompact.inclusion, KPLocalCube.integerInclusion,
          Matrix.GeneralLinearGroup.map_apply, KPStandardLocalRootLifts.integralW]
    have hp : Valued.v ((g * KPTameCompact.inclusion F q W) 1 0) ≤
        Valued.v ((g * KPTameCompact.inclusion F q W) 1 1) := by
      simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, entry]
        using (le_of_not_ge h)
    obtain ⟨k, hk⟩ := triangularize_pivot F q (g * KPTameCompact.inclusion F q W) hp
    refine ⟨W * k, ?_⟩
    simpa only [map_mul, mul_assoc] using hk

theorem integral_ratio (b : KPRankOneInduction.upperBorel F q)
    (k : KPTameCompact.K0 F q)
    (hk : Matrix.ProjGenLinGroup.mk (KPTameCompact.inclusion F q k) = b.val) :
    KPLocalPrincipalSeries.localAbs (q.adicCompletion F)
      (KPRankOneInduction.borelRatio F q b) = 1 := by
  obtain ⟨A, hA, hu⟩ := b.property
  obtain ⟨u, he⟩ := (Matrix.ProjGenLinGroup.mk_eq_mk_iff
    (g₁ := KPTameCompact.inclusion F q k) (g₂ := A)).mp (hk.trans hA.symm)
  have hz : (KPTameCompact.inclusion F q k) 1 0 = 0 := by
    have he10 := congrArg (fun M : KPRankOneInduction.GL2 F q => M 1 0) he
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Fin.reduceEq, if_true, if_false, mul_zero, zero_add, add_zero, hu] at he10
    exact (mul_eq_zero.mp he10).resolve_right u.ne_zero
  have hki : k 1 0 = 0 := by
    apply Subtype.ext
    simpa [KPTameCompact.inclusion, KPLocalCube.integerInclusion,
      Matrix.GeneralLinearGroup.map_apply] using hz
  have hdet : IsUnit (k 0 0 * k 1 1) := by
    simpa [Matrix.det_fin_two, hki] using k.det.isUnit
  have hva : ValuativeRel.valuation (q.adicCompletion F) ((k 0 0 : KPTameCompact.O F q) : q.adicCompletion F) = 1 := by
    exact (Valuation.integer.integers _).one_of_isUnit (isUnit_of_mul_isUnit_left hdet)
  have hvd : ValuativeRel.valuation (q.adicCompletion F) ((k 1 1 : KPTameCompact.O F q) : q.adicCompletion F) = 1 := by
    exact (Valuation.integer.integers _).one_of_isUnit (isUnit_of_mul_isUnit_right hdet)
  have hr := KPRankOneInduction.borelRatio_eq F q b (KPTameCompact.inclusion F q k) hk hz
  have hv : ValuativeRel.valuation (q.adicCompletion F)
      (KPRankOneInduction.borelRatio F q b : q.adicCompletion F) = 1 := by
    rw [hr, Valuation.map_div]
    simpa [KPTameCompact.inclusion, KPLocalCube.integerInclusion,
      Matrix.GeneralLinearGroup.map_apply, hva, hvd]
  simp [KPLocalPrincipalSeries.localAbs, hv]

end
end DedekindZetaZeroFree.ActualFiniteBorel.IwasawaProof

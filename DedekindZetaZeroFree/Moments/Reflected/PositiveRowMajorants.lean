module

public import DedekindZetaZeroFree.Moments.Reflected.BetaEulerSeries
public import DedekindZetaZeroFree.Arithmetic.Ideals.Counting.NormSeries

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical

set_option maxHeartbeats 800000

variable {F : Type} [Field F] [NumberField F]

def exteriorNormZeta (cS : Ideal (𝓞 F)) (t : ℝ) : ℝ :=
  ∑' I : ExteriorIdeal cS, (idealNorm I.val).rpow (-t)

def PositiveRowIndex {cS : Ideal (𝓞 F)} (f : ExteriorSquarefreeIdeal cS) :=
  {a : ExteriorIdeal cS // IdealSupportedOn a.val f.val.val} ×
    ExteriorSquarefreeIdeal cS × ExteriorIdeal cS

def positiveRowWeight {cS : Ideal (𝓞 F)} (f : ExteriorSquarefreeIdeal cS)
    (σ : ℝ) (x : PositiveRowIndex f) : ℝ :=
  betaIdeal f x.1.val.val * (rowNorm x.1.val x.2.1.val x.2.2).rpow (-σ) /
    (Real.sqrt (idealNorm x.2.1.val.val) * idealNorm x.2.2.val)

private theorem exterior_norm_summable (cS : Ideal (𝓞 F)) (t : ℝ) (ht : 1 < t) :
    Summable (fun I : ExteriorIdeal cS => (idealNorm I.val).rpow (-t)) := by
  let e : ExteriorIdeal cS → NonzeroIdeal F := fun I => ⟨I.val, I.property.1⟩
  have he : Function.Injective e := by
    intro I J h
    apply Subtype.ext
    exact congrArg (fun I : NonzeroIdeal F => I.val) h
  have H := (ideal_norm_rpow_summable F t ht).comp_injective he
  exact H

private theorem real_weight_factor (a c n b σ : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hn : 0 < n) :
    b * (a * c * n ^ 3).rpow (-σ) / (Real.sqrt c * n) =
      (b * a.rpow (-σ)) * (c.rpow (-(σ + 1 / 2)) * n.rpow (-(3 * σ + 1))) := by
  change b * (a * c * n ^ (3 : ℕ)) ^ (-σ) / (Real.sqrt c * n) =
    (b * a ^ (-σ)) * (c ^ (-(σ + 1 / 2)) * n ^ (-(3 * σ + 1)))
  have ec : -(σ + 1 / 2) = -σ - 1 / 2 := by ring
  have en : -(3 * σ + 1) = 3 * (-σ) - 1 := by ring
  rw [Real.mul_rpow (mul_nonneg ha.le hc.le) (pow_nonneg hn.le _),
    Real.mul_rpow ha.le hc.le, ← Real.rpow_natCast_mul hn.le,
    ec, en, Real.rpow_sub hc, Real.rpow_sub hn,
    Real.rpow_one, ← Real.sqrt_eq_rpow]
  norm_num
  ring

private theorem positiveRowWeight_factor {cS : Ideal (𝓞 F)}
    (f : ExteriorSquarefreeIdeal cS) (σ : ℝ) (x : PositiveRowIndex f) :
    positiveRowWeight f σ x = betaIdealTerm f σ x.1 *
      ((idealNorm x.2.1.val.val).rpow (-(σ + 1 / 2)) *
       (idealNorm x.2.2.val).rpow (-(3 * σ + 1))) := by
  have ha : 0 < idealNorm x.1.val.val := lt_of_lt_of_le zero_lt_one
    (idealNorm_ge_one _ x.1.val.property.1)
  have hc : 0 < idealNorm x.2.1.val.val := lt_of_lt_of_le zero_lt_one
    (idealNorm_ge_one _ x.2.1.val.property.1)
  have hn : 0 < idealNorm x.2.2.val := lt_of_lt_of_le zero_lt_one
    (idealNorm_ge_one _ x.2.2.property.1)
  exact real_weight_factor _ _ _ _ σ ha hc hn

theorem positiveRowWeight_summable_le {cS : Ideal (𝓞 F)}
    (f : ExteriorSquarefreeIdeal cS) (σ : ℝ) (hσ : 1 / 2 < σ) :
    Summable (positiveRowWeight f σ) ∧
      (∑' x : PositiveRowIndex f, positiveRowWeight f σ x) ≤
        eulerIdeal f σ * exteriorNormZeta cS (σ + 1 / 2) *
          exteriorNormZeta cS (3 * σ + 1) := by
  have hs : 0 ≤ σ := by linarith
  let C : ExteriorIdeal cS → ℝ := fun c => (idealNorm c.val).rpow (-(σ + 1 / 2))
  let N : ExteriorIdeal cS → ℝ := fun n => (idealNorm n.val).rpow (-(3 * σ + 1))
  have hC : Summable C := exterior_norm_summable cS _ (by linarith)
  have hN : Summable N := exterior_norm_summable cS _ (by linarith)
  have hCs : Summable (fun c : ExteriorSquarefreeIdeal cS => C c.val) :=
    hC.subtype (fun c => Squarefree c.val)
  have hCN : Summable (fun p : ExteriorSquarefreeIdeal cS × ExteriorIdeal cS =>
      C p.1.val * N p.2) := summable_mul_of_summable_norm hCs.norm hN.norm
  have hA := betaIdealTerm_summable f σ hs
  have hprod : Summable (fun x : PositiveRowIndex f =>
      betaIdealTerm f σ x.1 * (C x.2.1.val * N x.2.2)) :=
    summable_mul_of_summable_norm hA.norm hCN.norm
  have hW : Summable (positiveRowWeight f σ) :=
    hprod.congr (fun x => (positiveRowWeight_factor f σ x).symm)
  refine ⟨hW, ?_⟩
  have hcol : (∑' c : ExteriorSquarefreeIdeal cS, C c.val) ≤ exteriorNormZeta cS (σ + 1 / 2) := by
    exact Summable.tsum_subtype_le C {c | Squarefree c.val}
      (fun c => Real.rpow_nonneg (le_trans zero_le_one (idealNorm_ge_one _ c.property.1)) _)
      hC
  have heuler : 0 ≤ eulerIdeal f σ := by
    rw [← betaIdealTerm_tsum f σ hs]
    exact tsum_nonneg (betaIdealTerm_nonneg f σ hs)
  have hn : 0 ≤ exteriorNormZeta cS (3 * σ + 1) :=
    tsum_nonneg (fun n => Real.rpow_nonneg
      (le_trans zero_le_one (idealNorm_ge_one _ n.property.1)) _)
  have heq : (∑' x : PositiveRowIndex f, positiveRowWeight f σ x) =
      eulerIdeal f σ * (∑' c : ExteriorSquarefreeIdeal cS, C c.val) *
        exteriorNormZeta cS (3 * σ + 1) := by
    calc
      _ = ∑' x : PositiveRowIndex f, betaIdealTerm f σ x.1 * (C x.2.1.val * N x.2.2) :=
        tsum_congr (positiveRowWeight_factor f σ)
      _ = (∑' a, betaIdealTerm f σ a) *
          (∑' p : ExteriorSquarefreeIdeal cS × ExteriorIdeal cS, C p.1.val * N p.2) :=
        (hA.tsum_mul_tsum hCN hprod).symm
      _ = eulerIdeal f σ *
          ((∑' c : ExteriorSquarefreeIdeal cS, C c.val) * ∑' n, N n) := by
        rw [betaIdealTerm_tsum f σ hs, ← hCs.tsum_mul_tsum hN hCN]
      _ = _ := (mul_assoc _ _ _).symm
  rw [heq]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcol heuler) hn

end
end DedekindZetaZeroFree

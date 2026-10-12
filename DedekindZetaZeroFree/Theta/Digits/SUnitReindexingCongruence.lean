module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.ReciprocityAndGenuineCharacterConventions
public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData
public import DedekindZetaZeroFree.Theta.Digits.NormLevelQuotientDescent

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaForwardQuotientMeasurability.MatrixConstruction
open NumberField IsDedekindDomain
open scoped Classical

namespace ArithmeticCongruence
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (p : KPFinitePlace F) (hp : p ∉ A.Sf)
local instance : ValuativeRel (p.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F p
local instance : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
 lemma vmap (x : F) : Valued.v (algebraMap F (p.adicCompletion F) x) = p.valuation F x := by
  exact p.valuedAdicCompletion_eq_valuation' x
 lemma memO (x : p.adicCompletion F) : x ∈ KPTameCompact.O F p ↔ Valued.v x ≤ 1 := by
  change ValuativeRel.valuation (p.adicCompletion F) x ≤ 1 ↔ _
  exact (ValuativeRel.isEquiv _ _).le_one_iff_le_one
def loc : A.R →+* KPTameCompact.O F p :=
  ((algebraMap F (p.adicCompletion F)).comp A.R.val).codRestrict _ (fun x =>
    (memO p _).mpr (by rw [RingHom.comp_apply, vmap]; exact x.property p hp))
lemma loc_val (x : A.R) : ((loc A p hp x : KPTameCompact.O F p) : p.adicCompletion F) =
    algebraMap F (p.adicCompletion F) (x : F) := rfl
lemma loc_int (x : 𝓞 F) : ((loc A p hp (algebraMap (𝓞 F) A.R x) : KPTameCompact.O F p) : p.adicCompletion F) =
    algebraMap (𝓞 F) (p.adicCompletion F) x := by
  change algebraMap F _ (algebraMap (𝓞 F) F x) = _
  exact (IsScalarTower.algebraMap_apply _ _ _ x).symm
private lemma loc_prime (x : 𝓞 F) (hx : x ∈ p.asIdeal) :
    loc A p hp (algebraMap (𝓞 F) A.R x) ∈ KPTameCompact.p F p := by
  rw [KPTameCompact.p, KPLocalCube.maximalIdeal, IsLocalRing.mem_maximalIdeal]
  change ¬ IsUnit _
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  apply (ValuativeRel.isEquiv (ValuativeRel.valuation (p.adicCompletion F))
    (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one.mpr
  rw [loc_int, IsScalarTower.algebraMap_apply (𝓞 F) F (p.adicCompletion F), vmap]
  exact (p.valuation_lt_one_iff_mem (K := F) x).mpr hx
lemma loc_ideal (x : A.R) (hx : x ∈ Ideal.map (algebraMap (𝓞 F) A.R) p.asIdeal) :
    loc A p hp x ∈ KPTameCompact.p F p := by
  have hle : Ideal.map (algebraMap (𝓞 F) A.R) p.asIdeal ≤ Ideal.comap (loc A p hp) (KPTameCompact.p F p) := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun x hx => loc_prime A p hp x hx
  exact hle hx

lemma digit_diff (u : A.U) (P : Finset (KPFinitePlace F)) (hP : ∀ q ∈ P, q ∉ A.Sf)
    (v : ThetaDigitAverage.Dig P) (q : P) :
    let L := ThetaDigitAverage.residueLifts P
    let v' := ThetaDigitDescent.reindex A P hP u v
    algebraMap (𝓞 F) A.R (L.lift q (v' q)) -
      (A.unitEquiv u : A.R) ^ 6 * algebraMap (𝓞 F) A.R (L.lift q (v q)) ∈
        Ideal.map (algebraMap (𝓞 F) A.R) q.val.asIdeal := by
  dsimp only
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, map_mul, map_pow]
  have he := Classical.choose_spec (ThetaDigitAverage.residue_SInteger_comparison A q.val (hP _ q.property))
  change ∀ r, ThetaDigitDescent.residueComparison A q.val (hP _ q.property)
    (Ideal.Quotient.mk q.val.asIdeal r) = Ideal.Quotient.mk _ (algebraMap (𝓞 F) A.R r) at he
  rw [← he, ← he, (ThetaDigitAverage.residueLifts P).residue_lift,
    (ThetaDigitAverage.residueLifts P).residue_lift]
  change ThetaDigitDescent.residueComparison A q.val (hP _ q.property)
    (↑(ThetaDigitDescent.residueSixthUnit A q.val (hP _ q.property) u) * v q) - _ = 0
  rw [map_mul]
  simp [ThetaDigitDescent.residueSixthUnit]

end ArithmeticCongruence

end DedekindZetaZeroFree.ThetaForwardQuotientMeasurability.MatrixConstruction

end

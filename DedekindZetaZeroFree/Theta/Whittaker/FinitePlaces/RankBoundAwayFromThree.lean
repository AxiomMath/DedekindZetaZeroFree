module

public import DedekindZetaZeroFree.Theta.Whittaker.TameFinite.RankOneSlices

@[expose] public section

noncomputable section
open scoped NumberField Classical Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FourierContinuation

theorem three_unit_of_not_mem (F : Type) [Field F] [NumberField F]
    (q : KPFinitePlace F) (hq : (3 : 𝓞 F) ∉ q.asIdeal) :
    IsUnit (3 : (valuation (q.adicCompletion F)).integer) := by
  have hv : valuation (q.adicCompletion F) (3 : q.adicCompletion F) = 1 := by
    letI : (Valued.v : Valuation (q.adicCompletion F)
        (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
    rw [← (ValuativeRel.isEquiv (Valued.v : Valuation (q.adicCompletion F)
      (WithZero (Multiplicative ℤ))) (valuation (q.adicCompletion F))).eq_one_iff_eq_one]
    have he := q.valuedAdicCompletion_eq_valuation (K := F) (3 : 𝓞 F)
    have hn := (q.valuation_eq_one_iff_notMem (K := F) (r := (3 : 𝓞 F))).mpr hq
    simpa only [map_ofNat] using he.trans hn
  apply (Valuation.integer.integers (valuation (q.adicCompletion F))).isUnit_iff_valuation_eq_one.mpr
  simpa only [map_ofNat] using hv

theorem three_not_mem_maximalIdeal_of_not_mem (F : Type) [Field F] [NumberField F]
    (q : KPFinitePlace F) (hq : (3 : 𝓞 F) ∉ q.asIdeal) :
    (3 : (valuation (q.adicCompletion F)).integer) ∉
      IsLocalRing.maximalIdeal (valuation (q.adicCompletion F)).integer := by
  have hu := three_unit_of_not_mem F q hq
  simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hu

namespace TensorActions
open MomentSources
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

theorem finite_slice_rank_le_one_of_three_not_mem (D : TensorActions R N)
    (q : KPFinitePlace F) (hq : (3 : 𝓞 F) ∉ q.asIdeal) :
    Module.rank ℂ (D.toTensorHC.sliceLine (Sum.inr q)) ≤ 1 :=
  D.finite_slice_rank_le_one_tame q (three_not_mem_maximalIdeal_of_not_mem F q hq)
end TensorActions
end DedekindZetaZeroFree.FourierContinuation

end

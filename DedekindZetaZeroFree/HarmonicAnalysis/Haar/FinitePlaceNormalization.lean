module

public import DedekindZetaZeroFree.Theta.Periods.FiniteHaarTransport

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.CurrentFiniteHaarBinding
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
set_option backward.isDefEq.respectTransparency false

theorem integerVolume_eq (q : KPFinitePlace F) :
    PoissonS.integerVolume F q = localHalfDifferentFactor F q := by
  rw [PoissonS.integerVolume,
    FiniteOscillatoryStabilization.globalDifferentExponent_eq_localDifferentExponent F q,
    zpow_natCast, localHalfDifferentFactor_eq_inv_sqrt F q,
    localDifferentNorm, Nat.cast_pow, one_div]

theorem finiteHaar_eq (N : MomentSources.TraceHaarTransport R) (q : KPFinitePlace F) :
    N.finiteHaar q = localNormalizedHaar F q := by
  letI := N.finiteHaar_add q
  let K := finiteCompletionIntegersPositiveCompacts F q
  have h := Measure.addHaarMeasure_unique (N.finiteHaar q) K
  have hO : (K : Set (q.adicCompletion F)) = {x | ‖x‖ ≤ (1 : ℝ)} := by
    rw [coe_finiteCompletionIntegersPositiveCompacts]
    ext x
    exact ⟨norm_le_one_of_mem_adicCompletionIntegers q,
      mem_adicCompletionIntegers_of_norm_le_one q⟩
  rw [hO, N.finite_mass q, integerVolume_eq] at h
  exact h

end DedekindZetaZeroFree.FourierContinuation.CurrentFiniteHaarBinding

end

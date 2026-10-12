module

public import DedekindZetaZeroFree.Theta.Digits.FiniteCharacterMasks
public import DedekindZetaZeroFree.Arithmetic.LocalFields.SignedTraceUniformizer
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.CodifferentTraceDuality

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources NumberField IsDedekindDomain
open scoped Classical BigOperators
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem rational_mul_local (p : KPFinitePlace F) (a : F) (x : p.adicCompletion F) :
    algebraMap F (KPAdeles F) a * KPRationalAdelicSplitting.localAdele F (Sum.inr p) x =
      KPRationalAdelicSplitting.localAdele F (Sum.inr p)
        (algebraMap F (p.adicCompletion F) a * x) := by
  apply Prod.ext
  · change (algebraMap F (KPAdeles F) a).1 * 0 = 0
    exact mul_zero _
  · apply Subtype.ext
    funext q
    change (algebraMap F (q.adicCompletion F) a) *
      (RestrictedProduct.single (fun q : KPFinitePlace F => q.adicCompletionIntegers F) p x) q =
      (RestrictedProduct.single (fun q : KPFinitePlace F => q.adicCompletionIntegers F) p
        (algebraMap F (p.adicCompletion F) a * x)) q
    by_cases h : q = p
    · subst q
      simp
    · simp [RestrictedProduct.single_eq_of_ne _ _ h]

theorem trace_local (p : KPFinitePlace F) (x : p.adicCompletion F) :
    adelicTraceCharacter F (KPRationalAdelicSplitting.localAdele F (Sum.inr p) x) =
      ResidueTrace.localTraceCharacter p x := by
  rw [KPRationalAdelicSplitting.localAdele, adelicTraceCharacter_finite_single,
    ← CodifferentResidueSieve.localTraceCharacter_eq_localFiniteCharacter]

theorem digitParameter_phase (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) (a : F) :
    (adelicTraceCharacter F (algebraMap F (KPAdeles F) a * digitParameter R m d) : ℂ) =
      ∏ p : ThetaDigitAverage.rowPrimes R.A m.val m.property,
        (ResidueTrace.localTraceCharacter p.val
          (algebraMap F (p.val.adicCompletion F) a *
            (-algebraMap (𝓞 F) (p.val.adicCompletion F)
              ((ThetaDigitAverage.residueLifts (ThetaDigitAverage.rowPrimes R.A m.val m.property)).lift p (d p)) /
              algebraMap F (p.val.adicCompletion F)
                (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A ⟨p.val,
                  ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1⟩) : F))) : ℂ) := by
  have hsum {ι : Type} (s : Finset ι) (f : ι → KPAdeles F) :
      adelicTraceCharacter F (∑ i ∈ s, f i) = ∏ i ∈ s, adelicTraceCharacter F (f i) := by
    induction s using Finset.induction_on with
    | empty => simp [AddChar.map_zero_eq_one]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]
  simp only [digitParameter, Finset.mul_sum, rational_mul_local]
  rw [hsum Finset.univ]
  simp only [trace_local]
  exact map_prod (Circle.coeHom : Circle →* ℂ) _ _

end DedekindZetaZeroFree.DigitMasks

end

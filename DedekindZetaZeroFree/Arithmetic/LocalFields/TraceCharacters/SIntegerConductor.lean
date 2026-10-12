module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.LocalSeriesDefinitions

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.CompatiblePrimeRawLocal
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem exterior_notMem (p : ExteriorPrime A) : p.val ∉ A.Sf := by
  intro hp
  have h := (A.exterior_iff ⟨p.val.asIdeal, p.val.ne_bot⟩).mp p.property p.val hp
  rw [sup_idem] at h
  exact p.val.isPrime.ne_top h

theorem sInteger_local_integral_source (p : ExteriorPrime A) (x : A.R) :
    algebraMap F (LocalField p) (x : F) ∈ p.val.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact Set.integer_valuation_le_one _ _ x (exterior_notMem p)

theorem negativeTrace_integer_source (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (x : LocalIntegers p) :
    negativeTrace p (x : LocalField p) = 1 := by
  have hx := (hS p.val (exterior_notMem p) (x : LocalField p)).2 x.property
  have htrace : ResidueTrace.localTraceCharacter p.val (x : LocalField p) = 1 := by
    simpa using hx (1 : LocalIntegers p)
  simp only [negativeTrace, AddChar.neg_apply', htrace, inv_one]

end DedekindZetaZeroFree.CompatiblePrimeRawLocal

end

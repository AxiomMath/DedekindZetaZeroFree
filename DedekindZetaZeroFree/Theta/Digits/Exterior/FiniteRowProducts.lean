module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.LocalSignedAverages

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open MomentSources NumberField IsDedekindDomain ThetaExpansion
open scoped NumberField Classical
open _root_.DedekindZetaZeroFree.ThetaBranch renaming finite_split → finite_split
open _root_.DedekindZetaZeroFree.ThetaBranch renaming exteriorLocalFactor_finite → exteriorLocalFactor_finite
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem row_support (m : ThetaReflectionData.Row R.A)
    (D : ThetaBranch.RowFactorization R.A R.probe.allowed m) :
    ThetaDigitAverage.rowPrimes R.A m.val m.property = ThetaBranch.support D.rowIdeal.val := by
  ext p
  have hs : p ∈ ThetaBranch.support D.rowIdeal.val ↔
      idealPrimeExponent p.asIdeal D.rowIdeal.val ≠ 0 := by
    simp only [ThetaBranch.support, Finset.mem_preimage, idealPrimeSupport,
      idealPrimeExponent, Multiset.mem_toFinset, Multiset.count_ne_zero]
  rw [hs]
  by_cases hp : p ∈ R.A.Sf
  · have hz : idealPrimeExponent p.asIdeal D.rowIdeal.val = 0 := by
      by_contra hn
      exact ThetaBranch.support_outside R.A D.rowIdeal p (hs.mpr hn) hp
    simp [ThetaDigitAverage.rowPrimes, ThetaDigitAverage.RowPrimes, hp, hz]
  · simp only [ThetaDigitAverage.rowPrimes, Set.Finite.mem_toFinset,
      ThetaDigitAverage.RowPrimes, Set.mem_setOf_eq, hp, not_false_eq_true, true_and]
    rw [SIntegerLocalization.generator_valuation R.A.Sf D.rowIdeal.val
      D.rowIdeal.property.1 m.val D.row_generates.1 D.row_generates.2 p hp,
      ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega

def rowEmbedding (m : ThetaReflectionData.Row R.A) : RowPrime R m ↪ ThetaBranch.ExteriorPrime R.A where
  toFun := exteriorRowPrime R m
  inj' := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun z : ThetaBranch.ExteriorPrime R.A => z.val) h

def exteriorRows (m : ThetaReflectionData.Row R.A) : Finset (ThetaBranch.ExteriorPrime R.A) :=
  Finset.univ.map (rowEmbedding R m)

theorem mem_exteriorRows (m : ThetaReflectionData.Row R.A) (p : ThetaBranch.ExteriorPrime R.A) :
    p ∈ exteriorRows R m ↔ p.val ∈ ThetaDigitAverage.rowPrimes R.A m.val m.property := by
  simp only [exteriorRows, Finset.mem_map, Finset.mem_univ, true_and, rowEmbedding]
  constructor
  · rintro ⟨q, rfl⟩
    exact q.property
  · intro hp
    exact ⟨⟨p.val,hp⟩, Subtype.ext rfl⟩

theorem prod_exteriorRows {M : Type*} [CommMonoid M] (m : ThetaReflectionData.Row R.A)
    (f : ThetaBranch.ExteriorPrime R.A → M) :
    (∏ p ∈ exteriorRows R m, f p) = ∏ p : RowPrime R m, f (exteriorRowPrime R m p) := by
  rw [exteriorRows, Finset.prod_map]
  rfl

theorem split_product {P : Type*} [DecidableEq P] (s : Finset P) (f : P → ℂ)
    (hf : Function.HasFiniteMulSupport f) :
    (∏ᶠ p, f p) = (∏ p ∈ s, f p) * ∏ᶠ p, if p ∈ s then 1 else f p :=
  finite_split s f hf

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end

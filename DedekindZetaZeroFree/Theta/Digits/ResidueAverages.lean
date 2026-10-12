module

public import DedekindZetaZeroFree.CharacterSums.Gauss.SexticFourierMasks
public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData
public import DedekindZetaZeroFree.Arithmetic.LocalFields.PlacesAndCompletions

@[expose] public section

namespace DedekindZetaZeroFree
namespace ThetaDigitAverage

noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical

variable {F : Type} [Field F] [NumberField F]

def RowPrimes (A : SArithmeticData F) (m : A.R) : Set (KPFinitePlace F) :=
  {p | p ∉ A.Sf ∧ p.valuation F (m : F) < 1}

theorem rowPrimes_finite (A : SArithmeticData F) (m : A.R) (hm : m ≠ 0) :
    (RowPrimes A m).Finite := by
  have hmF : (m : F) ≠ 0 := by
    intro h
    apply hm
    exact Subtype.ext h

  refine (HeightOneSpectrum.Support.finite (𝓞 F) ((m : F)⁻¹)).subset ?_
  intro p hp
  change 1 < p.valuation F ((m : F)⁻¹)
  rw [map_inv₀]
  exact (one_lt_inv₀ ((p.valuation F).pos_iff.mpr hmF)).2 hp.2

def rowPrimes (A : SArithmeticData F) (m : A.R) (hm : m ≠ 0) :
    Finset (KPFinitePlace F) := (rowPrimes_finite A m hm).toFinset

def rowExponent (A : SArithmeticData F) (m : A.R) (p : KPFinitePlace F) : Fin 6 :=
  ⟨Int.toNat (-WithZero.log (p.valuation F (m : F))) % 6, Nat.mod_lt _ (by decide)⟩

abbrev Residue (p : KPFinitePlace F) := (𝓞 F) ⧸ p.asIdeal

instance residueField (p : KPFinitePlace F) : Field (Residue p) := by
  letI : p.asIdeal.IsMaximal := p.isMaximal
  exact Ideal.Quotient.field p.asIdeal

instance residueFintype (p : KPFinitePlace F) : Fintype (Residue p) := Fintype.ofFinite _

abbrev Dig (P : Finset (KPFinitePlace F)) := (p : P) → Residue p.val

theorem residue_SInteger_comparison (A : SArithmeticData F)
    (p : KPFinitePlace F) (hp : p ∉ A.Sf) :
    ∃ e : Residue p ≃+* (A.R ⧸ Ideal.map (algebraMap (𝓞 F) A.R) p.asIdeal),
      ∀ r : 𝓞 F, e (Ideal.Quotient.mk p.asIdeal r) =
        Ideal.Quotient.mk _ (algebraMap (𝓞 F) A.R r) := by
  letI := SIntegerLocalization.isLocalization_away A.Sf
  let M := Submonoid.powers (SIntegerLocalization.denominator A.Sf)

  have hM : Algebra.algebraMapSubmonoid (Residue p) M ≤
      IsUnit.submonoid (Residue p) := by
    rintro x ⟨r, hr, rfl⟩
    obtain ⟨n, rfl⟩ := hr
    change IsUnit (Ideal.Quotient.mk p.asIdeal
      (SIntegerLocalization.denominator A.Sf ^ n))
    rw [map_pow]
    apply IsUnit.pow
    apply isUnit_iff_ne_zero.mpr
    intro h
    exact hp ((SIntegerLocalization.denominator_mem_iff A.Sf p).mp
      (Ideal.Quotient.eq_zero_iff_mem.mp h))

  let e := (IsLocalization.atUnits (Residue p)
    (Algebra.algebraMapSubmonoid (Residue p) M)
    (S := A.R ⧸ Ideal.map (algebraMap (𝓞 F) A.R) p.asIdeal) hM).toRingEquiv
  exact ⟨e, fun r => rfl⟩

structure ResidueLifts (P : Finset (KPFinitePlace F)) where
  lift : ∀ p : P, Residue p.val → 𝓞 F
  residue_lift : ∀ p v, Ideal.Quotient.mk p.val.asIdeal (lift p v) = v

theorem residueLifts_nonempty (P : Finset (KPFinitePlace F)) :
    Nonempty (ResidueLifts P) := by
  classical
  exact ⟨⟨fun p => Function.surjInv Ideal.Quotient.mk_surjective,
    fun p => Function.surjInv_eq Ideal.Quotient.mk_surjective⟩⟩

def residueLifts (P : Finset (KPFinitePlace F)) : ResidueLifts P :=
  Classical.choice (residueLifts_nonempty P)

end
end ThetaDigitAverage
end DedekindZetaZeroFree

module

public import Mathlib

@[expose] public section

open scoped NumberField Classical ValuativeRel
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PalomarHilbert

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]

abbrev FinitePlace := HeightOneSpectrum (𝓞 F)

abbrev Family := ∀ v : FinitePlace F,
  (v.adicCompletion F)ˣ → (v.adicCompletion F)ˣ → rootsOfUnity 6 F

abbrev adicValuation (v : FinitePlace F) :
    Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v

abbrev completionRelation (v : FinitePlace F) : ValuativeRel (v.adicCompletion F) :=
  ValuativeRel.ofValuation (adicValuation F v)

local instance (v : FinitePlace F) : ValuativeRel (v.adicCompletion F) :=
  completionRelation F v

abbrev LocalIntegers (v : FinitePlace F) :=
  (ValuativeRel.valuation (v.adicCompletion F)).integer

abbrev Residue (v : FinitePlace F) := IsLocalRing.ResidueField (LocalIntegers F v)

def integerUnitInclusion (v : FinitePlace F) :
    (LocalIntegers F v)ˣ →* (v.adicCompletion F)ˣ :=
  Units.map (ValuativeRel.valuation (v.adicCompletion F)).integer.subtype.toMonoidHom

def diagonal (v : FinitePlace F) : Fˣ →* (v.adicCompletion F)ˣ :=
  Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom

def OrdinaryUniformizer (v : FinitePlace F) (π : (v.adicCompletion F)ˣ) : Prop :=
  adicValuation F v (π : v.adicCompletion F) =
    ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))

structure IsSexticHilbertFamily (H : Family F) : Prop where
  continuous : ∀ v : FinitePlace F,
    letI : TopologicalSpace (rootsOfUnity 6 F) := ⊥
    Continuous (fun ab : (v.adicCompletion F)ˣ × (v.adicCompletion F)ˣ =>
      H v ab.1 ab.2)
  mul_left : ∀ (v : FinitePlace F) (a b c : (v.adicCompletion F)ˣ),
    H v (a * b) c = H v a c * H v b c
  mul_right : ∀ (v : FinitePlace F) (a b c : (v.adicCompletion F)ˣ),
    H v a (b * c) = H v a b * H v a c
  alternating : ∀ (v : FinitePlace F) (a : (v.adicCompletion F)ˣ), H v a a = 1
  productFormula : ∀ a b : Fˣ,
    Function.HasFiniteMulSupport (fun v => H v (diagonal F v a) (diagonal F v b)) ∧
    (∏ᶠ v, H v (diagonal F v a) (diagonal F v b)) = 1
  tame : ∀ v : FinitePlace F, (6 : 𝓞 F) ∉ v.asIdeal →
    (∀ u u' : (LocalIntegers F v)ˣ,
      H v (integerUnitInclusion F v u) (integerUnitInclusion F v u') = 1) ∧
    ∀ π : (v.adicCompletion F)ˣ, OrdinaryUniformizer F v π →
    ∀ u : (LocalIntegers F v)ˣ, ∃ r : LocalIntegers F v,
      (r : v.adicCompletion F) = algebraMap F (v.adicCompletion F)
        ((H v π (integerUnitInclusion F v u) : Fˣ) : F) ∧
      IsLocalRing.residue (LocalIntegers F v) r =
        IsLocalRing.residue (LocalIntegers F v) (u : LocalIntegers F v) ^
          ((Nat.card (Residue F v) - 1) / 6)

end
end DedekindZetaZeroFree.PalomarHilbert

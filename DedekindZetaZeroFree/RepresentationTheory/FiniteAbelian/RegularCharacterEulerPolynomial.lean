module

public import DedekindZetaZeroFree.RepresentationTheory.FiniteAbelian.CharacterEvaluationFibers
public import DedekindZetaZeroFree.Algebra.RootsOfUnityEulerPolynomial

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped BigOperators

theorem regularCharacterDeterminant
    {G : Type*} [CommGroup G] [Finite G] (g : G) (x : ℂ) :
    ∏ ρ : ComplexDual G, (1 - (ρ g : ℂ) * x) =
      (1 - x ^ orderOf g) ^ (Nat.card G / orderOf g) := by
  classical
  have hf := dualEvaluation_orderOf_pos g
  letI : NeZero (orderOf g) := ⟨Nat.ne_of_gt hf⟩
  letI : Fintype (rootsOfUnity (orderOf g) ℂ) := Fintype.ofFinite _
  let e : ComplexDual G → rootsOfUnity (orderOf g) ℂ := fun ρ =>
    ⟨ρ g, (mem_rootsOfUnity _ _).mpr (dualEvaluation_pow_orderOf g ρ)⟩
  have hcard (ζ : rootsOfUnity (orderOf g) ℂ) :
      Fintype.card {ρ : ComplexDual G // e ρ = ζ} = Nat.card G / orderOf g := by
    rw [← Nat.card_eq_fintype_card]
    have he : {ρ : ComplexDual G // e ρ = ζ} ≃ {ρ : ComplexDual G // ρ g = ζ.val} :=
      Equiv.subtypeEquivRight (fun ρ => by simp [e, Subtype.ext_iff])
    rw [Nat.card_congr he]
    exact dualEvaluationFibers g ζ.val ((mem_rootsOfUnity _ _).mp ζ.property)
  calc
    ∏ ρ : ComplexDual G, (1 - (ρ g : ℂ) * x) =
        ∏ ζ : rootsOfUnity (orderOf g) ℂ, ∏ _ρ : {ρ : ComplexDual G // e ρ = ζ},
          (1 - (ζ.val : ℂ) * x) :=
      (Fintype.prod_fiberwise' e (fun ζ => 1 - (ζ.val : ℂ) * x)).symm
    _ = ∏ ζ : rootsOfUnity (orderOf g) ℂ,
          (1 - (ζ.val : ℂ) * x) ^ (Nat.card G / orderOf g) := by
      apply Finset.prod_congr rfl
      intro ζ _
      simp only [Finset.prod_const, Finset.card_univ, hcard]
    _ = (∏ ζ : rootsOfUnity (orderOf g) ℂ, (1 - (ζ.val : ℂ) * x)) ^
          (Nat.card G / orderOf g) := Finset.prod_pow _ _ _
    _ = (1 - x ^ orderOf g) ^ (Nat.card G / orderOf g) := by
      rw [rootsEulerPolynomial (orderOf g) hf x]

end DedekindZetaZeroFree.AbelianQuotient

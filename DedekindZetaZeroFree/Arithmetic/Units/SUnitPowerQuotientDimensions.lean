module

public import DedekindZetaZeroFree.Arithmetic.Units.SUnitPowerQuotientCoordinates

@[expose] public section

namespace DedekindZetaZeroFree.SArithmeticData

noncomputable section

variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)

include A in

theorem finrank_torsionPowerQuotient (ℓ : ℕ) (hℓ : ℓ = 2 ∨ ℓ = 3)
    [Fact (Nat.Prime ℓ)] :
    Module.finrank (ZMod ℓ)
      (Additive (PowerQuotient (NumberField.Units.torsion F) ℓ)) = 1 := by
  have hpos : 0 < ℓ := by rcases hℓ with h | h <;> simp [h]
  have hdvd : ℓ ∣ 12 := by rcases hℓ with h | h <;> simp [h]
  let n : ℕ+ := ⟨ℓ, hpos⟩
  have em : PowerQuotient (NumberField.Units.torsion F) ℓ ≃*
      Multiplicative (ZMod ℓ) := A.torsionPowerQuotientEquiv n hdvd
  letI : AddCommGroup (ZMod ℓ) := (inferInstance : CommRing (ZMod ℓ)).toAddCommGroup
  let e := addEquivToZModLinearEquiv ℓ
    (Additive (PowerQuotient (NumberField.Units.torsion F) ℓ)) (ZMod ℓ)
    em.toAdditiveLeft
  exact e.finrank_eq.trans (Module.finrank_self (ZMod ℓ))

theorem sunit_structure_and_power_quotients :
    Nonempty (A.Rˣ ≃* NumberField.Units.torsion F ×
      Multiplicative (Fin (NumberField.InfinitePlace.nrComplexPlaces F +
        A.Sf.card - 1) → ℤ)) ∧
    Finite (NumberField.Units.torsion F) ∧
    (Module.finrank (ZMod 2)
      (Additive (PowerQuotient (NumberField.Units.torsion F) 2)) = 1 ∧
      Module.finrank (ZMod 2) (Additive (PowerQuotient A.Rˣ 2)) =
        NumberField.InfinitePlace.nrComplexPlaces F + A.Sf.card) ∧
    (Module.finrank (ZMod 3)
      (Additive (PowerQuotient (NumberField.Units.torsion F) 3)) = 1 ∧
      Module.finrank (ZMod 3) (Additive (PowerQuotient A.Rˣ 3)) =
        NumberField.InfinitePlace.nrComplexPlaces F + A.Sf.card) ∧
    Finite (PowerQuotient A.Rˣ 6) := by
  exact ⟨⟨A.unitStructure⟩, (torsion_finite (F := F)),
    ⟨A.finrank_torsionPowerQuotient 2 (Or.inl rfl),
      finrank_sunitPowerQuotient F A 2 (Or.inl rfl)⟩,
    ⟨A.finrank_torsionPowerQuotient 3 (Or.inr rfl),
      finrank_sunitPowerQuotient F A 3 (Or.inr rfl)⟩,
    sunitSixthPowerQuotient_finite F A⟩

end
end DedekindZetaZeroFree.SArithmeticData

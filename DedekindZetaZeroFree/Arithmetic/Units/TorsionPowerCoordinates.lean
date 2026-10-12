module

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData
public import ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.All

@[expose] public section

namespace DedekindZetaZeroFree.SArithmeticData

theorem primitive_roots_of_dvd_twelve {F : Type} [Field F] [NumberField F]
    (A : DedekindZetaZeroFree.SArithmeticData F) (n : ℕ+) (hn : (n : ℕ) ∣ 12) :
    (primitiveRoots (n : ℕ) F).Nonempty := by
  exact ⟨A.zeta12 ^ (12 / (n : ℕ)), (mem_primitiveRoots n.pos).2
    (A.primitive_zeta12.pow (by decide) (Nat.div_mul_cancel hn).symm)⟩

noncomputable def torsionPowerQuotientEquiv {F : Type} [Field F] [NumberField F]
    (A : DedekindZetaZeroFree.SArithmeticData F) (n : ℕ+) (hn : (n : ℕ) ∣ 12) :
    (NumberField.Units.torsion F ⧸
      (powMonoidHom (n : ℕ) :
        NumberField.Units.torsion F →* NumberField.Units.torsion F).range) ≃*
      Multiplicative (ZMod (n : ℕ)) := by
  exact KummerTheory.numberFieldTorsionNthPowerQuotientEquivZMod (K := F) n
    (A.primitive_roots_of_dvd_twelve n hn)

end DedekindZetaZeroFree.SArithmeticData

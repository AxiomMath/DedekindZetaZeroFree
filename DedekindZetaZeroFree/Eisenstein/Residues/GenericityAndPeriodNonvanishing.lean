module

public import DedekindZetaZeroFree.Adeles.Characters.CompactAbelianAndAdelicUniqueness

@[expose] public section

open MeasureTheory
open scoped NumberField MatrixGroups

namespace DedekindZetaZeroFree.KPGlobalGenericity

theorem split_root_invariance {G : Type*} [Group G]
    (j : SL(2, ℂ) →* G) (θ : G → ℂ)
    (hupper : ∀ (z : ℂ) (g : G),
      θ (j (Matrix.SpecialLinearGroup.transvection (i := 0) (j := 1) (by decide) z) * g) = θ g)
    (hlower : ∀ (z : ℂ) (g : G),
      θ (j (Matrix.SpecialLinearGroup.transvection (i := 1) (j := 0) (by decide) z) * g) = θ g) :
    ∀ s g, θ (j s * g) = θ g := by
  intro s
  apply Matrix.SL2.transvection_induction
      (fun s => ∀ g, θ (j s * g) = θ g) ?_ ?_ s
  · intro i k hik z
    fin_cases i <;> fin_cases k
    · exact (hik rfl).elim
    · exact hupper z
    · exact hlower z
    · exact (hik rfl).elim
  · intro A B hA hB g
    rw [map_mul, mul_assoc, hA, hB]

theorem unipotentFiber_eq
    (F : Type) [Field F] [NumberField F]
    {G : Type*} [Group G]
    (n : AddChar (NumberField.AdeleRing (𝓞 F) F) G) (θ : G → ℂ)
    (hθn : ∀ (t : F) (g : G),
      θ (n (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t) * g) = θ g)
    (g : G) (x : NumberField.AdeleRing (𝓞 F) F) :
    KPCompactFourier.unipotentFiber F n θ g (QuotientAddGroup.mk x) = θ (n x * g) := by
  let r := KPCompactFourier.representative F (QuotientAddGroup.mk x)
  have hr : (QuotientAddGroup.mk r : KPCompactFourier.AdditiveQuotient F) = QuotientAddGroup.mk x :=
    Quotient.out_eq' _
  have hm : r - x ∈ NumberField.AdeleRing.principalSubgroup (𝓞 F) F :=
    QuotientAddGroup.eq_iff_sub_mem.mp hr
  obtain ⟨t, ht⟩ := hm
  have hr' : r = algebraMap F (NumberField.AdeleRing (𝓞 F) F) t + x := by
    rw [ht]; abel
  change θ (n r * g) = _
  rw [hr', AddChar.map_add_eq_mul, mul_assoc, hθn]

end DedekindZetaZeroFree.KPGlobalGenericity

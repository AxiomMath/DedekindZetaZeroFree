module

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData
public import ClassFieldTheory.All

@[expose] public section

set_option autoImplicit false

namespace DedekindZetaZeroFree

theorem sunit_root_of_simpleKummerExtension_finrank_one
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (n : ℕ+) (a : A.U) (hnF : ((n : ℕ) : F) ≠ 0)
    (hdegree : Module.finrank F
      (KummerTheory.chosenSimpleKummerExtension F n hnF (a : Fˣ)) = 1) :
    ∃ b : A.U, b ^ (n : ℕ) = a := by
  let E := KummerTheory.chosenSimpleKummerExtension F n hnF (a : Fˣ)
  let β := KummerTheory.chosenSimpleKummerRootUnit F n hnF (a : Fˣ)
  have hbij : Function.Bijective (algebraMap F E) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp (by simpa only [E] using hdegree)
  obtain ⟨x, hx⟩ := hbij.2 (β : E)
  have hx0 : x ≠ 0 := by
    intro h
    have h0 : algebraMap F E x = 0 := by rw [h, map_zero]
    rw [hx] at h0
    exact β.ne_zero h0
  let b0 : Fˣ := Units.mk0 x hx0
  have hb0 : (b0 : F) = x := rfl
  have hmap : Units.map (algebraMap F E).toMonoidHom b0 = β := by
    apply Units.ext
    change algebraMap F E (b0 : F) = (β : E)
    rw [hb0, hx]
  have hpow : β ^ (n : ℕ) =
      Units.map (algebraMap F E).toMonoidHom (a : Fˣ) :=
    KummerTheory.chosenSimpleKummerRootUnit_pow F n hnF (a : Fˣ)
  have hpow2 : b0 ^ (n : ℕ) = (a : Fˣ) := by
    apply Units.map_injective hbij.1
    rw [map_pow, hmap, hpow]
  have hmem : b0 ∈ SUnitGroup (K := F) A.Sf := by
    apply KummerTheory.mem_sUnitGroup_of_pow_mem (K := F) A.Sf n b0
    rw [hpow2]
    exact a.property
  refine ⟨⟨b0, hmem⟩, ?_⟩
  exact Subtype.ext (by simpa using hpow2)

end DedekindZetaZeroFree

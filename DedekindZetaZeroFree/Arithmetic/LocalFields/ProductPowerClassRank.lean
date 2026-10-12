module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.PowerDefectProduct
public import DedekindZetaZeroFree.Arithmetic.LocalFields.PowerClassIndices

@[expose] public section

open scoped NumberField Classical
open NumberField

namespace DedekindZetaZeroFree
namespace SArithmeticData

noncomputable section
set_option maxHeartbeats 2000000

abbrev Vn (F : Type) [Field F] [NumberField F] (A : SArithmeticData F) (n : ℕ) :=
  (v : A.Place) → PowerQuotient (A.Completion v)ˣ n

instance instVnModule (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (n : ℕ) : Module (ZMod n) (Additive (Vn F A n)) :=
  (AddEquiv.piAdditive (fun v : A.Place => PowerQuotient (A.Completion v)ˣ n)).module
    (ZMod n)

private theorem Vn_finite_aux (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (n : ℕ) (hn : n = 2 ∨ n = 3) :
    Finite (Vn F A n) := by
  haveI (v : A.Place) : Finite (PowerQuotient (A.Completion v)ˣ n) := by
    cases v with
    | inl w =>
      haveI := A.infinite_power_quotient_subsingleton w n
        (by rcases hn with h | h <;> simp [IsLocalRootOrder, h])
      infer_instance
    | inr v =>
      exact A.finite_power_class_finite ⟨n, by omega⟩ hn v.val v.property
  infer_instance

private theorem Vn_card_aux (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (n : ℕ) (hn : n = 2 ∨ n = 3) :
    Nat.card (Vn F A n) = n ^ (2 * A.Sf.card + Module.finrank ℚ F) := by
  have hi (w : InfinitePlace F) : Nat.card (PowerQuotient w.Completionˣ n) = 1 := by
    haveI := A.infinite_power_quotient_subsingleton w n
      (by rcases hn with h | h <;> simp [IsLocalRootOrder, h])
    simp
  have hf (v : ↥A.Sf) : Nat.card (PowerQuotient (v.val.adicCompletion F)ˣ n) =
      n * (n * GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceNthPowerDefect
        (K := F) ⟨n, by omega⟩ v.val) := by
    exact GlobalClassFieldTheory.ClassFieldAxiom.card_finitePlace_nthPowerQuotient_eq_defect
      (K := F) ⟨n, by omega⟩
      ⟨A.zeta12 ^ (12 / n), (mem_primitiveRoots (show 0 < n by omega)).2
        (A.primitive_root n (by rcases hn with h | h <;> simp [IsLocalRootOrder, h]))⟩
      v.val
  rw [Nat.card_pi, Fintype.prod_sum_type]
  simp only [Completion, hi, Finset.prod_const_one, one_mul]
  simp_rw [hf, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe, A.prod_finitePlaceNthPowerDefect n hn]
  rw [pow_add, pow_mul]
  ring

theorem Vn_module_finite (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (n : ℕ) (hn : n = 2 ∨ n = 3) :
    Module.Finite (ZMod n) (Additive (Vn F A n)) := by
  haveI := Vn_finite_aux F A n hn
  infer_instance

theorem Vn_finrank (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (n : ℕ) (hn : n = 2 ∨ n = 3) :
    Module.finrank (ZMod n) (Additive (Vn F A n)) =
      2 * A.Sf.card + Module.finrank ℚ F := by
  haveI : Fact n.Prime := ⟨by rcases hn with h | h <;> rw [h] <;> norm_num⟩
  haveI := Vn_finite_aux F A n hn
  have hfr := Module.natCard_eq_pow_finrank (K := ZMod n)
    (V := Additive (Vn F A n))
  have hK : Nat.card (ZMod n) = n := by rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hK] at hfr
  apply Nat.pow_right_injective (by omega : 1 < n)
  change n ^ _ = n ^ _
  rw [← hfr, (Nat.card_congr (Additive.ofMul : Vn F A n ≃ Additive (Vn F A n))).symm]
  exact Vn_card_aux F A n hn

theorem Vn_finrank_complex (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (n : ℕ) (hn : n = 2 ∨ n = 3) :
    Module.finrank (ZMod n) (Additive (Vn F A n)) =
      2 * (A.Sf.card + InfinitePlace.nrComplexPlaces F) := by
  rw [Vn_finrank F A n hn]
  have hreal := InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
    (by decide : 2 < 12) A.primitive_zeta12
  have hdegree := InfinitePlace.card_add_two_mul_card_eq_rank (K := F)
  rw [hreal, zero_add] at hdegree
  rw [← hdegree]
  ring

theorem Vn_card (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (n : ℕ) (hn : n = 2 ∨ n = 3) :
    Nat.card (Vn F A n) = n ^ (2 * A.Sf.card + Module.finrank ℚ F) := by
  exact Vn_card_aux F A n hn

end
end SArithmeticData
end DedekindZetaZeroFree

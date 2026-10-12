module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.PrimeToIntegralIdealClasses
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealFactorization

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

theorem exists_integralIdealUnit_ratio (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (J : ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm)) :
    ∃ (A B : Ideal (𝓞 F)) (hA : A ≠ ⊥) (hB : B ≠ ⊥),
      A ⊔ m = ⊤ ∧ B ⊔ m = ⊤ ∧
        (J : ClassFieldTheory.NumberFieldFractionalIdealGroup F) =
          integralIdealUnit A hA * (integralIdealUnit B hB)⁻¹ := by
  classical
  let e := ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector
    (J : ClassFieldTheory.NumberFieldFractionalIdealGroup F)
  let s := e.support
  have hcop : ∀ v ∈ s, v.asIdeal ⊔ m = ⊤ := by
    intro v hv
    have hv0 : FractionalIdeal.count F v
        ((J : ClassFieldTheory.NumberFieldFractionalIdealGroup F) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
      simpa [s, e] using (Finsupp.mem_support_iff.mp hv)
    have hnot : ¬m ≤ v.asIdeal := by
      intro hle
      apply hv0
      apply J.property v
      rw [Finsupp.mem_support_iff, fullModulus_finitePart]
      exact (Associates.count_ne_zero_iff_dvd hm v.irreducible).mpr
        (Ideal.dvd_iff_le.mpr hle)
    apply (Ideal.isMaximal_def.mp (v.isPrime.isMaximal v.ne_bot)).lt_iff.mp
    exact lt_of_le_of_ne le_sup_left (fun he => hnot (he ▸ le_sup_right))
  let A : Ideal (𝓞 F) := ∏ v ∈ s, v.asIdeal ^ (e v).toNat
  let B : Ideal (𝓞 F) := ∏ v ∈ s, v.asIdeal ^ (-e v).toNat
  have hA : A ≠ ⊥ := Finset.prod_ne_zero_iff.mpr
    (fun v _ => pow_ne_zero _ v.ne_bot)
  have hB : B ≠ ⊥ := Finset.prod_ne_zero_iff.mpr
    (fun v _ => pow_ne_zero _ v.ne_bot)
  refine ⟨A, B, hA, hB, ?_, ?_, ?_⟩
  · exact Ideal.prod_sup_eq_top (fun v hv => Ideal.pow_sup_eq_top (hcop v hv))
  · exact Ideal.prod_sup_eq_top (fun v hv => Ideal.pow_sup_eq_top (hcop v hv))
  · apply Units.ext
    change ((J : ClassFieldTheory.NumberFieldFractionalIdealGroup F) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (A : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) *
        (B : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)⁻¹
    have hj : ClassFieldTheory.NumberFieldFractionalIdealGroup.factorization
        (Multiplicative.ofAdd e) = (J : ClassFieldTheory.NumberFieldFractionalIdealGroup F) := by
      apply ClassFieldTheory.NumberFieldFractionalIdealGroup.ext_count
      intro v
      rw [ClassFieldTheory.NumberFieldFractionalIdealGroup.count_factorization]
      exact ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector_apply _ v
    rw [← hj, ClassFieldTheory.NumberFieldFractionalIdealGroup.factorization_val]
    change (∏ v ∈ s, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ e v) = _
    have ha : (A : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        ∏ v ∈ s, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ (e v).toNat := by
      exact (map_prod (FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 F)) F) _ _).trans
        (Finset.prod_congr rfl (fun v _ => FractionalIdeal.coeIdeal_pow (nonZeroDivisors (𝓞 F)) F _ _))
    have hb : (B : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        ∏ v ∈ s, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ (-e v).toNat := by
      exact (map_prod (FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 F)) F) _ _).trans
        (Finset.prod_congr rfl (fun v _ => FractionalIdeal.coeIdeal_pow (nonZeroDivisors (𝓞 F)) F _ _))
    rw [ha, hb, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    have hn : e v = ((e v).toNat : ℤ) - ((-e v).toNat : ℤ) := by omega
    conv_lhs => rw [hn]
    rw [zpow_sub₀ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)]
    simp only [zpow_natCast, div_eq_mul_inv]

end DedekindZetaZeroFree.LargeSieve.RayBridge

end

module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.IntegralIdealModulus

@[expose] public section

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.RayClassBridge.RayFractional

variable (F : Type) [Field F] [NumberField F]
variable (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)

private lemma count_finset_prod_prime
    (s : Finset (HeightOneSpectrum (𝓞 F))) (n : HeightOneSpectrum (𝓞 F) → ℕ)
    (v : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F v
      ((∏ w ∈ s, w.asIdeal ^ n w : Ideal (𝓞 F)) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      if v ∈ s then (n v : ℤ) else 0 := by
  classical
  have hcoe :
      ((∏ w ∈ s, w.asIdeal ^ n w : Ideal (𝓞 F)) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        ∏ w ∈ s, (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ n w := by
    rw [show ((∏ w ∈ s, w.asIdeal ^ n w : Ideal (𝓞 F)) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 F)) F
          (∏ w ∈ s, w.asIdeal ^ n w) from rfl]
    rw [map_prod]
    exact Finset.prod_congr rfl fun w _ => map_pow _ _ _
  rw [hcoe]
  rw [show FractionalIdeal.count F v
        (∏ w ∈ s, (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ n w) =
      ∑ w ∈ s,
        FractionalIdeal.count F v ((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ n w)
      from FractionalIdeal.count_prod F v s _
        (fun w _ => pow_ne_zero _
          (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot))]
  simp only [FractionalIdeal.count_pow, FractionalIdeal.count_maximal, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq']

private lemma sup_mul_coprime (I J : Ideal (𝓞 F))
    (hI : I ⊔ 𝔪 = ⊤) (hJ : J ⊔ 𝔪 = ⊤) : (I * J) ⊔ 𝔪 = ⊤ := by
  rw [eq_top_iff]
  calc (⊤ : Ideal (𝓞 F)) = (I ⊔ 𝔪) * (J ⊔ 𝔪) := by rw [hI, hJ]; simp
    _ = (I * J ⊔ I * 𝔪) ⊔ (𝔪 * J ⊔ 𝔪 * 𝔪) := by
        rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    _ ≤ I * J ⊔ 𝔪 := by
        refine sup_le (sup_le le_sup_left ?_) (sup_le ?_ ?_)
        · exact le_trans Ideal.mul_le_right le_sup_right
        · exact le_trans Ideal.mul_le_left le_sup_right
        · exact le_trans Ideal.mul_le_left le_sup_right

private lemma sup_pow_coprime (I : Ideal (𝓞 F)) (n : ℕ) (h : I ⊔ 𝔪 = ⊤) :
    (I ^ n) ⊔ 𝔪 = ⊤ := by
  induction n with
  | zero => simp [Ideal.one_eq_top]
  | succ n ih => rw [pow_succ]; exact sup_mul_coprime F 𝔪 _ _ ih h

private lemma sup_finset_prod_coprime (s : Finset (HeightOneSpectrum (𝓞 F)))
    (n : HeightOneSpectrum (𝓞 F) → ℕ)
    (h : ∀ v ∈ s, v.asIdeal ⊔ 𝔪 = ⊤) :
    (∏ v ∈ s, v.asIdeal ^ n v) ⊔ 𝔪 = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ideal.one_eq_top]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact sup_mul_coprime F 𝔪 _ _
        (sup_pow_coprime F 𝔪 _ _ (h a (Finset.mem_insert_self a s)))
        (ih fun v hv => h v (Finset.mem_insert_of_mem hv))

private lemma coprime_of_mem_subgroup
    (x : ClassFieldTheory.NumberFieldFractionalIdealGroup F)
    (hx : x ∈ ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus F 𝔪 h𝔪))
    (v : HeightOneSpectrum (𝓞 F))
    (hv : FractionalIdeal.count F v
      (x : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0) :
    v.asIdeal ⊔ 𝔪 = ⊤ := by
  classical
  have h𝔪0 : 𝔪 ≠ 0 := by rw [Ideal.zero_eq_bot]; exact h𝔪
  have hnotmem : v ∉ (narrowIdealModulus F 𝔪 h𝔪).finitePart.support := fun hmem => hv (hx v hmem)
  have hzero : (narrowIdealModulus F 𝔪 h𝔪).finitePart v = 0 :=
    Finsupp.notMem_support_iff.mp hnotmem
  rw [narrowIdealModulus_finitePart] at hzero
  have hcount : FractionalIdeal.count F v (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 :=
    le_antisymm (Int.toNat_eq_zero.mp hzero)
      (FractionalIdeal.count_coe_nonneg F v 𝔪)
  have hndvd : ¬ v.asIdeal ∣ 𝔪 := by
    rw [← Associates.count_ne_zero_iff_dvd h𝔪0 v.irreducible]
    intro h
    have hz : ((Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors : ℤ) = 0 := by
      rw [← FractionalIdeal.count_coe F v h𝔪0]
      exact hcount
    exact h (by exact_mod_cast hz)
  have hnotle : ¬ 𝔪 ≤ v.asIdeal := fun h => hndvd (Ideal.dvd_iff_le.mpr h)
  by_contra hne
  have hmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have heq : v.asIdeal = v.asIdeal ⊔ 𝔪 := hmax.eq_of_le hne le_sup_left
  exact hnotle (heq.symm ▸ le_sup_right)

theorem exists_integralUnit_ratio
    (x : ClassFieldTheory.NumberFieldFractionalIdealGroup F)
    (hx : x ∈ ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus F 𝔪 h𝔪)) :
    ∃ (A B : Ideal (𝓞 F)) (hA : A ≠ ⊥) (hB : B ≠ ⊥)
      (hcA : A ⊔ 𝔪 = ⊤) (hcB : B ⊔ 𝔪 = ⊤),
      x = integralUnit F A hA * (integralUnit F B hB)⁻¹ := by
  classical
  let e := ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector x
  let P : Finset (HeightOneSpectrum (𝓞 F)) := e.support.filter (fun v => 0 < e v)
  let N : Finset (HeightOneSpectrum (𝓞 F)) := e.support.filter (fun v => e v < 0)
  let A : Ideal (𝓞 F) := ∏ v ∈ P, v.asIdeal ^ (e v).toNat
  let B : Ideal (𝓞 F) := ∏ v ∈ N, v.asIdeal ^ (-(e v)).toNat
  have hmemP : ∀ v, v ∈ P ↔ 0 < e v := by
    intro v
    rw [Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_gt h, h⟩⟩
  have hmemN : ∀ v, v ∈ N ↔ e v < 0 := by
    intro v
    rw [Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
  have hcountA : ∀ v, FractionalIdeal.count F v
      (A : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      = if v ∈ P then ((e v).toNat : ℤ) else 0 := by
    intro v
    exact count_finset_prod_prime F P (fun w => (e w).toNat) v
  have hcountB : ∀ v, FractionalIdeal.count F v
      (B : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      = if v ∈ N then ((-(e v)).toNat : ℤ) else 0 := by
    intro v
    exact count_finset_prod_prime F N (fun w => (-(e w)).toNat) v
  have hA : A ≠ ⊥ := by
    by_cases hP : P = ∅
    · have hAeq : A = ⊤ := by
        change (∏ v ∈ P, v.asIdeal ^ (e v).toNat) = ⊤
        rw [hP]
        simp [Ideal.one_eq_top]
      rw [hAeq]
      exact top_ne_bot
    · obtain ⟨v, hvP⟩ := Finset.nonempty_iff_ne_empty.mpr hP
      intro hbot
      have hc := hcountA v
      rw [hbot, FractionalIdeal.coeIdeal_bot, FractionalIdeal.count_zero, if_pos hvP] at hc
      have hpos : 0 < e v := (hmemP v).mp hvP
      have hcast : ((e v).toNat : ℤ) = e v := Int.toNat_of_nonneg (le_of_lt hpos)
      exact (by rw [hcast]; omega : ((e v).toNat : ℤ) ≠ 0) hc.symm
  have hB : B ≠ ⊥ := by
    by_cases hN : N = ∅
    · have hBeq : B = ⊤ := by
        change (∏ v ∈ N, v.asIdeal ^ (-(e v)).toNat) = ⊤
        rw [hN]
        simp [Ideal.one_eq_top]
      rw [hBeq]
      exact top_ne_bot
    · obtain ⟨v, hvN⟩ := Finset.nonempty_iff_ne_empty.mpr hN
      intro hbot
      have hc := hcountB v
      rw [hbot, FractionalIdeal.coeIdeal_bot, FractionalIdeal.count_zero, if_pos hvN] at hc
      have hpos : 0 < -(e v) := neg_pos.mpr ((hmemN v).mp hvN)
      have hcast : ((-(e v)).toNat : ℤ) = -(e v) := Int.toNat_of_nonneg (le_of_lt hpos)
      exact (by rw [hcast]; omega : ((-(e v)).toNat : ℤ) ≠ 0) hc.symm
  have hcA : A ⊔ 𝔪 = ⊤ := by
    refine sup_finset_prod_coprime F 𝔪 P (fun v => (e v).toNat) fun v hvP => ?_
    refine coprime_of_mem_subgroup F 𝔪 h𝔪 x hx v ?_
    rw [← ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector_apply x v]
    exact ne_of_gt ((hmemP v).mp hvP)
  have hcB : B ⊔ 𝔪 = ⊤ := by
    refine sup_finset_prod_coprime F 𝔪 N (fun v => (-(e v)).toNat) fun v hvN => ?_
    refine coprime_of_mem_subgroup F 𝔪 h𝔪 x hx v ?_
    rw [← ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector_apply x v]
    exact ne_of_lt ((hmemN v).mp hvN)
  refine ⟨A, B, hA, hB, hcA, hcB, ?_⟩
  apply ClassFieldTheory.NumberFieldFractionalIdealGroup.ext_count
  intro v
  have hR : FractionalIdeal.count F v
      ((integralUnit F A hA * (integralUnit F B hB)⁻¹ :
        ClassFieldTheory.NumberFieldFractionalIdealGroup F) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      = FractionalIdeal.count F v (A : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
        - FractionalIdeal.count F v (B : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, integralUnit_val, integralUnit_val,
      FractionalIdeal.count_mul, FractionalIdeal.count_inv]
    · ring
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr hA
    · exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hB)
  rw [hR, hcountA v, hcountB v,
    ← ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector_apply x v]
  by_cases hpos : 0 < e v
  · rw [if_pos ((hmemP v).mpr hpos), if_neg (fun h => absurd ((hmemN v).mp h) (by omega)),
      Int.toNat_of_nonneg (le_of_lt hpos)]
    ring
  · by_cases hneg : e v < 0
    · rw [if_neg (fun h => absurd ((hmemP v).mp h) hpos), if_pos ((hmemN v).mpr hneg),
        Int.toNat_of_nonneg (neg_nonneg.mpr (le_of_lt hneg))]
      ring
    · have hz : e v = 0 := by omega
      rw [hz, if_neg (fun h => absurd ((hmemP v).mp h) (by omega)),
        if_neg (fun h => absurd ((hmemN v).mp h) (by omega))]
      ring

theorem exists_integralPrimeTo_ratio
    (x : ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus F 𝔪 h𝔪)) :
    ∃ (A B : Ideal (𝓞 F)) (hA : A ≠ ⊥) (hB : B ≠ ⊥)
      (hcA : A ⊔ 𝔪 = ⊤) (hcB : B ⊔ 𝔪 = ⊤),
      x = integralPrimeTo F 𝔪 h𝔪 A hA hcA * (integralPrimeTo F 𝔪 h𝔪 B hB hcB)⁻¹ := by
  obtain ⟨A, B, hA, hB, hcA, hcB, hx⟩ :=
    exists_integralUnit_ratio F 𝔪 h𝔪 (x : ClassFieldTheory.NumberFieldFractionalIdealGroup F) x.2
  refine ⟨A, B, hA, hB, hcA, hcB, ?_⟩
  apply Subtype.ext
  change (x : ClassFieldTheory.NumberFieldFractionalIdealGroup F) =
    integralUnit F A hA * (integralUnit F B hB)⁻¹
  exact hx

theorem monoidHom_ext_of_integralPrimeTo {M : Type*} [Group M]
    (χ ψ : ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus F 𝔪 h𝔪) →* M)
    (h : ∀ (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤),
      χ (integralPrimeTo F 𝔪 h𝔪 I hI hcop) = ψ (integralPrimeTo F 𝔪 h𝔪 I hI hcop)) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  obtain ⟨A, B, hA, hB, hcA, hcB, hx⟩ := exists_integralPrimeTo_ratio F 𝔪 h𝔪 x
  rw [hx, map_mul, map_inv, map_mul, map_inv, h A hA hcA, h B hB hcB]

theorem eq_of_integral_values
    (χ ψ : ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus F 𝔪 h𝔪) →* ℂˣ)
    (h : ∀ (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤),
      (χ (integralPrimeTo F 𝔪 h𝔪 I hI hcop) : ℂ) =
        (ψ (integralPrimeTo F 𝔪 h𝔪 I hI hcop) : ℂ)) :
    χ = ψ :=
  monoidHom_ext_of_integralPrimeTo F 𝔪 h𝔪 χ ψ fun I hI hcop => Units.ext (h I hI hcop)

end DedekindZetaZeroFree.RayClassBridge.RayFractional

end

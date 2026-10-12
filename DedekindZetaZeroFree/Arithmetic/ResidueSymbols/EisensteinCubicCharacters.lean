module

public import DedekindZetaZeroFree.Arithmetic.Ideals.EisensteinIntegers.PrimaryIdealDomain
public import Mathlib.NumberTheory.JacobiSum.Basic

@[expose] public section

namespace DedekindZetaZeroFree.Eisenstein

abbrev redq (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (q : Ideal (R E)) :
    R E →+* (R E ⧸ q) := Ideal.Quotient.mk q

@[instance_reducible] noncomputable def residueField (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (q : Ideal (R E)) (hq0 : q ≠ ⊥)
    (hqp : q.IsPrime) : Field (R E ⧸ q) := by
  letI : q.IsMaximal := hqp.isMaximal hq0
  exact Ideal.Quotient.field q

@[instance_reducible] noncomputable def residueFintype (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (q : Ideal (R E)) (hq0 : q ≠ ⊥) :
    Fintype (R E ⧸ q) := by
  letI : Finite (R E ⧸ q) := Ring.HasFiniteQuotients.finiteQuotient hq0
  exact Fintype.ofFinite _

noncomputable def residueCard (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (q : Ideal (R E)) (hq0 : q ≠ ⊥) : ℕ :=
  @Fintype.card (R E ⧸ q) (residueFintype E q hq0)

noncomputable def cubicResidueExponent (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (q : Ideal (R E)) (hq0 : q ≠ ⊥) : ℕ :=
  (residueCard E q hq0 - 1) / 3

theorem redq_η_isPrimitiveRoot (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    IsPrimitiveRoot (redq E q (η E ω hω)) 3 := by
  classical
  letI := residueField E q hq0 hqp
  have h3 : (3 : R E ⧸ q) ≠ 0 := by
    intro h
    have hmem : (3 : R E) ∈ q := Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using h)
    have h6 : (6 : R E) ∈ q := by
      convert q.mul_mem_left 2 hmem using 1 <;> norm_num
    have hle : Ideal.span {(6 : R E)} ≤ q := Ideal.span_le.mpr (by simpa using h6)
    have ht : q = ⊤ := by simpa [sup_eq_left.mpr hle] using hq6
    exact hqp.ne_top ht
  have hp := hω.toInteger_isPrimitiveRoot
  have hpow : redq E q (η E ω hω) ^ 3 = 1 := by
    rw [← map_pow, hp.pow_eq_one, map_one]
  have hne : redq E q (η E ω hω) ≠ 1 := by
    intro h
    have hg := congrArg (redq E q) (hp.geom_sum_eq_zero (by decide : 1 < 3))
    simp [Finset.sum_range_succ, map_add, map_pow, h] at hg
    exact h3 (by linear_combination hg)
  exact isPrimitiveRoot_of_mem_nthRootsFinset (by decide : Nat.Prime 3)
    ((Polynomial.mem_nthRootsFinset (by decide : 0 < 3) 1).mpr hpow) hne

theorem three_dvd_residueCard_sub_one (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (q : Ideal (R E))
    (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    3 ∣ residueCard E q hq0 - 1 := by
  letI := residueField E q hq0 hqp
  letI := residueFintype E q hq0
  obtain ⟨ω, hω⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ E
    (Set.mem_singleton 3) (by decide : 3 ≠ 0)
  have hp := redq_η_isPrimitiveRoot E ω hω q hq0 hqp hq6
  exact hp.dvd_of_pow_eq_one _ (FiniteField.pow_card_sub_one_eq_one _
    (hp.ne_zero (by decide : 3 ≠ 0)))

theorem cubicResidueExponent_pos (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (q : Ideal (R E))
    (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    0 < cubicResidueExponent E q hq0 := by
  letI := residueField E q hq0 hqp
  letI := residueFintype E q hq0
  have hc : 1 < residueCard E q hq0 := Fintype.one_lt_card
  have hd := three_dvd_residueCard_sub_one E q hq0 hqp hq6
  unfold cubicResidueExponent
  exact Nat.div_pos (Nat.le_of_dvd (by omega) hd) (by decide)

theorem twice_cubicResidueExponent_lt (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (q : Ideal (R E))
    (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    2 * cubicResidueExponent E q hq0 < residueCard E q hq0 - 1 := by
  have hp := cubicResidueExponent_pos E q hq0 hqp hq6
  have hd := three_dvd_residueCard_sub_one E q hq0 hqp hq6
  have he : cubicResidueExponent E q hq0 * 3 = residueCard E q hq0 - 1 :=
    Nat.div_mul_cancel hd
  omega

private theorem roots_red_bijective (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    Function.Bijective (restrictRootsOfUnity (redq E q) 3) := by
  letI := residueField E q hq0 hqp
  have hp := hω.toInteger_isPrimitiveRoot
  have hr := redq_η_isPrimitiveRoot E ω hω q hq0 hqp hq6
  constructor
  · intro a b hab
    obtain ⟨i, hi, hai⟩ := hp.eq_pow_of_pow_eq_one ((mem_rootsOfUnity' 3 a.val).mp a.prop)
    obtain ⟨j, hj, hbj⟩ := hp.eq_pow_of_pow_eq_one ((mem_rootsOfUnity' 3 b.val).mp b.prop)
    have he : i = j := hr.pow_inj hi hj (by
      have hv := congrArg (fun z : rootsOfUnity 3 (R E ⧸ q) => (z.val : R E ⧸ q)) hab
      change redq E q (a.val : R E) = redq E q (b.val : R E) at hv
      simpa only [← hai, ← hbj, map_pow] using hv)
    apply rootsOfUnity.coe_injective
    simpa only [← hai, ← hbj, he]
  · intro a
    obtain ⟨i, hi, hai⟩ := hr.eq_pow_of_pow_eq_one ((mem_rootsOfUnity' 3 a.val).mp a.prop)
    refine ⟨rootsOfUnity.mkOfPowEq (η E ω hω ^ i) ?_, ?_⟩
    · rw [← pow_mul, Nat.mul_comm i 3, pow_mul, hp.pow_eq_one, one_pow]
    · apply rootsOfUnity.coe_injective
      change redq E q (η E ω hω ^ i) = (a.val : R E ⧸ q)
      simpa only [map_pow] using hai

theorem existsUnique_cubicResidueCharacter (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    ∃! ρ : MulChar (R E ⧸ q) (R E),
      ρ 0 = 0 ∧ ∀ x : R E ⧸ q, x ≠ 0 →
        ρ x ∈ ({1, η E ω hω, η E ω hω ^ 2} : Set (R E)) ∧
        redq E q (ρ x) = x ^ cubicResidueExponent E q hq0 := by
  classical
  letI := residueField E q hq0 hqp
  letI := residueFintype E q hq0
  let e := MulEquiv.ofBijective (restrictRootsOfUnity (redq E q) 3)
    (roots_red_bijective E ω hω q hq0 hqp hq6)
  let f : (R E ⧸ q)ˣ →* rootsOfUnity 3 (R E ⧸ q) := {
    toFun := fun x => ⟨x ^ cubicResidueExponent E q hq0, by
      rw [mem_rootsOfUnity, ← pow_mul, cubicResidueExponent, Nat.div_mul_cancel
        (three_dvd_residueCard_sub_one E q hq0 hqp hq6)]
      apply Units.ext
      exact FiniteField.pow_card_sub_one_eq_one (x : R E ⧸ q) x.ne_zero⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by intros; apply Subtype.ext; simp [mul_pow] }
  let g : (R E ⧸ q)ˣ →* (R E)ˣ :=
    (rootsOfUnity 3 (R E)).subtype.comp (e.symm.toMonoidHom.comp f)
  let ρ := MulChar.ofUnitHom g
  have hred (x : (R E ⧸ q)ˣ) : redq E q (ρ x) = (x : R E ⧸ q) ^ cubicResidueExponent E q hq0 := by
    have he := e.apply_symm_apply (f x)
    have hv := congrArg (fun z : rootsOfUnity 3 (R E ⧸ q) => (z.val : R E ⧸ q)) he
    change redq E q (g x : R E) = (x : R E ⧸ q) ^ cubicResidueExponent E q hq0 at hv
    simpa only [ρ, MulChar.ofUnitHom_coe] using hv
  have hcube (x : (R E ⧸ q)ˣ) : ρ x ^ 3 = 1 := by
    change (MulChar.ofUnitHom g) x ^ 3 = 1
    rw [MulChar.ofUnitHom_coe]
    exact (mem_rootsOfUnity' 3 (e.symm (f x)).val).mp (e.symm (f x)).prop
  have hmem (x : (R E ⧸ q)ˣ) :
      ρ x ∈ ({1, η E ω hω, η E ω hω ^ 2} : Set (R E)) := by
    obtain ⟨i, hi, hei⟩ := hω.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one (hcube x)
    interval_cases i <;> simp_all
  refine ⟨ρ, ⟨MulChar.map_zero _, ?_⟩, ?_⟩
  · intro x hx
    lift x to (R E ⧸ q)ˣ using (isUnit_iff_ne_zero.mpr hx)
    exact ⟨hmem x, hred x⟩
  · intro χ hχ
    apply MulChar.ext
    intro x
    have hx := hχ.2 x x.ne_zero
    have hχcube : χ x ^ 3 = 1 := by
      rcases hx.1 with h | h | h <;> rw [h]
      · simp
      · exact hω.toInteger_isPrimitiveRoot.pow_eq_one
      · rw [← pow_mul, show 2 * 3 = 3 * 2 by decide, pow_mul,
          hω.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    have he : restrictRootsOfUnity (redq E q) 3 (rootsOfUnity.mkOfPowEq (χ x) hχcube) =
        restrictRootsOfUnity (redq E q) 3 (rootsOfUnity.mkOfPowEq (ρ x) (hcube x)) := by
      apply rootsOfUnity.coe_injective
      exact hx.2.trans (hred x).symm
    exact congrArg (fun z : rootsOfUnity 3 (R E) => (z.val : R E))
      ((roots_red_bijective E ω hω q hq0 hqp hq6).1 he)

noncomputable def ρq (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) : MulChar (R E ⧸ q) (R E) :=
  Classical.choose (existsUnique_cubicResidueCharacter E ω hω q hq0 hqp hq6)

@[simp] theorem ρq_zero (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    ρq E ω hω q hq0 hqp hq6 0 = 0 := by
  exact MulChar.map_zero _

theorem ρq_mem (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) (x : R E ⧸ q) (hx : x ≠ 0) :
    ρq E ω hω q hq0 hqp hq6 x ∈ ({1, η E ω hω, η E ω hω ^ 2} : Set (R E)) := by
  exact (Classical.choose_spec (existsUnique_cubicResidueCharacter E ω hω q hq0 hqp hq6)).1.2 x hx |>.1

theorem redq_ρq (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) (x : R E ⧸ q) :
    redq E q (ρq E ω hω q hq0 hqp hq6 x) = x ^ cubicResidueExponent E q hq0 := by
  by_cases hx : x = 0
  · subst x
    simp [cubicResidueExponent_pos E q hq0 hqp hq6 |>.ne']
  · exact (Classical.choose_spec (existsUnique_cubicResidueCharacter E ω hω q hq0 hqp hq6)).1.2 x hx |>.2

theorem orderOf_ρq (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    orderOf (ρq E ω hω q hq0 hqp hq6) = 3 := by
  letI := residueField E q hq0 hqp
  letI := residueFintype E q hq0
  have hc : ρq E ω hω q hq0 hqp hq6 ^ 3 = 1 := by
    apply MulChar.ext
    intro x
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    have hm := ρq_mem E ω hω q hq0 hqp hq6 x x.ne_zero
    rcases hm with h | h | h <;> rw [h]
    · simp
    · exact hω.toInteger_isPrimitiveRoot.pow_eq_one
    · rw [← pow_mul, show 2 * 3 = 3 * 2 by decide, pow_mul,
        hω.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
  have hn : ρq E ω hω q hq0 hqp hq6 ≠ 1 := by
    intro he
    have ha : ∀ x : (R E ⧸ q)ˣ, x ^ cubicResidueExponent E q hq0 = 1 := by
      intro x
      apply Units.ext
      have hr := redq_ρq E ω hω q hq0 hqp hq6 x
      simpa only [he, MulChar.one_apply_coe, map_one, Units.val_pow_eq_pow_val,
        Units.val_one] using hr.symm
    have hd := (FiniteField.forall_pow_eq_one_iff (R E ⧸ q) _).mp ha
    have hp := cubicResidueExponent_pos E q hq0 hqp hq6
    have hl := twice_cubicResidueExponent_lt E q hq0 hqp hq6
    have hle := Nat.le_of_dvd hp hd
    change residueCard E q hq0 - 1 ≤ cubicResidueExponent E q hq0 at hle
    omega
  exact orderOf_eq_prime hc hn

theorem ρq_cube (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    ρq E ω hω q hq0 hqp hq6 ^ 3 = 1 := by
  simpa [orderOf_ρq E ω hω q hq0 hqp hq6] using pow_orderOf_eq_one (ρq E ω hω q hq0 hqp hq6)

theorem ρq_sq_ne_one (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    ρq E ω hω q hq0 hqp hq6 ^ 2 ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one h
  rw [orderOf_ρq E ω hω q hq0 hqp hq6] at this
  norm_num at this

@[simp] theorem ρq_neg_one (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    ρq E ω hω q hq0 hqp hq6 (-1) = 1 := by
  exact MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) (ρq_cube E ω hω q hq0 hqp hq6)

noncomputable def ρqC (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (ι : E →+* ℂ) (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) : MulChar (R E ⧸ q) ℂ :=
  (ρq E ω hω q hq0 hqp hq6).ringHomComp (ιR E ι)

theorem ρqC_facts (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (ι : E →+* ℂ) (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    orderOf (ρqC E ω hω ι q hq0 hqp hq6) = 3 ∧
      ρqC E ω hω ι q hq0 hqp hq6 ^ 3 = 1 ∧
      ρqC E ω hω ι q hq0 hqp hq6 ^ 2 ≠ 1 ∧
      ρqC E ω hω ι q hq0 hqp hq6 (-1) = 1 := by
  have hi : Function.Injective (ιR E ι) := ι.injective.comp NumberField.RingOfIntegers.coe_injective
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (orderOf_injective (MulChar.ringHomCompHom (ιR E ι))
      (MulChar.injective_ringHomComp hi) _).trans (orderOf_ρq E ω hω q hq0 hqp hq6)
  · simp only [ρqC, MulChar.ringHomComp_pow, ρq_cube, MulChar.ringHomComp_one]
  · simpa only [ρqC, MulChar.ringHomComp_pow, MulChar.ringHomComp_ne_one_iff hi] using
      ρq_sq_ne_one E ω hω q hq0 hqp hq6
  · simp only [ρqC, MulChar.ringHomComp_apply, ρq_neg_one, map_one]

end DedekindZetaZeroFree.Eisenstein

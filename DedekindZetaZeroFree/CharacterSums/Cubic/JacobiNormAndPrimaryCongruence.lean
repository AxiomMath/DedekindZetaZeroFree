module
public import Mathlib.NumberTheory.MulChar.Lemmas

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.EisensteinCubicCharacters
public import DedekindZetaZeroFree.Arithmetic.Ideals.EisensteinIntegers.CoordinateNorms

@[expose] public section

namespace DedekindZetaZeroFree.Eisenstein

private lemma normSq_jacobiSum_self {F : Type} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) (hχχ : χ * χ ≠ 1)
    (hchar : ringChar ℂ ≠ ringChar F) :
    Complex.normSq (jacobiSum χ χ) = (Fintype.card F : ℝ) := by
  have hinv : jacobiSum χ⁻¹ χ⁻¹ = star (jacobiSum χ χ) := by
    rw [← MulChar.star_eq_inv χ]
    exact jacobiSum_ringHomComp χ χ (starRingEnd ℂ)
  have H := jacobiSum_mul_jacobiSum_inv hchar hχ hχ hχχ
  rw [hinv] at H
  have hnum : (Complex.normSq (jacobiSum χ χ) : ℂ) = (Fintype.card F : ℂ) := by
    rw [← Complex.mul_conj]
    exact H
  exact Complex.ofReal_injective hnum

noncomputable def Jq (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) : R E :=
  letI := residueFintype E q hq0
  jacobiSum (ρq E ω hω q hq0 hqp hq6) (ρq E ω hω q hq0 hqp hq6)

theorem ιR_Jq (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (ι : E →+* ℂ) (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    letI := residueFintype E q hq0
    ιR E ι (Jq E ω hω q hq0 hqp hq6) =
      jacobiSum (ρqC E ω hω ι q hq0 hqp hq6) (ρqC E ω hω ι q hq0 hqp hq6) := by
  letI := residueFintype E q hq0
  simp only [Jq, ρqC]
  rw [jacobiSum_ringHomComp]

theorem normSq_Jq (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (ι : E →+* ℂ) (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    Complex.normSq (ιR E ι (Jq E ω hω q hq0 hqp hq6)) =
      (residueCard E q hq0 : ℝ) := by
  letI : Field (R E ⧸ q) := residueField E q hq0 hqp
  letI : Fintype (R E ⧸ q) := residueFintype E q hq0
  have hχ : ρqC E ω hω ι q hq0 hqp hq6 ≠ 1 := by
    intro h
    have := (ρqC_facts E ω hω ι q hq0 hqp hq6).1
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hχχ : ρqC E ω hω ι q hq0 hqp hq6 * ρqC E ω hω ι q hq0 hqp hq6 ≠ 1 := by
    have := (ρqC_facts E ω hω ι q hq0 hqp hq6).2.2.1
    rwa [pow_two] at this
  have hC : ringChar ℂ = 0 := (CharP.ringChar_zero_iff_CharZero ℂ).mpr inferInstance
  have hchar : ringChar ℂ ≠ ringChar (R E ⧸ q) := by
    rw [hC]
    exact fun h => CharP.ringChar_ne_zero_of_finite (R E ⧸ q) h.symm
  have main := normSq_jacobiSum_self (ρqC E ω hω ι q hq0 hqp hq6) hχ hχχ hchar
  rw [ιR_Jq E ω hω ι q hq0 hqp hq6]
  exact main

theorem absNorm_span_Jq (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    Ideal.absNorm (Ideal.span {Jq E ω hω q hq0 hqp hq6}) = residueCard E q hq0 := by
  obtain ⟨ι⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 := absNorm_span_eq_normSq E ι (Jq E ω hω q hq0 hqp hq6)
  have h2 := normSq_Jq E ω hω ι q hq0 hqp hq6
  exact Nat.cast_injective (h1.trans h2)

theorem Jq_add_one_mem_m3 (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    Jq E ω hω q hq0 hqp hq6 + 1 ∈ m3 E := by
  letI : Field (R E ⧸ q) := residueField E q hq0 hqp
  letI : Fintype (R E ⧸ q) := residueFintype E q hq0
  obtain ⟨z, _hz, hzJ⟩ :=
    exists_jacobiSum_eq_neg_one_add (F := R E ⧸ q) (R := R E) (n := 3) (by norm_num)
      (ρq_cube E ω hω q hq0 hqp hq6) (ρq_cube E ω hω q hq0 hqp hq6)
      (three_dvd_residueCard_sub_one E q hq0 hqp hq6) hω.toInteger_isPrimitiveRoot
  have hη : (η E ω hω - 1) ^ 2 = -(3 : R E) * η E ω hω := by
    linear_combination eta_sq_add_eta_add_one E ω hω
  have hJq : Jq E ω hω q hq0 hqp hq6 =
      jacobiSum (ρq E ω hω q hq0 hqp hq6) (ρq E ω hω q hq0 hqp hq6) := rfl
  rw [hJq, hzJ, hη]
  exact Ideal.mem_span_singleton.mpr ⟨-(z * η E ω hω), by ring⟩

theorem red3_Jq (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    red3 E (Jq E ω hω q hq0 hqp hq6) = -1 := by
  have h := Jq_add_one_mem_m3 E ω hω q hq0 hqp hq6
  have h0 : red3 E (Jq E ω hω q hq0 hqp hq6 + 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr h
  rw [map_add, map_one] at h0
  exact eq_neg_iff_add_eq_zero.mpr h0

end DedekindZetaZeroFree.Eisenstein

module

public import DedekindZetaZeroFree.CharacterSums.Cubic.JacobiNormAndPrimaryCongruence
public import DedekindZetaZeroFree.CharacterSums.Cubic.JacobiPrimeReduction
public import DedekindZetaZeroFree.Arithmetic.Ideals.EisensteinIntegers.PrimaryGenerators

@[expose] public section

namespace DedekindZetaZeroFree.Eisenstein

theorem mem_I3_of_sup_span_six_eq_top (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (q : Ideal (R E)) (hq0 : q ≠ ⊥)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    q ∈ I3 E := by
  refine (mem_I3 E q).mpr ⟨hq0, ?_⟩
  apply top_unique
  rw [← hq6]
  apply sup_le_sup_left
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact ⟨2, by norm_num⟩

def q3 (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (q : Ideal (R E)) (hq0 : q ≠ ⊥)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) : I3 E :=
  ⟨q, mem_I3_of_sup_span_six_eq_top E q hq0 hq6⟩

theorem span_Jq (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    Ideal.span {Jq E ω hω q hq0 hqp hq6} = q := by
  have hmem : Jq E ω hω q hq0 hqp hq6 ∈ q :=
    jacobiSum_ρq_mem E ω hω q hq0 hqp hq6
  have hle : Ideal.span {Jq E ω hω q hq0 hqp hq6} ≤ q :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  obtain ⟨B, hB⟩ := (Ideal.dvd_iff_le.mpr hle : q ∣ Ideal.span {Jq E ω hω q hq0 hqp hq6})
  have habsP : Ideal.absNorm (Ideal.span {Jq E ω hω q hq0 hqp hq6}) = residueCard E q hq0 :=
    absNorm_span_Jq E ω hω q hq0 hqp hq6
  have habsq : Ideal.absNorm q = residueCard E q hq0 := by
    letI := residueFintype E q hq0
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact Nat.card_eq_fintype_card
  have habs_eq : Ideal.absNorm (Ideal.span {Jq E ω hω q hq0 hqp hq6}) = Ideal.absNorm q :=
    habsP.trans habsq.symm
  have hprod : Ideal.absNorm q * Ideal.absNorm B = Ideal.absNorm q := by
    rw [← map_mul, ← hB]
    exact habs_eq
  have hAne : Ideal.absNorm q ≠ 0 := fun h => hq0 (Ideal.absNorm_eq_zero_iff.mp h)
  have hB1 : Ideal.absNorm B = 1 :=
    Nat.mul_left_cancel (Nat.pos_of_ne_zero hAne) (by rw [mul_one]; exact hprod)
  have hBtop : B = ⊤ := Ideal.absNorm_eq_one_iff.mp hB1
  rw [hB, hBtop, Ideal.mul_top]

theorem Jq_eq_neg_primaryGenerator (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    Jq E ω hω q hq0 hqp hq6 = -primaryGenerator E (q3 E q hq0 hq6) := by
  have hspan : Ideal.span {Jq E ω hω q hq0 hqp hq6} = q :=
    span_Jq E ω hω q hq0 hqp hq6
  have hspanPG : Ideal.span {primaryGenerator E (q3 E q hq0 hq6)} = q := by
    rw [span_primaryGenerator]
    rfl
  have hxy : Ideal.span {-(Jq E ω hω q hq0 hqp hq6)} =
      Ideal.span {primaryGenerator E (q3 E q hq0 hq6)} := by
    rw [Ideal.span_singleton_neg, hspan, hspanPG]
  have hx0 : Ideal.span {-(Jq E ω hω q hq0 hqp hq6)} ≠ ⊥ := by
    rw [Ideal.span_singleton_neg, hspan]
    exact hq0
  have hred : red3 E (-(Jq E ω hω q hq0 hqp hq6)) = 1 := by
    rw [map_neg, red3_Jq]
    simp
  have hx3unit : IsUnit (red3 E (-(Jq E ω hω q hq0 hqp hq6))) := by
    rw [hred]
    exact isUnit_one
  have hred3eq : red3 E (-(Jq E ω hω q hq0 hqp hq6)) =
      red3 E (primaryGenerator E (q3 E q hq0 hq6)) := by
    rw [hred, red3_primaryGenerator]
  exact neg_eq_iff_eq_neg.mp (eq_of_span_eq_of_red3_eq E (-(Jq E ω hω q hq0 hqp hq6))
    (primaryGenerator E (q3 E q hq0 hq6)) hxy hx0 hx3unit hred3eq)

theorem jacobiSum_ρqC_eq_neg_primaryGenerator (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (ι : E →+* ℂ) (q : Ideal (R E)) (hq0 : q ≠ ⊥) (hqp : q.IsPrime)
    (hq6 : q ⊔ Ideal.span {(6 : R E)} = ⊤) :
    letI := residueFintype E q hq0
    jacobiSum (ρqC E ω hω ι q hq0 hqp hq6) (ρqC E ω hω ι q hq0 hqp hq6) =
      -ιR E ι (primaryGenerator E (q3 E q hq0 hq6)) := by
  letI := residueFintype E q hq0
  have h := jacobiSum_ringHomComp (ρq E ω hω q hq0 hqp hq6) (ρq E ω hω q hq0 hqp hq6)
    (ιR E ι)
  simp only [ρqC]
  rw [h, show jacobiSum (ρq E ω hω q hq0 hqp hq6) (ρq E ω hω q hq0 hqp hq6) =
      Jq E ω hω q hq0 hqp hq6 from rfl,
    Jq_eq_neg_primaryGenerator E ω hω q hq0 hqp hq6]
  simp

end DedekindZetaZeroFree.Eisenstein

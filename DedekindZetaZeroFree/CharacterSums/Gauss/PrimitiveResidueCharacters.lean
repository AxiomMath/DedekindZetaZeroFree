module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree

open scoped Classical

def IsPrimitiveResidueCharacter {A : Type*} [CommRing A]
    (χ : MulChar A ℂ) : Prop :=
  ∀ n : A, ¬ IsUnit n →
    ∃ a : Aˣ, χ (a : A) ≠ 1 ∧ n * ((a : A) - 1) = 0

def IsOrthogonalResidueAddChar {A : Type*} [CommRing A] [Fintype A]
    (ψ : AddChar A ℂ) : Prop :=
  ∀ n : A, n ≠ 0 → ∑ d : A, ψ (n * d) = 0

private lemma residue_shifted {A : Type*} [CommRing A] [Fintype A]
    (χ : MulChar A ℂ) (ψ : AddChar A ℂ)
    (hp : IsPrimitiveResidueCharacter χ) (n : A) :
    gaussSum χ⁻¹ (ψ.mulShift n) = χ n * gaussSum χ⁻¹ ψ := by
  by_cases hn : IsUnit n
  · simpa using gaussSum_mulShift_eq χ⁻¹ ψ hn.unit
  · obtain ⟨a, ha, hna⟩ := hp n hn
    have hna' : n * (a : A) = n := by linear_combination hna
    have hs : (ψ.mulShift n).mulShift (a : A) = ψ.mulShift n := by
      rw [AddChar.mulShift_mulShift, hna']
    have he := gaussSum_mulShift χ⁻¹ (ψ.mulShift n) a
    rw [hs] at he
    have hi : χ⁻¹ (a : A) ≠ 1 := by
      simpa [MulChar.inv_apply_eq_inv'] using ha
    rw [MulChar.map_nonunit χ hn, zero_mul]
    exact eq_zero_of_mul_eq_self_left hi he

private lemma residue_inversion {A : Type*} [CommRing A] [Fintype A]
    (χ : MulChar A ℂ) (ψ : AddChar A ℂ)
    (ho : IsOrthogonalResidueAddChar ψ) :
    (∑ n : A, gaussSum χ⁻¹ (ψ.mulShift n) * ψ (-n)) = (Fintype.card A : ℂ) := by
  simp only [gaussSum, AddChar.mulShift_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← AddChar.map_add_eq_mul]
  simp only [← sub_eq_add_neg, ← mul_sub_one]
  have hor (d : A) : (∑ n : A, ψ (n * (d - 1))) =
      if d = 1 then (Fintype.card A : ℂ) else 0 := by
    split_ifs with hd
    · simp [hd]
    · simpa [mul_comm] using ho (d - 1) (sub_ne_zero.mpr hd)
  simp_rw [← Finset.mul_sum, hor]
  simp

private lemma residue_unit_sum {A : Type*} [CommRing A] [Fintype A]
    (χ : MulChar A ℂ) (ψ : AddChar A ℂ) (n : A) :
    (∑ d : Aˣ, χ⁻¹ (d : A) * ψ (n * (d : A))) =
      gaussSum χ⁻¹ (ψ.mulShift n) := by
  apply Fintype.sum_of_injective Units.val Units.val_injective
  · intro d hd
    have hnu : ¬ IsUnit d := by
      rintro ⟨u, rfl⟩
      exact hd ⟨u, rfl⟩
    simp [MulChar.map_nonunit _ hnu]
  · intro d
    rfl

theorem detector_gauss_residue
    (A : Type*) [CommRing A] [Fintype A]
    (χ : MulChar A ℂ) (ψ : AddChar A ℂ)
    (hprimitive : IsPrimitiveResidueCharacter χ)
    (horthogonal : IsOrthogonalResidueAddChar ψ) :
    ‖gaussSum χ⁻¹ ψ‖ ^ 2 = (Fintype.card A : ℝ) ∧
      (∀ n : A, χ n = (gaussSum χ⁻¹ ψ)⁻¹ *
        ∑ d : Aˣ, χ⁻¹ (d : A) * ψ (n * (d : A))) ∧
      (∀ n : A, ¬ IsUnit n →
        (gaussSum χ⁻¹ ψ)⁻¹ *
          (∑ d : Aˣ, χ⁻¹ (d : A) * ψ (n * (d : A))) = 0) := by
  have hprod : gaussSum χ⁻¹ ψ * star (gaussSum χ⁻¹ ψ) = (Fintype.card A : ℂ) := by
    have hi := residue_inversion χ ψ horthogonal
    simp_rw [residue_shifted χ ψ hprimitive] at hi
    simp only [mul_comm (χ _) (gaussSum χ⁻¹ ψ), mul_assoc] at hi
    rw [← Finset.mul_sum] at hi
    rw [star_gaussSum_eq, inv_inv]
    simpa only [gaussSum, AddChar.inv_apply] using hi
  have hnorm : ‖gaussSum χ⁻¹ ψ‖ ^ 2 = (Fintype.card A : ℝ) := by
    have hr := congrArg Complex.re hprod
    simpa only [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow,
      Complex.ofReal_re, Complex.natCast_re] using hr
  have hnz : gaussSum χ⁻¹ ψ ≠ 0 := by
    intro hz
    have hc : (Fintype.card A : ℝ) > 0 := by exact_mod_cast Fintype.card_pos
    rw [hz, norm_zero, zero_pow (by decide)] at hnorm
    linarith
  refine ⟨hnorm, ?_, ?_⟩
  · intro n
    rw [residue_unit_sum, residue_shifted χ ψ hprimitive, mul_left_comm, inv_mul_cancel₀ hnz, mul_one]
  · intro n hn
    rw [residue_unit_sum, residue_shifted χ ψ hprimitive, MulChar.map_nonunit χ hn, zero_mul, mul_zero]

end DedekindZetaZeroFree

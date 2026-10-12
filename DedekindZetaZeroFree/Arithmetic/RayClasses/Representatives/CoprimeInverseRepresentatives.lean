module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.TotallyPositiveCoprimeRepresentatives

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem exists_ray_inverse_coprime (F : Type) [Field F] [NumberField F]
    (m q I : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hq : q ≠ ⊥) (hI : I ≠ ⊥)
    (hIm : I ⊔ m = ⊤) :
    ∃ (J : Ideal (𝓞 F)) (a : 𝓞 F),
      J ≠ ⊥ ∧ J ⊔ (m * q) = ⊤ ∧ a ≠ 0 ∧ a - 1 ∈ m ∧
        (∀ φ : F →+* ℝ, 0 < φ (a : F)) ∧ I * J = Ideal.span {a} := by
  classical
  set r : Ideal (𝓞 F) := I * (m * q) with hrdef
  have hr : r ≠ ⊥ := by
    rw [hrdef]; exact mul_ne_zero hI (mul_ne_zero hm hq)
  have hrI : r ≤ I := by
    rw [hrdef]
    calc I * (m * q) ≤ I * ⊤ := Ideal.mul_mono_right le_top
      _ = I := Ideal.mul_top I
  have hrm : r ≤ m := by
    rw [hrdef]; exact le_trans Ideal.mul_le_right Ideal.mul_le_left

  obtain ⟨b0, hb0⟩ := IsDedekindDomain.exists_sup_span_eq hrI hr

  obtain ⟨b, hbne, hbsub, hbpos⟩ := exists_totallyPositive_residue F r hr b0
  have hb0I : b0 ∈ I := by
    rw [← hb0]
    exact (le_sup_right : Ideal.span {b0} ≤ r ⊔ Ideal.span {b0}) (Ideal.mem_span_singleton_self b0)
  have hbI : b ∈ I := by
    have hb' : b - b0 ∈ I := hrI hbsub
    have : b = b0 + (b - b0) := by ring
    rw [this]; exact Ideal.add_mem I hb0I hb'
  have hspanb_le : Ideal.span {b} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hbI
  obtain ⟨J0, hJ0⟩ := (Ideal.dvd_iff_le.mpr hspanb_le : I ∣ Ideal.span {b})
  have hJ0ne : J0 ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot] at hJ0
    exact hbne (Ideal.span_singleton_eq_bot.mp hJ0)
  have hsup_br : Ideal.span {b} ⊔ r = I := by
    refine le_antisymm (sup_le hspanb_le hrI) ?_
    rw [← hb0]
    refine sup_le le_sup_right ?_
    rw [Ideal.span_singleton_le_iff_mem]
    have h1 : b ∈ Ideal.span {b} ⊔ r := Submodule.mem_sup_left (Ideal.mem_span_singleton_self b)
    have h2 : b - b0 ∈ Ideal.span {b} ⊔ r := Submodule.mem_sup_right hbsub
    have : b0 = b - (b - b0) := by ring
    rw [this]; exact sub_mem h1 h2
  have hJ0sup : J0 ⊔ (m * q) = ⊤ := by
    have h : I * (J0 ⊔ m * q) = I * ⊤ := by
      rw [Ideal.mul_sup, ← hJ0, ← hrdef, Ideal.mul_top, hsup_br]
    exact mul_left_cancel₀ hI h
  have hspanb_m : Ideal.span {b} ⊔ m = ⊤ := by
    have hle : I ≤ Ideal.span {b} ⊔ m := by
      rw [← hb0]
      refine sup_le ?_ ?_
      · exact le_trans hrm le_sup_right
      · rw [Ideal.span_singleton_le_iff_mem]
        have h1 : b ∈ Ideal.span {b} ⊔ m := Submodule.mem_sup_left (Ideal.mem_span_singleton_self b)
        have h2 : b - b0 ∈ Ideal.span {b} ⊔ m := Submodule.mem_sup_right (hrm hbsub)
        have : b0 = b - (b - b0) := by ring
        rw [this]; exact sub_mem h1 h2
    rw [eq_top_iff]
    calc ⊤ = I ⊔ m := hIm.symm
      _ ≤ (Ideal.span {b} ⊔ m) ⊔ m := sup_le_sup_right hle m
      _ = Ideal.span {b} ⊔ m := by rw [sup_assoc, sup_idem]

  obtain ⟨x, hx, y, hy, hxy⟩ :=
    Ideal.isCoprime_iff_exists.mp (Ideal.isCoprime_iff_sup_eq.mpr hspanb_m)
  obtain ⟨u0, rfl⟩ := Ideal.mem_span_singleton.mp hx
  have hbu0 : b * u0 - 1 ∈ m := by
    have : b * u0 - 1 = -y := by linear_combination hxy
    rw [this]; exact neg_mem hy
  have hspanu0 : Ideal.span {u0} ⊔ m = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq]
    refine Ideal.coprime_of_no_prime_ge ?_
    intro P hle1 hle2 hP
    have hu0P : u0 ∈ P := hle1 (Ideal.mem_span_singleton_self u0)
    have hbu0P : b * u0 ∈ P := Ideal.mul_mem_left P b hu0P
    have hsubP : b * u0 - 1 ∈ P := hle2 hbu0
    have hone : (1 : 𝓞 F) ∈ P := by
      have : b * u0 - (b * u0 - 1) = 1 := by ring
      rw [← this]; exact sub_mem hbu0P hsubP
    exact hP.ne_top (Ideal.eq_top_iff_one P |>.mpr hone)

  obtain ⟨u, hune, husub, husup, hupos⟩ :=
    exists_totallyPositive_coprime_residue F m q hm hq u0 hspanu0
  refine ⟨J0 * Ideal.span {u}, b * u, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_ne_zero hJ0ne (by
      intro h; exact hune (Ideal.span_singleton_eq_bot.mp h))
  · have h1 : IsCoprime J0 (m * q) := Ideal.isCoprime_iff_sup_eq.mpr hJ0sup
    have h2 : IsCoprime (Ideal.span {u}) (m * q) := Ideal.isCoprime_iff_sup_eq.mpr husup
    exact (h1.mul_left h2).sup_eq
  · exact mul_ne_zero hbne hune
  · have h1 : b * u - b * u0 ∈ m := by
      rw [← mul_sub]; exact Ideal.mul_mem_left m b husub
    have : b * u - 1 = (b * u - b * u0) + (b * u0 - 1) := by ring
    rw [this]; exact Ideal.add_mem m h1 hbu0
  · intro φ
    have : ((b * u : 𝓞 F) : F) = (b : F) * (u : F) := by push_cast; ring
    rw [this, map_mul]
    exact mul_pos (hbpos φ) (hupos φ)
  · rw [← mul_assoc, ← hJ0, Ideal.span_singleton_mul_span_singleton]

end DedekindZetaZeroFree.LargeSieve

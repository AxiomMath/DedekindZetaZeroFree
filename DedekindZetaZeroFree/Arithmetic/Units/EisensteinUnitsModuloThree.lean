module

public import DedekindZetaZeroFree.Arithmetic.Ideals.EisensteinIntegers.PrimaryIdealDomain

@[expose] public section

namespace DedekindZetaZeroFree.Eisenstein

open IsCyclotomicExtension.Rat.Three
private lemma lambda_sq_aux (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3) :
    «λ» E ω hω ^ 2 = -(3 : R E) * η E ω hω := by
  have h := eta_sq_add_eta_add_one hω
  change (η E ω hω)^2 + η E ω hω + 1 = 0 at h
  dsimp [«λ»]
  linear_combination h

private lemma lambda_not_dvd_one (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3) :
    ¬ «λ» E ω hω ∣ 1 := by
  intro h
  have hn := map_dvd (Algebra.norm ℤ) h
  rw [hω.norm_toInteger_sub_one_of_prime_ne_two' (by decide), map_one] at hn
  norm_num at hn

private lemma lambda_not_dvd_two (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3) :
    ¬ «λ» E ω hω ∣ (2 : R E) := by
  intro h
  have hn := map_dvd (Algebra.norm ℤ) h
  rw [hω.norm_toInteger_sub_one_of_prime_ne_two' (by decide)] at hn
  have hnorm : Algebra.norm ℤ (2 : R E) = (2 : ℤ) ^ Module.finrank ℤ (R E) := by
    simpa using (Algebra.norm_algebraMap (R := ℤ) (S := R E) 2)
  rw [hnorm] at hn
  have hp : Prime (3 : ℤ) := by decide
  have := hp.dvd_of_dvd_pow hn
  norm_num at this

private lemma red3_eq_of_lambda_sq_dvd (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (x y : R E) (h : «λ» E ω hω ^ 2 ∣ x - y) : red3 E x = red3 E y := by
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  apply dvd_trans (b := «λ» E ω hω ^ 2) _ h
  rw [lambda_sq_aux]
  exact dvd_mul_of_dvd_left (dvd_neg.mpr dvd_rfl) _

private lemma lambda_sq_dvd_three (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3) :
    «λ» E ω hω ^ 2 ∣ (3 : R E) := by
  rw [lambda_sq_aux]
  have hu := hω.toInteger_isPrimitiveRoot.isUnit (by decide : 3 ≠ 0)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine ⟨-v, ?_⟩
  change 3 = -3 * hω.toInteger * -v
  calc
    (3 : R E) = 3 * (hω.toInteger * v) := by rw [hv, mul_one]
    _ = -3 * hω.toInteger * -v := by ring

private lemma exists_unit_residue (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ω : E) (hω : IsPrimitiveRoot ω 3)
    (x : R E) (hx : «λ» E ω hω ∣ x - 1) :
    ∃ u : (R E)ˣ, red3 E (u : R E) = red3 E x := by
  let e : (R E)ˣ := (hω.toInteger_isPrimitiveRoot.isUnit (by decide : 3 ≠ 0)).unit
  have he : (e : R E) = η E ω hω := rfl
  obtain ⟨b, hb⟩ := hx
  rcases lambda_dvd_or_dvd_sub_one_or_dvd_add_one hω b with h | h | h
  · refine ⟨1, ?_⟩
    symm
    apply red3_eq_of_lambda_sq_dvd E ω hω
    change «λ» E ω hω ^ 2 ∣ x - 1
    rw [hb, pow_two]
    exact mul_dvd_mul_left _ h
  · refine ⟨e, ?_⟩
    rw [he]
    symm
    apply red3_eq_of_lambda_sq_dvd E ω hω
    have hx : x - η E ω hω = «λ» E ω hω * (b - 1) := by
      dsimp [«λ»] at hb ⊢
      linear_combination hb
    rw [hx, pow_two]
    exact mul_dvd_mul_left _ h
  · refine ⟨e ^ 2, ?_⟩
    simp only [Units.val_pow_eq_pow_val, he]
    symm
    apply red3_eq_of_lambda_sq_dvd E ω hω
    have hs := eta_sq hω
    change (η E ω hω)^2 = -η E ω hω - 1 at hs
    have hx : x - η E ω hω ^ 2 = 3 + «λ» E ω hω * (b + 1) := by
      dsimp [«λ»] at hb ⊢
      linear_combination hb - hs
    rw [hx]
    exact dvd_add (lambda_sq_dvd_three E ω hω)
      (by simpa [pow_two] using mul_dvd_mul_left («λ» E ω hω) h)

private lemma lift_unit_residue (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (x : R E) (hx : IsUnit (red3 E x)) :
    ∃ u : (R E)ˣ, red3 E (u : R E) = red3 E x := by
  obtain ⟨ω, hω⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ E
    (Set.mem_singleton 3) (by decide : 3 ≠ 0)
  have hnot : ¬ «λ» E ω hω ∣ x := by
    intro h
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hzmem : x * z - 1 ∈ m3 E := by
      apply Ideal.Quotient.eq.mp
      simpa only [map_mul, map_one] using hy
    have hz : (3 : R E) ∣ x * z - 1 := Ideal.mem_span_singleton.mp hzmem
    have hd := dvd_trans hω.toInteger_sub_one_dvd_prime' hz
    exact lambda_not_dvd_one E ω hω
      (by convert dvd_sub (dvd_mul_of_dvd_left h z) hd using 1; ring)
  rcases lambda_dvd_or_dvd_sub_one_or_dvd_add_one hω x with h | h | h
  · contradiction
  · exact exists_unit_residue E ω hω x h
  · have hneg : «λ» E ω hω ∣ -x - 1 := by
      simpa only [neg_add_rev, sub_eq_add_neg, add_comm] using h.neg_right
    obtain ⟨u, hu⟩ := exists_unit_residue E ω hω (-x) hneg
    refine ⟨-u, ?_⟩
    simpa using congrArg Neg.neg hu

private lemma kernel_trivial (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (u : (R E)ˣ)
    (hu : red3 E (u : R E) = 1) : u = 1 := by
  obtain ⟨ω, hω⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ E
    (Set.mem_singleton 3) (by decide : 3 ≠ 0)
  have hdmem : (u : R E) - 1 ∈ m3 E := by
    apply Ideal.Quotient.eq.mp
    simpa only [map_one] using hu
  have hd : (3 : R E) ∣ (u : R E) - 1 := Ideal.mem_span_singleton.mp hdmem
  have hsq := dvd_trans (lambda_sq_dvd_three E ω hω) hd
  rcases eq_one_or_neg_one_of_unit_of_congruent hω u ⟨1, by simpa using hsq⟩ with h | h
  · exact h
  · exfalso
    have hd' : «λ» E ω hω ∣ (2 : R E) := by
      have := dvd_trans hω.toInteger_sub_one_dvd_prime' hd
      rw [h, Units.val_neg, Units.val_one] at this
      convert this.neg_right using 1 <;> ring
    exact lambda_not_dvd_two E ω hω hd'

theorem red3_units_bijective (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] :
    Function.Bijective (Units.map (red3 E).toMonoidHom) := by
  constructor
  · intro u v huv
    have hk : red3 E ((u * v⁻¹ : (R E)ˣ) : R E) = 1 := by
      have hm := congrArg Units.val huv
      change red3 E (u : R E) = red3 E (v : R E) at hm
      simp only [Units.val_mul, map_mul, hm]
      exact (Units.map (red3 E).toMonoidHom v).mul_inv
    have := kernel_trivial E (u * v⁻¹) hk
    exact mul_inv_eq_one.mp this
  · intro v
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (v : R E ⧸ m3 E)
    have hunit : IsUnit (red3 E x) := by rw [hx]; exact v.isUnit
    obtain ⟨u, hu⟩ := lift_unit_residue E x hunit
    exact ⟨u, Units.ext (hu.trans hx)⟩

theorem existsUnique_unit_mul_red3_eq_one (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (x : R E) (hx : IsUnit (red3 E x)) :
    ∃! u : (R E)ˣ, red3 E ((u : R E) * x) = 1 := by
  classical
  let v := hx.unit
  obtain ⟨u, hu⟩ := (red3_units_bijective E).surjective v⁻¹
  refine ⟨u, ?_, ?_⟩
  · have hv := congrArg Units.val hu
    change red3 E ((u : R E) * x) = 1
    change red3 E (u : R E) = (↑v⁻¹ : R E ⧸ m3 E) at hv
    rw [map_mul, hv, ← hx.unit_spec]
    exact Units.inv_mul v
  · intro u' hu'
    apply (red3_units_bijective E).injective
    apply Units.ext
    have : red3 E (u' : R E) * (v : R E ⧸ m3 E) = 1 := by
      simpa [v] using hu'
    have h' : red3 E (u' : R E) = (v⁻¹ : (R E ⧸ m3 E)ˣ) := by
      simpa [mul_assoc] using congrArg (fun y : R E ⧸ m3 E => y * (↑v⁻¹ : R E ⧸ m3 E)) this
    exact h'.trans (congrArg Units.val hu).symm

theorem unit_eq_one_of_red3_eq_one (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (u : (R E)ˣ)
    (hu : red3 E (u : R E) = 1) : u = 1 := by
  apply (red3_units_bijective E).injective
  apply Units.ext
  simpa using hu

theorem isUnit_red3_iff_span_sup_m3_eq_top (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (x : R E) :
    IsUnit (red3 E x) ↔ Ideal.span {x} ⊔ m3 E = ⊤ := by
  rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_iff_exists]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hz : x * z - 1 ∈ m3 E := by
      apply Ideal.Quotient.eq.mp
      simpa only [map_mul, map_one] using hy
    refine ⟨x * z, Ideal.mem_span_singleton.mpr (dvd_mul_right x z),
      -(x * z - 1), (m3 E).neg_mem hz, ?_⟩
    ring
  · rintro ⟨a, ha, b, hb, hab⟩
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp ha
    apply IsUnit.of_mul_eq_one (red3 E z)
    have h := congrArg (red3 E) hab
    simpa only [map_add, map_mul, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr hb,
      add_zero] using h

end DedekindZetaZeroFree.Eisenstein

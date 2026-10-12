module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.SevenTermApproximation

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirectDictionary
variable {F : Type} [Field F] [NumberField F]
private lemma rel {a b : Ideal (𝓞 F)} (h : a ⊔ b = ⊤) : IsRelPrime a b := by
  intro z hza hzb
  rw [Ideal.isUnit_iff]
  exact le_antisymm le_top (h ▸ sup_le (Ideal.dvd_iff_le.mp hza) (Ideal.dvd_iff_le.mp hzb))

open UniqueFactorizationMonoid

private lemma ideal_radical_eq (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) :
    q.radical = UniqueFactorizationMonoid.radical q := by
  let r := UniqueFactorizationMonoid.radical q
  have hr : r ≠ ⊥ := radical_ne_zero
  have hsf : Squarefree r := squarefree_radical
  obtain ⟨hp, hprod, _, _, _, _⟩ := Vendor.CutoffDifference.squarefree_divisor_dictionary r hr hsf
  let P := (factors r).toFinset
  have heq : P.inf (fun p => p) = r := by
    have h := IsDedekindDomain.inf_prime_pow_eq_prod P (fun p => p) (fun _ => 1)
      hp (by intro i hi j hj hij; exact hij)
    calc
      P.inf (fun p => p) = ∏ p ∈ P, p := by simpa only [pow_one] using h
      _ = r := hprod
  have hgen : ∀ S : Finset (Ideal (𝓞 F)), (∀ p ∈ S, Prime p) →
      (S.inf (fun p => p)).IsRadical := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [Ideal.IsRadical]
    | insert p S hnot ih =>
      intro hpr
      rw [Finset.inf_insert]
      apply Ideal.IsRadical.inf
      · exact (Ideal.isPrime_of_prime (hpr p (by simp))).isRadical
      · exact ih (by intro t ht; exact hpr t (by simp [ht]))
  have hR : r.IsRadical := heq ▸ hgen P hp
  apply le_antisymm
  · exact (hR.radical_le_iff).mpr (Ideal.dvd_iff_le.mp radical_dvd_self)
  · obtain ⟨n, hn⟩ := exists_dvd_radical_self_pow hq
    have hle : r ^ n ≤ q := Ideal.dvd_iff_le.mp hn
    have : r ≤ (r ^ n).radical := by
      intro x hx
      exact ⟨n, Ideal.pow_mem_pow hx n⟩
    exact this.trans (Ideal.radical_mono hle)

lemma sum_divisors_mul (a b : Ideal (𝓞 F)) (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (hab : a ⊔ b = ⊤) (H : Ideal (𝓞 F) → ℂ) :
    ∑ f ∈ idealDivisors (a * b), H f =
      ∑ x ∈ idealDivisors a, ∑ y ∈ idealDivisors b, H (x * y) := by
  have h0 : a * b ≠ ⊥ := mul_ne_zero ha hb
  have heq : idealDivisors (a * b) =
      ((idealDivisors a) ×ˢ (idealDivisors b)).image (fun p => p.1 * p.2) := by
    ext f
    simp only [mem_idealDivisors h0, Finset.mem_image, Finset.mem_product]
    constructor
    · intro hf
      obtain ⟨x, y, hx, hy, hxy⟩ := exists_dvd_and_dvd_of_dvd_mul hf
      exact ⟨(x,y), ⟨(mem_idealDivisors ha).mpr hx, (mem_idealDivisors hb).mpr hy⟩, hxy.symm⟩
    · rintro ⟨⟨x,y⟩, ⟨hx,hy⟩, rfl⟩
      exact mul_dvd_mul ((mem_idealDivisors ha).mp hx) ((mem_idealDivisors hb).mp hy)
  rw [heq, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro p hp q hq hpq
    obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hq1,hq2⟩ := Finset.mem_product.mp hq
    have px := (mem_idealDivisors ha).mp hp1
    have py := (mem_idealDivisors hb).mp hp2
    have qx := (mem_idealDivisors ha).mp hq1
    have qy := (mem_idealDivisors hb).mp hq2
    have hpqrel : IsRelPrime p.1 q.2 := ((rel hab).of_dvd_left px).of_dvd_right qy
    have hqprel : IsRelPrime q.1 p.2 := ((rel hab).of_dvd_left qx).of_dvd_right py
    change p.1 * p.2 = q.1 * q.2 at hpq
    have hp1q1 : p.1 ∣ q.1 := hpqrel.dvd_of_dvd_mul_right (hpq ▸ dvd_mul_right p.1 p.2)
    have hq1p1 : q.1 ∣ p.1 := hqprel.dvd_of_dvd_mul_right (hpq.symm ▸ dvd_mul_right q.1 q.2)
    have hp1eq : p.1 = q.1 := le_antisymm (Ideal.dvd_iff_le.mp hq1p1) (Ideal.dvd_iff_le.mp hp1q1)
    apply Prod.ext hp1eq
    exact mul_left_cancel₀ (ne_bot_of_mem_idealDivisors hp1) (by simpa [hp1eq] using hpq)

lemma sum_moebius_radical (a : Ideal (𝓞 F)) (ha : a ≠ ⊥)
    (H : Ideal (𝓞 F) → ℂ) :
    ∑ f ∈ idealDivisors a, (moebius f : ℂ) * H f =
      ∑ f ∈ idealDivisors a.radical, (moebius f : ℂ) * H f := by
  have hrad : a.radical = UniqueFactorizationMonoid.radical a := ideal_radical_eq a ha
  have hr0 : a.radical ≠ ⊥ := by rw [hrad]; exact radical_ne_zero
  have hsub : idealDivisors a.radical ⊆ idealDivisors a := by
    intro f hf
    apply (mem_idealDivisors ha).mpr
    exact ((mem_idealDivisors hr0).mp hf).trans (by rw [hrad]; exact radical_dvd_self)
  symm
  apply Finset.sum_subset hsub
  intro f hf hnot
  have hnsf : ¬Squarefree f := by
    intro hsf
    apply hnot
    apply (mem_idealDivisors hr0).mpr
    rw [hrad, UniqueFactorizationMonoid.dvd_radical_iff hsf.isRadical ha]
    exact (mem_idealDivisors ha).mp hf
  simp [moebius_of_not_squarefree hnsf]

lemma largeDensity_triple {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
    (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F))
    (hp : C.ValidPair p) (Z : ℝ) :
    Context.largeDensity ((c * C.d) * (p.1 * p.2)) Z =
      ∑ f₀ ∈ C.mobiusDivisors, ∑ f₁ ∈ idealDivisors p.1,
        ∑ f₂ ∈ idealDivisors p.2,
          if Z < norm (f₀ * (f₁ * f₂)) then
            (moebius f₀ : ℂ) * (moebius f₁ : ℂ) * (moebius f₂ : ℂ) /
              ((norm f₀ : ℂ) * (norm f₁ : ℂ) * (norm f₂ : ℂ))
          else 0 := by
  have hcd0 : c * C.d ≠ ⊥ := mul_ne_zero C.D.original_ne_bot C.hd0
  have huv0 : p.1 * p.2 ≠ ⊥ := mul_ne_zero hp.hu0 hp.hv0
  have hcuv : c ⊔ (p.1 * p.2) = ⊤ := by
    rw [Ideal.sup_mul_eq_of_coprime_left (by simpa [sup_comm] using hp.huc)]
    simpa [sup_comm] using hp.hvc
  have hfixed : (c * C.d) ⊔ (p.1 * p.2) = ⊤ := by
    rw [sup_comm, Ideal.sup_mul_eq_of_coprime_left (by simpa [sup_comm] using hcuv)]
    simpa [sup_comm] using hp.hduv
  unfold Context.largeDensity
  rw [Finset.sum_filter, sum_divisors_mul _ _ hcd0 huv0 hfixed]
  simp_rw [sum_divisors_mul _ _ hp.hu0 hp.hv0 hp.huv]
  have hfrel : ∀ f₀ ∈ idealDivisors (c * C.d), ∀ f₁ ∈ idealDivisors p.1,
      ∀ f₂ ∈ idealDivisors p.2,
      moebius (f₀ * (f₁ * f₂)) = moebius f₀ * moebius f₁ * moebius f₂ := by
    intro f₀ hf₀ f₁ hf₁ f₂ hf₂
    have hd₀ := (mem_idealDivisors hcd0).mp hf₀
    have hd₁ := (mem_idealDivisors hp.hu0).mp hf₁
    have hd₂ := (mem_idealDivisors hp.hv0).mp hf₂
    rw [((rel hfixed).of_dvd_left hd₀ |>.of_dvd_right (mul_dvd_mul hd₁ hd₂)).moebius_mul,
      ((rel hp.huv).of_dvd_left hd₁ |>.of_dvd_right hd₂).moebius_mul]
    ring
  have hterm : ∀ f₀ ∈ idealDivisors (c * C.d),
      (∑ f₁ ∈ idealDivisors p.1, ∑ f₂ ∈ idealDivisors p.2,
        if Z < norm (f₀ * (f₁ * f₂)) then
          (moebius (f₀ * (f₁ * f₂)) : ℂ) / (norm (f₀ * (f₁ * f₂)) : ℂ) else 0) =
      (moebius f₀ : ℂ) *
        (∑ f₁ ∈ idealDivisors p.1, ∑ f₂ ∈ idealDivisors p.2,
          if Z < norm (f₀ * (f₁ * f₂)) then
            (moebius f₁ : ℂ) * (moebius f₂ : ℂ) /
              ((norm f₀ : ℂ) * (norm f₁ : ℂ) * (norm f₂ : ℂ)) else 0) := by
    intro f₀ hf₀
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f₁ hf₁
    apply Finset.sum_congr rfl
    intro f₂ hf₂
    split_ifs <;> simp [hfrel f₀ hf₀ f₁ hf₁ f₂ hf₂, ExplicitTerms.norm, map_mul, mul_inv_rev] <;> ring
  rw [Finset.sum_congr rfl hterm, sum_moebius_radical _ hcd0]
  unfold Context.mobiusDivisors
  apply Finset.sum_congr rfl
  intro f₀ hf₀
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f₁ hf₁
  apply Finset.sum_congr rfl
  intro f₂ hf₂
  split_ifs <;> ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirectDictionary

end

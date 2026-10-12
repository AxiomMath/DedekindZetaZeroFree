module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.PrimeToFractionalIdealRatios
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.PositiveChineseRemainder
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.LocalCongruenceAndPositivity

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

private theorem sup_eq_top_of_forall_count_zero
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      v ∈ (fullModulus m hm).finitePart.support →
      FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0) :
    I ⊔ m = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal (I ⊔ m) hne
  have hPprime : P.IsPrime := hPmax.isPrime
  have hPne : P ≠ ⊥ := by
    intro hbot
    exact hI (le_bot_iff.mp (le_trans le_sup_left (hbot ▸ hle)))
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨P, hPprime, hPne⟩
  have hPI : v.asIdeal ∣ I := Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle)
  have hPm : v.asIdeal ∣ m := Ideal.dvd_iff_le.mpr (le_trans le_sup_right hle)
  have hmem : v ∈ (fullModulus m hm).finitePart.support := by
    rw [Finsupp.mem_support_iff, fullModulus_finitePart]
    intro hzero
    exact (Associates.count_ne_zero_iff_dvd hm v.irreducible).mpr hPm hzero
  have hcount := h v hmem
  rw [FractionalIdeal.count_coe F v hI] at hcount
  exact (Associates.count_ne_zero_iff_dvd hI v.irreducible).mpr hPI (Nat.cast_eq_zero.mp hcount)

theorem exists_mixed_integral_generator
    (m f : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hf : f ≠ ⊥) (hmf : m ≤ f)
    (x : Fˣ) (hx : ClassFieldTheory.IsRayCongruent (fullModulus f hf) x)
    (hprime : toPrincipalIdeal (𝓞 F) F x ∈
      ClassFieldTheory.rayClassPrimeToIdeals (fullModulus m hm)) :
    ∃ a b : 𝓞 F,
      a ≠ 0 ∧ b ≠ 0 ∧ (a : F) = (x : F) * (b : F) ∧
      a - 1 ∈ f ∧ b - 1 ∈ f ∧
      (∀ φ : F →+* ℝ, 0 < φ (a : F)) ∧
      (∀ φ : F →+* ℝ, 0 < φ (b : F)) ∧
      Ideal.span {a} ⊔ m = ⊤ ∧ Ideal.span {b} ⊔ m = ⊤ := by
  classical
  obtain ⟨A, B, hA, hB, hAcop, hBcop, hJ⟩ :=
    exists_integralIdealUnit_ratio m hm ⟨toPrincipalIdeal (𝓞 F) F x, hprime⟩
  obtain ⟨b, hb0, hbB, hb1m, hbpos⟩ := exists_positive_mem_congruent_one m hm B hB hBcop

  have hJunit : toPrincipalIdeal (𝓞 F) F x =
      integralIdealUnit A hA * (integralIdealUnit B hB)⁻¹ := hJ
  have hcalc : toPrincipalIdeal (𝓞 F) F x * integralIdealUnit B hB = integralIdealUnit A hA := by
    rw [hJunit, mul_assoc, inv_mul_cancel, mul_one]
  have hval' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F) *
      (B : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (A : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    have hh := congr_arg Units.val hcalc
    simpa [integralIdealUnit, coe_toPrincipalIdeal, Units.val_mul] using hh

  have hspanb : (Ideal.span {b} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F) := by
    rw [FractionalIdeal.coeIdeal_span_singleton]
  have hb_le_B : (Ideal.span {b} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≤
      (B : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
    (FractionalIdeal.coeIdeal_le_coeIdeal F).mpr ((Ideal.span_singleton_le_iff_mem (I := B)).mpr hbB)

  have hkey : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((x : F) * (b : F)) ≤
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F)
        = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F) *
            (Ideal.span {b} : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by rw [hspanb]
      _ ≤ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F) *
            (B : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by gcongr
      _ = (A : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hval'
      _ ≤ 1 := FractionalIdeal.coeIdeal_le_one
  have hmem : ((x : F) * (b : F)) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
    FractionalIdeal.spanSingleton_le_iff_mem.mp hkey
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff (nonZeroDivisors (𝓞 F))).mp hmem

  have hxF : (x : F) ≠ 0 := Units.ne_zero x
  have hbF : (b : F) ≠ 0 := fun h => hb0 (FaithfulSMul.algebraMap_injective (𝓞 F) F h)
  have ha0 : a ≠ 0 := by
    intro hzero
    have : (x : F) * (b : F) = 0 := by rw [← ha, hzero, map_zero]
    exact mul_ne_zero hxF hbF this

  have hposx : ∀ φ : F →+* ℝ, 0 < φ (x : F) := ray_congruent_pos f hf x hx
  have hapos : ∀ φ : F →+* ℝ, 0 < φ (a : F) := by
    intro φ
    have h1 : (a : F) = (x : F) * (b : F) := ha
    rw [h1, map_mul]
    exact mul_pos (hposx φ) (hbpos φ)

  have hsub : a - b ∈ f := ray_congruent_sub_mem f hf x hx a b ha
  have hb1f : b - 1 ∈ f := hmf hb1m
  have ha1f : a - 1 ∈ f := by
    have heq : a - 1 = (a - b) + (b - 1) := by ring
    rw [heq]
    exact f.add_mem hsub hb1f

  have hspanb_cop : Ideal.span {b} ⊔ m = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have hb_in : b ∈ Ideal.span {b} ⊔ m := Submodule.mem_sup_left (Ideal.mem_span_singleton_self b)
    have hb1_in : b - 1 ∈ Ideal.span {b} ⊔ m := Submodule.mem_sup_right hb1m
    have hthis : b - (b - 1) ∈ Ideal.span {b} ⊔ m := sub_mem hb_in hb1_in
    have h1eq : b - (b - 1) = (1 : 𝓞 F) := by ring
    rwa [h1eq] at hthis

  have hspan_a_ne : Ideal.span {a} ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp ha0
  have hspan_b_ne : Ideal.span {b} ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp hb0
  have hcount_a : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      v ∈ (fullModulus m hm).finitePart.support →
      FractionalIdeal.count F v
        ((Ideal.span {a} : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
    intro v hv
    have hxcount : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F)) = 0 := by
      have h1 := hprime v hv
      rwa [coe_toPrincipalIdeal] at h1
    have hv_ne : (fullModulus m hm).finitePart v ≠ 0 := Finsupp.mem_support_iff.mp hv
    have hdvd_m : v.asIdeal ∣ m := by
      rw [fullModulus_finitePart] at hv_ne
      exact (Associates.count_ne_zero_iff_dvd hm v.irreducible).mp hv_ne
    have hbcount : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F)) = 0 := by
      rw [← hspanb, FractionalIdeal.count_coe F v hspan_b_ne]
      by_contra hne
      have hdvd : v.asIdeal ∣ Ideal.span {b} :=
        (Associates.count_ne_zero_iff_dvd hspan_b_ne v.irreducible).mp (fun h => hne (Nat.cast_eq_zero.mpr h))
      have hb_mem_v : b ∈ v.asIdeal :=
        (Ideal.dvd_iff_le.mp hdvd) (Ideal.mem_span_singleton_self b)
      have hb1_mem_v : b - 1 ∈ v.asIdeal := (Ideal.dvd_iff_le.mp hdvd_m) hb1m
      have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
        have := sub_mem hb_mem_v hb1_mem_v
        simpa using this
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    have hcoe : ((Ideal.span {a} : Ideal (𝓞 F)) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((x : F) * (b : F)) := by
      rw [FractionalIdeal.coeIdeal_span_singleton, ha]
    rw [hcoe, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul F v
        ((FractionalIdeal.spanSingleton_ne_zero_iff (S := nonZeroDivisors (𝓞 F))).mpr hxF)
        ((FractionalIdeal.spanSingleton_ne_zero_iff (S := nonZeroDivisors (𝓞 F))).mpr hbF),
      hxcount, hbcount, add_zero]
  have hspana : Ideal.span {a} ⊔ m = ⊤ :=
    sup_eq_top_of_forall_count_zero m hm (Ideal.span {a}) hspan_a_ne hcount_a
  exact ⟨a, b, ha0, hb0, ha, ha1f, hb1f, hapos, hbpos, hspana, hspanb_cop⟩

end DedekindZetaZeroFree.LargeSieve.RayBridge

end

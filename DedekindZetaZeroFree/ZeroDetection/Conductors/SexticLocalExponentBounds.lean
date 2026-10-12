module

public import DedekindZetaZeroFree.Arithmetic.Kummer.FrequencyClassesAndCharacterRigidity

@[expose] public section

open scoped NumberField
open IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.Detector.Conductor.LocalExponent

theorem principal_value_eq_one_of_sixth_power_congr
    (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hmt : m ≠ ⊤) (χ : RayClassCharacter F m)
    (hχ : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ m = ⊤ → χ I ^ (6 : ℕ) = 1)
    (a b : 𝓞 F) (ha : a ≠ 0)
    (hpos : ∀ φ : F →+* ℝ, 0 < φ (a : F))
    (hcop : Ideal.span {a} ⊔ m = ⊤) (hab : a - b ^ (6 : ℕ) ∈ m) :
    χ (Ideal.span {a}) = 1 := by
  have hone : (1 : 𝓞 F) ∈ Ideal.span {a} ⊔ m := by rw [hcop]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hone
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hx
  have had : a * d - 1 ∈ m := by
    have heq : a * d - 1 = -y := by linear_combination hxy
    rw [heq]
    exact m.neg_mem hy
  let c := b ^ (5 : ℕ) * d
  have hac : a * c ^ (6 : ℕ) - 1 ∈ m := by
    apply Ideal.Quotient.eq.mp
    have hab' : Ideal.Quotient.mk m a = Ideal.Quotient.mk m b ^ (6 : ℕ) := by
      simpa only [map_pow] using (Ideal.Quotient.eq.mpr hab)
    have had' : Ideal.Quotient.mk m a * Ideal.Quotient.mk m d = 1 := by
      simpa only [map_mul, map_one] using (Ideal.Quotient.eq.mpr had)
    have hbc : Ideal.Quotient.mk m b * Ideal.Quotient.mk m c = 1 := by
      dsimp [c]
      simp only [map_mul, map_pow]
      calc
        Ideal.Quotient.mk m b * (Ideal.Quotient.mk m b ^ 5 * Ideal.Quotient.mk m d) =
            Ideal.Quotient.mk m b ^ 6 * Ideal.Quotient.mk m d := by ring
        _ = 1 := by rw [← hab']; exact had'
    simp only [map_mul, map_pow, map_one]
    rw [hab', ← mul_pow, hbc, one_pow]
  have hac0 : a * c ^ (6 : ℕ) ≠ 0 := by
    intro hz
    have h1 : (1 : 𝓞 F) ∈ m := by simpa [hz] using m.neg_mem hac
    exact hmt (Ideal.eq_top_of_isUnit_mem m h1 isUnit_one)
  have hc0 : c ≠ 0 := by
    intro hz
    simp [hz] at hac0
  have hccop : Ideal.span {c} ⊔ m = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have hprod : a * c ^ (6 : ℕ) ∈ Ideal.span {c} ⊔ m := by
      apply Ideal.mem_sup_left
      exact Ideal.mul_mem_left _ _
        (Ideal.pow_mem_of_mem (Ideal.span {c}) (Ideal.mem_span_singleton_self c) 6 (by decide))
    have hsub : a * c ^ (6 : ℕ) - 1 ∈ Ideal.span {c} ⊔ m := Ideal.mem_sup_right hac
    simpa using (Ideal.span {c} ⊔ m).sub_mem hprod hsub
  have hval : χ (Ideal.span {a * c ^ (6 : ℕ)}) = 1 := by
    apply χ.map_span' _ hac0 hac
    intro φ
    change 0 < φ ((a : F) * (c : F) ^ (6 : ℕ))
    rw [map_mul, map_pow]
    apply mul_pos (hpos φ)
    have hcF : (c : F) ≠ 0 := (NumberField.RingOfIntegers.coe_ne_zero_iff).mpr hc0
    have hφ : φ (c : F) ≠ 0 := by
      intro hz
      exact hcF (φ.injective (by simpa using hz))
    positivity
  rw [← Ideal.span_singleton_mul_span_singleton, χ.map_mul',
    ← Ideal.span_singleton_pow] at hval
  have hpow : χ ((Ideal.span {c}) ^ (6 : ℕ)) = χ (Ideal.span {c}) ^ (6 : ℕ) := by
    induction 6 with
    | zero => simpa using χ.map_top'
    | succ n ih => rw [pow_succ, χ.map_mul', ih, pow_succ]
  rw [hpow, hχ _ (by simpa [Ideal.span_singleton_eq_bot] using hc0) hccop, mul_one] at hval
  exact hval

theorem primitive_modulus_not_lt_of_sixth_power_lifting
    (F : Type) [Field F] [NumberField F]
    (χ : PrimitiveFrequencyCharacter F)
    (hχ : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ χ.conductor = ⊤ →
      χ.character I ^ (6 : ℕ) = 1)
    (f : Ideal (𝓞 F))
    (hlift : ∀ a : 𝓞 F, a ≠ 0 → a - 1 ∈ f →
      (∀ φ : F →+* ℝ, 0 < φ (a : F)) → Ideal.span {a} ⊔ χ.conductor = ⊤ →
      ∃ b : 𝓞 F, a - b ^ (6 : ℕ) ∈ χ.conductor) :
    ¬ χ.conductor < f := by
  intro hlt
  have hmt : χ.conductor ≠ ⊤ := by
    intro heq
    simpa [heq] using hlt
  obtain ⟨a, ha, haf, hpos, hcop, hne⟩ := χ.primitive f hlt
  obtain ⟨b, hab⟩ := hlift a ha haf hpos hcop
  exact hne (principal_value_eq_one_of_sixth_power_congr F χ.conductor hmt
    χ.character hχ a b ha hpos hcop hab)

set_option maxHeartbeats 800000 in

theorem sixth_power_lifting_at_wild_maximal
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsMaximal]
    (e : ℕ) (he : p ^ e = Ideal.span {(6 : R)} ⊔ p ^ (e + 1))
    (a : R) (ha : a - 1 ∈ p ^ (2 * e + 1)) (n : ℕ) :
    ∃ b : R, b - 1 ∈ p ∧ a - b ^ (6 : ℕ) ∈ p ^ n := by
  have hpm : p.IsMaximal := inferInstance
  have hp : p.IsPrime := inferInstance
  have lift : ∀ n : ℕ, ∃ b : R, b - 1 ∈ p ∧
      a - b ^ (6 : ℕ) ∈ p ^ (2 * e + 1 + n) := by
    intro n
    induction n with
    | zero => exact ⟨1, by simp, by simpa using ha⟩
    | succ n ih =>
      obtain ⟨b, hb, herror⟩ := ih
      let m := 2 * e + 1 + n
      let r := e + 1 + n
      have her : e + r = m := by dsimp [m, r]; omega
      have hb0 : b ∉ p := by
        intro h
        exact hpm.ne_top ((Ideal.eq_top_iff_one p).mpr (by simpa using p.sub_mem h hb))
      have hb5 : b ^ (5 : ℕ) ∉ p := fun h => hb0 (hp.mem_of_pow_mem 5 h)
      obtain ⟨c, d, hd, hcd⟩ := Ideal.IsMaximal.exists_inv_pow p hb5 (m + 1)
      have hdecomp : p ^ m = Ideal.span {(6 : R)} * p ^ r ⊔ p ^ (m + 1) := by
        calc
          p ^ m = p ^ e * p ^ r := by rw [← pow_add, her]
          _ = (Ideal.span {(6 : R)} ⊔ p ^ (e + 1)) * p ^ r := by rw [← he]
          _ = Ideal.span {(6 : R)} * p ^ r ⊔ p ^ (m + 1) := by
            rw [Ideal.sup_mul, ← pow_add]
            congr 2
            omega
      have herrc : (a - b ^ (6 : ℕ)) * c ∈ p ^ m := Ideal.mul_mem_right c _ herror
      rw [hdecomp] at herrc
      obtain ⟨z, hz, y, hy, hzy⟩ := Submodule.mem_sup.mp herrc
      obtain ⟨t, ht, rfl⟩ := Ideal.mem_span_singleton_mul.mp hz
      have ht0 : t ∈ p := Ideal.pow_le_self (show r ≠ 0 by dsimp [r]; omega) ht
      refine ⟨b + t, ?_, ?_⟩
      · convert p.add_mem hb ht0 using 1 <;> ring
      have hlin : a - b ^ (6 : ℕ) - 6 * b ^ (5 : ℕ) * t ∈ p ^ (m + 1) := by
        have hmem := (p ^ (m + 1)).add_mem
          (Ideal.mul_mem_left _ (a - b ^ (6 : ℕ)) hd)
          (Ideal.mul_mem_left _ (b ^ (5 : ℕ)) hy)
        convert hmem using 1
        linear_combination -(a - b ^ (6 : ℕ)) * hcd - b ^ (5 : ℕ) * hzy
      have ht2 : t ^ 2 ∈ p ^ (m + 1) := by
        apply Ideal.pow_le_pow_right (show m + 1 ≤ r + r by dsimp [m, r]; omega)
        simpa only [pow_add, pow_two] using Ideal.mul_mem_mul ht ht
      have hrem := Ideal.mul_mem_right
        ((15 : R) * b ^ 4 + 20 * b ^ 3 * t + 15 * b ^ 2 * t ^ 2 + 6 * b * t ^ 3 + t ^ 4)
        (p ^ (m + 1)) ht2
      convert (p ^ (m + 1)).sub_mem hlin hrem using 1
      ring
  obtain ⟨b, hb, hab⟩ := lift n
  exact ⟨b, hb, Ideal.pow_le_pow_right (by omega) hab⟩

theorem sixth_power_lift_glue
    {R : Type*} [CommRing R] (p q : Ideal R) (hpq : p ⊔ q = ⊤)
    (a c : R) (haq : a - 1 ∈ q) (n : ℕ) (hac : a - c ^ (6 : ℕ) ∈ p ^ n) :
    ∃ b : R, a - b ^ (6 : ℕ) ∈ p ^ n * q := by
  have hcop : IsCoprime (p ^ n) q := Ideal.isCoprime_iff_sup_eq.mpr (Ideal.pow_sup_eq_top hpq)
  obtain ⟨x, hx, y, hy, hxy⟩ := hcop.exists
  let b := c * y + x
  have hbc : b - c ∈ p ^ n := by
    have heq : b - c = x * (1 - c) := by dsimp [b]; linear_combination c * hxy
    rw [heq]
    exact Ideal.mul_mem_right _ _ hx
  have hb1 : b - 1 ∈ q := by
    have heq : b - 1 = y * (c - 1) := by dsimp [b]; linear_combination hxy
    rw [heq]
    exact Ideal.mul_mem_right _ _ hy
  refine ⟨b, ?_⟩
  rw [Ideal.mul_eq_inf_of_isCoprime hcop]
  constructor
  · apply Ideal.Quotient.eq.mp
    have hbc' := Ideal.Quotient.eq.mpr hbc
    have hac' := Ideal.Quotient.eq.mpr hac
    simpa only [map_pow] using hac'.trans (congrArg (fun t => t ^ (6 : ℕ)) hbc').symm
  · apply Ideal.Quotient.eq.mp
    have hb1' := Ideal.Quotient.eq.mpr hb1
    have haq' := Ideal.Quotient.eq.mpr haq
    simp only [map_one] at hb1' haq'
    simpa only [map_pow] using haq'.trans (by rw [hb1', one_pow])

set_option maxHeartbeats 800000 in

theorem sextic_exponent_le_of_local_lifting
    (F : Type) [Field F] [NumberField F]
    (χ : PrimitiveFrequencyCharacter F)
    (hχ : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ χ.conductor = ⊤ →
      χ.character I ^ (6 : ℕ) = 1)
    (v : HeightOneSpectrum (𝓞 F)) (B : ℕ)
    (hlift : ∀ a : 𝓞 F, a - 1 ∈ v.asIdeal ^ B → ∀ n : ℕ,
      ∃ c : 𝓞 F, a - c ^ (6 : ℕ) ∈ v.asIdeal ^ n) :
    (normalizedFactors χ.conductor).count v.asIdeal ≤ B := by
  classical
  let k := (normalizedFactors χ.conductor).count v.asIdeal
  have hfin : FiniteMultiplicity v.asIdeal χ.conductor :=
    finiteMultiplicity_of_emultiplicity_eq_natCast
      (emultiplicity_eq_count_normalizedFactors v.irreducible χ.conductor_ne_zero)
  obtain ⟨q, hq, hqnot⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  rw [← v.count_normalizedFactors_eq_multiplicity χ.conductor_ne_zero] at hq
  change χ.conductor = v.asIdeal ^ k * q at hq
  have hpq : v.asIdeal ⊔ q = ⊤ := by
    by_contra h
    have hpqeq := v.isMaximal.eq_of_le h le_sup_left
    exact hqnot (Ideal.dvd_iff_le.mpr (hpqeq ▸ le_sup_right))
  by_contra hk
  have hkB : B < k := by omega
  have hle : χ.conductor ≤ v.asIdeal ^ B * q := by
    rw [hq]
    simpa only [mul_comm] using
      mul_le_mul_right (Ideal.pow_le_pow_right (I := v.asIdeal) (show B ≤ k by omega)) q
  have hlt : χ.conductor < v.asIdeal ^ B * q := by
    apply lt_of_le_of_ne hle
    intro heq
    have hq0 : q ≠ 0 := by intro h; simp [h] at hq; exact χ.conductor_ne_zero hq
    have heq' : v.asIdeal ^ k = v.asIdeal ^ B :=
      mul_right_cancel₀ hq0 (hq.symm.trans heq)
    have heq'' := congrArg (fun I : Ideal (𝓞 F) => (normalizedFactors I).count v.asIdeal) heq'
    have hk1 : k = B := by simpa [v.irreducible.normalizedFactors_pow] using heq''
    omega
  exact primitive_modulus_not_lt_of_sixth_power_lifting F χ hχ (v.asIdeal ^ B * q)
    (fun a _ ha _ _ => by
      obtain ⟨c, hc⟩ := hlift a (Ideal.mul_le_left ha) k
      rw [hq]
      exact sixth_power_lift_glue v.asIdeal q hpq a c (Ideal.mul_le_right ha) k hc) hlt

set_option maxHeartbeats 800000 in

theorem principal_sup_next_prime_power
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) (a : R) (ha : a ≠ 0) :
    let e := (normalizedFactors (Ideal.span {a})).count v.asIdeal
    v.asIdeal ^ e = Ideal.span {a} ⊔ v.asIdeal ^ (e + 1) := by
  classical
  have hI : Ideal.span {a} ≠ 0 := by simpa [Ideal.span_singleton_eq_bot] using ha
  have hfin : FiniteMultiplicity v.asIdeal (Ideal.span {a}) :=
    finiteMultiplicity_of_emultiplicity_eq_natCast
      (emultiplicity_eq_count_normalizedFactors v.irreducible hI)
  obtain ⟨q, hq, hqnot⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  rw [← v.count_normalizedFactors_eq_multiplicity hI] at hq
  have hpq : v.asIdeal ⊔ q = ⊤ := by
    by_contra h
    have hpqeq := v.isMaximal.eq_of_le h le_sup_left
    exact hqnot (Ideal.dvd_iff_le.mpr (hpqeq ▸ le_sup_right))
  dsimp only
  conv_rhs => lhs; rw [hq]
  rw [pow_succ, ← Ideal.mul_sup, sup_comm q, hpq]
  simp

theorem six_not_mem_of_absNorm_coprime
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (hv : (Ideal.absNorm v.asIdeal).Coprime 6) : (6 : 𝓞 F) ∉ v.asIdeal := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  have hcop : IsCoprime (Ideal.absNorm v.asIdeal : 𝓞 F) (6 : 𝓞 F) := by
    simpa using hv.isCoprime.map (Int.castRingHom (𝓞 F))
  exact Ideal.IsPrime.notMem_of_isCoprime_of_mem hcop (Ideal.absNorm_mem v.asIdeal)

set_option maxHeartbeats 800000 in

theorem sextic_conductor_exponent_bounds
    (F : Type) [Field F] [NumberField F] :
    ∃ b : HeightOneSpectrum (𝓞 F) → ℕ,
      (∀ v, (Ideal.absNorm v.asIdeal).Coprime 6 → b v = 1) ∧
      ∀ (χ : PrimitiveFrequencyCharacter F),
        (∀ n : Ideal (𝓞 F), n ≠ ⊥ → n ⊔ χ.conductor = ⊤ →
          χ.character n ^ (6 : ℕ) = 1) →
        ∀ v : HeightOneSpectrum (𝓞 F),
          (normalizedFactors χ.conductor).count v.asIdeal ≤ b v := by
  classical
  let e : HeightOneSpectrum (𝓞 F) → ℕ :=
    fun v => (normalizedFactors (Ideal.span {(6 : 𝓞 F)})).count v.asIdeal
  refine ⟨fun v => 2 * e v + 1, ?_, ?_⟩
  · intro v hv
    have h6 := six_not_mem_of_absNorm_coprime F v hv
    have he0 : e v = 0 := by
      dsimp [e]
      apply Multiset.count_eq_zero.mpr
      intro h
      have hd := dvd_of_mem_normalizedFactors h
      exact h6 ((Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp hd))
    change 2 * e v + 1 = 1
    rw [he0]
  · intro χ hχ v
    letI : v.asIdeal.IsMaximal := v.isMaximal
    apply sextic_exponent_le_of_local_lifting F χ hχ v
    intro a ha n
    obtain ⟨c, _, hc⟩ := sixth_power_lifting_at_wild_maximal v.asIdeal (e v)
      (principal_sup_next_prime_power v (6 : 𝓞 F) (by norm_num)) a ha n
    exact ⟨c, hc⟩

end DedekindZetaZeroFree.Detector.Conductor.LocalExponent

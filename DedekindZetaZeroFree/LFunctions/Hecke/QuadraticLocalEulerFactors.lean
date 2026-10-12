module

public import DedekindZetaZeroFree.Arithmetic.Ideals.FinitePrimeContractionFibers
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveQuadraticRamification
public import ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusOrder

@[expose] public section

open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.LargeSieve

private lemma invs {F : Type} [Field F] [NumberField F]
    {f : Ideal (𝓞 F)} {η : DedekindZetaZeroFree.RayClassCharacter F f}
    (d : QuadraticRayExtensionData η) (p : HeightOneSpectrum (𝓞 F))
    (Q : HeightOneSpectrum (𝓞 d.extension)) (hQ : Q.asIdeal.LiesOver p.asIdeal) :
    (p.asIdeal.primesOver (𝓞 d.extension)).ncard *
      (Q.asIdeal.ramificationIdx (𝓞 F) * Q.asIdeal.inertiaDeg (𝓞 F)) = 2 := by
  letI : Q.asIdeal.LiesOver p.asIdeal := hQ
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    p.asIdeal (𝓞 d.extension) (d.extension ≃ₐ[F] d.extension)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal Q.asIdeal
    (d.extension ≃ₐ[F] d.extension),
    Ideal.inertiaDegIn_eq_inertiaDeg p.asIdeal Q.asIdeal
    (d.extension ≃ₐ[F] d.extension),
    IsGalois.card_aut_eq_finrank, d.degree_two] at h
  exact h
 noncomputable def fiberEquiv {F E : Type} [Field F] [Field E]
    [NumberField F] [NumberField E] [Algebra F E] (p : HeightOneSpectrum (𝓞 F)) :
    {Q : HeightOneSpectrum (𝓞 E) // Q.asIdeal.LiesOver p.asIdeal} ≃
      p.asIdeal.primesOver (𝓞 E) where
  toFun Q := ⟨Q.1.asIdeal, Q.1.isPrime, Q.2⟩
  invFun Q := ⟨⟨Q.1, Q.2.1, by
    letI : Q.1.LiesOver p.asIdeal := Q.2.2
    exact Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q.1⟩, Q.2.2⟩
  left_inv Q := rfl
  right_inv Q := rfl

private lemma fiber_card {F E : Type} [Field F] [Field E]
    [NumberField F] [NumberField E] [Algebra F E] (p : HeightOneSpectrum (𝓞 F)) :
    Nat.card {Q : HeightOneSpectrum (𝓞 E) // Q.asIdeal.LiesOver p.asIdeal} =
      (p.asIdeal.primesOver (𝓞 E)).ncard := by
  rw [Nat.card_congr (fiberEquiv p), Set.ncard_eq_toFinset_card']
  simp

private lemma constant_local {F : Type} [Field F] [NumberField F]
    {f : Ideal (𝓞 F)} {η : DedekindZetaZeroFree.RayClassCharacter F f}
    (d : QuadraticRayExtensionData η) (p : HeightOneSpectrum (𝓞 F))
    (Q : HeightOneSpectrum (𝓞 d.extension)) (hQ : Q.asIdeal.LiesOver p.asIdeal)
    (s : ℂ) (n g : ℕ)
    (hn : Q.asIdeal.inertiaDeg (𝓞 F) = n)
    (hg : (p.asIdeal.primesOver (𝓞 d.extension)).ncard = g) :
    (∏' Q : {Q : HeightOneSpectrum (𝓞 d.extension) // Q.asIdeal.LiesOver p.asIdeal},
      (1 - (Ideal.absNorm Q.val.asIdeal : ℂ) ^ (-s))⁻¹) =
      (1 - ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ^ n)⁻¹ ^ g := by
  letI := IdealEuler.finite_prime_liesOver (E := d.extension) p
  have hconst (R : {Q : HeightOneSpectrum (𝓞 d.extension) // Q.asIdeal.LiesOver p.asIdeal}) :
      (Ideal.absNorm R.1.asIdeal : ℂ) ^ (-s) =
        ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ^ n := by
    letI : Q.asIdeal.LiesOver p.asIdeal := hQ
    letI : R.1.asIdeal.LiesOver p.asIdeal := R.2
    have hr := Ideal.inertiaDeg_eq_of_isGaloisGroup p.asIdeal R.1.asIdeal Q.asIdeal
      (d.extension ≃ₐ[F] d.extension)
    rw [← Ideal.absNorm_pow_inertiaDeg p.asIdeal R.1.asIdeal, hr, hn]
    push_cast
    have hpow := Complex.cpow_mul_ofReal_nonneg
      (Nat.cast_nonneg (Ideal.absNorm p.asIdeal) : (0 : ℝ) ≤ _)
      (n : ℝ) (-s)
    rw [Real.rpow_natCast] at hpow
    push_cast at hpow
    rw [← hpow, Complex.cpow_nat_mul]
  simp_rw [hconst]
  letI := Fintype.ofFinite {Q : HeightOneSpectrum (𝓞 d.extension) // Q.asIdeal.LiesOver p.asIdeal}
  rw [tprod_fintype, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    fiber_card, hg]
private lemma unramified_cases {F : Type} [Field F] [NumberField F]
    {f : Ideal (𝓞 F)} {η : DedekindZetaZeroFree.RayClassCharacter F f}
    (d : QuadraticRayExtensionData η) (p : HeightOneSpectrum (𝓞 F))
    (hgood : p.asIdeal ⊔ f = ⊤)
    (Q : HeightOneSpectrum (𝓞 d.extension)) (hQ : Q.asIdeal.LiesOver p.asIdeal) :
    (η p.asIdeal = 1 ∧ Q.asIdeal.inertiaDeg (𝓞 F) = 1 ∧
      (p.asIdeal.primesOver (𝓞 d.extension)).ncard = 2) ∨
    (η p.asIdeal = -1 ∧ Q.asIdeal.inertiaDeg (𝓞 F) = 2 ∧
      (p.asIdeal.primesOver (𝓞 d.extension)).ncard = 1) := by
  letI : Q.asIdeal.LiesOver p.asIdeal := hQ
  have hunr := d.unramified p hgood Q.asIdeal Q.isPrime hQ
  letI := hunr
  have he := Ideal.ramificationIdx_eq_one Q.asIdeal (𝓞 F)
  have hefg := invs d p Q hQ
  rw [he, one_mul] at hefg
  have hord := ClassFieldTheory.orderOf_arithmeticFrobeniusAt_eq_inertiaDegree p Q hQ hunr
  have hχ := d.frobenius p hgood Q hQ
  have hs : (η p.asIdeal) ^ 2 = 1 := by
    rw [← hχ, ← Units.val_pow_eq_pow_val, d.character_square]
    rfl
  have hone : η p.asIdeal = 1 ↔ ClassFieldTheory.arithmeticFrobeniusAt (K := F) Q = 1 := by
    rw [← hχ]
    constructor
    · intro h
      apply d.character_injective
      rw [map_one]
      exact Units.ext h
    · intro h
      rw [h, map_one]
      rfl
  rcases sq_eq_one_iff.mp hs with h1 | hm
  · left
    have hi : Q.asIdeal.inertiaDeg (𝓞 F) = 1 := by
      rw [← hord, hone.mp h1, orderOf_one]
    rw [hi, mul_one] at hefg
    exact ⟨h1, hi, hefg⟩
  · right
    have hi : Q.asIdeal.inertiaDeg (𝓞 F) = 2 := by
      rw [← hord]
      apply orderOf_eq_prime
      · apply d.character_injective
        rw [map_pow, d.character_square, map_one]
      · intro h
        have hh := hone.mpr h
        rw [hm] at hh
        norm_num at hh
    rw [hi] at hefg
    exact ⟨hm, hi, by omega⟩
private lemma ramified_cases {F : Type} [Field F] [NumberField F]
    {f : Ideal (𝓞 F)} {η : DedekindZetaZeroFree.RayClassCharacter F f}
    (d : QuadraticRayExtensionData η) (p : HeightOneSpectrum (𝓞 F))
    (Q : HeightOneSpectrum (𝓞 d.extension)) (hQ : Q.asIdeal.LiesOver p.asIdeal)
    (hunr : ¬ Algebra.IsUnramifiedAt (𝓞 F) Q.asIdeal) :
    Q.asIdeal.inertiaDeg (𝓞 F) = 1 ∧
      (p.asIdeal.primesOver (𝓞 d.extension)).ncard = 1 := by
  letI : Q.asIdeal.LiesOver p.asIdeal := hQ
  have hefg := invs d p Q hQ
  have hepos := Q.asIdeal.ramificationIdx_pos (𝓞 F)
  have hfpos := Q.asIdeal.inertiaDeg_pos (𝓞 F)
  have he1 : Q.asIdeal.ramificationIdx (𝓞 F) ≠ 1 := by
    exact fun h => hunr (Ideal.ramificationIdx_eq_one_iff.mp h)
  have hgb : (p.asIdeal.primesOver (𝓞 d.extension)).ncard ≠ 0 := by
    intro h
    rw [h, zero_mul] at hefg
    omega
  have he2 : 2 ≤ Q.asIdeal.ramificationIdx (𝓞 F) := by omega
  have heupper : (p.asIdeal.primesOver (𝓞 d.extension)).ncard *
      (2 * Q.asIdeal.inertiaDeg (𝓞 F)) ≤ 2 := by
    calc _ ≤ (p.asIdeal.primesOver (𝓞 d.extension)).ncard *
        (Q.asIdeal.ramificationIdx (𝓞 F) * Q.asIdeal.inertiaDeg (𝓞 F)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ he2)
      _ = 2 := hefg
  have hfupper : 2 * Q.asIdeal.inertiaDeg (𝓞 F) ≤ 2 := by
    calc _ ≤ (p.asIdeal.primesOver (𝓞 d.extension)).ncard *
        (2 * Q.asIdeal.inertiaDeg (𝓞 F)) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hgb)
      _ ≤ 2 := heupper
  have hi : Q.asIdeal.inertiaDeg (𝓞 F) = 1 := by omega
  rw [hi, mul_one] at heupper
  exact ⟨hi, by omega⟩

theorem quadratic_local_euler_factors
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hn : ¬ η.IsPrincipal) (hp : η.IsPrimitive)
    (d : QuadraticRayExtensionData η)
    (p : HeightOneSpectrum (𝓞 F)) (s : ℂ) (hs : 1 < s.re) :
    (∏' Q : {Q : HeightOneSpectrum (𝓞 d.extension) //
        Q.asIdeal.LiesOver p.asIdeal},
      (1 - (Ideal.absNorm Q.val.asIdeal : ℂ) ^ (-s))⁻¹) =
      (1 - (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹ *
        (1 - η p.asIdeal * (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹ := by
  classical
  let x : ℂ := (Ideal.absNorm p.asIdeal : ℂ) ^ (-s)
  by_cases hgood : p.asIdeal ⊔ f = ⊤
  · obtain ⟨Q⟩ : Nonempty (p.asIdeal.primesOver (𝓞 d.extension)) := inferInstance
    let Q' : HeightOneSpectrum (𝓞 d.extension) :=
      ⟨Q.1, Q.2.1, by
        letI : Q.1.LiesOver p.asIdeal := Q.2.2
        exact Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q.1⟩
    have hQ : Q'.asIdeal.LiesOver p.asIdeal := Q.2.2
    rcases unramified_cases d p hgood Q' hQ with ⟨hη, hi, hg⟩ | ⟨hη, hi, hg⟩
    · rw [constant_local d p Q' hQ s 1 2 hi hg, hη]
      change (1 - x ^ 1)⁻¹ ^ 2 = (1 - x)⁻¹ * (1 - 1 * x)⁻¹
      simp [pow_two]
    · rw [constant_local d p Q' hQ s 2 1 hi hg, hη]
      change (1 - x ^ 2)⁻¹ ^ 1 = (1 - x)⁻¹ * (1 - -1 * x)⁻¹
      rw [pow_one, neg_one_mul, sub_neg_eq_add, ← mul_inv_rev]
      congr 1
      ring
  · obtain ⟨Q, hQ, hunr⟩ :=
      (quadratic_primitive_ramification F hF f hf η hq hn hp d p).mp hgood
    have ⟨hi, hg⟩ := ramified_cases d p Q hQ hunr
    have hη : η p.asIdeal = 0 :=
      (η.eq_zero_iff' p.asIdeal).mpr (Or.inr hgood)
    rw [constant_local d p Q hQ s 1 1 hi hg, hη]
    change (1 - x ^ 1)⁻¹ ^ 1 = (1 - x)⁻¹ * (1 - 0 * x)⁻¹
    simp

end DedekindZetaZeroFree.LargeSieve

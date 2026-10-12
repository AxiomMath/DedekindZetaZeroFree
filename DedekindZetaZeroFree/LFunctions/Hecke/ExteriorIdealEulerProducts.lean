module

public import DedekindZetaZeroFree.Arithmetic.Ideals.Counting.NormSeries
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterUnitarity
public import DedekindZetaZeroFree.Arithmetic.Ideals.ExteriorEulerProducts.PrimeExponentCoordinates
public import DedekindZetaZeroFree.Analysis.EulerProducts.GeometricProduct

@[expose] public section

namespace DedekindZetaZeroFree.ExteriorIdealEuler

noncomputable section
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

def one (cS : Ideal (𝓞 F)) : ExteriorIdeal cS :=
  ⟨⊤, by simp⟩

def mul {cS : Ideal (𝓞 F)} (I J : ExteriorIdeal cS) : ExteriorIdeal cS :=
  ⟨I.val * J.val, mul_ne_zero I.property.1 J.property.1,
    by rw [Ideal.mul_sup_eq_of_coprime_left I.property.2]; exact J.property.2⟩

def pow {cS : Ideal (𝓞 F)} (I : ExteriorIdeal cS) (k : ℕ) : ExteriorIdeal cS :=
  ⟨I.val ^ k, pow_ne_zero k I.property.1, Ideal.pow_sup_eq_top I.property.2⟩

def PrimeIndex (cS : Ideal (𝓞 F)) :=
  {p : ExteriorIdeal cS // Prime p.val}

structure IsCoefficient {cS : Ideal (𝓞 F)} (a : ExteriorIdeal cS → ℂ) : Prop where
  map_one : a (one cS) = 1
  map_mul : ∀ I J : ExteriorIdeal cS, I.val ⊔ J.val = ⊤ →
    a (mul I J) = a I * a J
  norm_le_one : ∀ I : ExteriorIdeal cS, ‖a I‖ ≤ 1
  map_prime_pow : ∀ (p : PrimeIndex cS) (k : ℕ),
    a (pow p.val k) = a p.val ^ k

def summand {cS : Ideal (𝓞 F)} (a : ExteriorIdeal cS → ℂ) (s : ℂ)
    (I : ExteriorIdeal cS) : ℂ :=
  a I * (Ideal.absNorm I.val : ℂ) ^ (-s)

def primeTerm {cS : Ideal (𝓞 F)} (a : ExteriorIdeal cS → ℂ) (s : ℂ)
    (p : PrimeIndex cS) : ℂ :=
  summand a s p.val

def factor {cS : Ideal (𝓞 F)} (a : ExteriorIdeal cS → ℂ) (s : ℂ)
    (p : PrimeIndex cS) : ℂ :=
  (1 - primeTerm a s p)⁻¹

theorem summand_one {cS : Ideal (𝓞 F)} (a : ExteriorIdeal cS → ℂ)
    (ha : IsCoefficient a) (s : ℂ) : summand a s (one cS) = 1 := by
  unfold summand
  rw [ha.map_one]
  simp [one]

theorem summand_mul {cS : Ideal (𝓞 F)} (a : ExteriorIdeal cS → ℂ)
    (ha : IsCoefficient a) (s : ℂ) (I J : ExteriorIdeal cS)
    (h : I.val ⊔ J.val = ⊤) :
    summand a s (mul I J) = summand a s I * summand a s J := by
  unfold summand
  rw [ha.map_mul I J h]
  change a I * a J * (Ideal.absNorm (I.val * J.val) : ℂ) ^ (-s) = _
  rw [map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

theorem summand_prime_pow {cS : Ideal (𝓞 F)} (a : ExteriorIdeal cS → ℂ)
    (ha : IsCoefficient a) (s : ℂ) (p : PrimeIndex cS) (k : ℕ) :
    summand a s (pow p.val k) = primeTerm a s p ^ k := by
  simp only [primeTerm, summand]
  rw [ha.map_prime_pow p k]
  change a p.val ^ k * (Ideal.absNorm (p.val.val ^ k) : ℂ) ^ (-s) = _
  rw [map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul, mul_pow]

theorem norm_summand_le {cS : Ideal (𝓞 F)}
    (a : ExteriorIdeal cS → ℂ) (ha : IsCoefficient a) (s : ℂ)
    (I : ExteriorIdeal cS) :
    ‖summand a s I‖ ≤ (idealNorm I.val) ^ (-s.re) := by
  have hq0 : 0 < idealNorm I.val := lt_of_lt_of_le zero_lt_one
    (idealNorm_ge_one _ I.property.1)
  have hc : (Ideal.absNorm I.val : ℂ) = (idealNorm I.val : ℂ) := by simp [idealNorm]
  rw [summand, norm_mul, hc, Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
  simpa using mul_le_mul_of_nonneg_right (ha.norm_le_one I)
    (Real.rpow_nonneg hq0.le (-s.re))

theorem summable_norm_summand {cS : Ideal (𝓞 F)}
    (a : ExteriorIdeal cS → ℂ) (ha : IsCoefficient a) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I : ExteriorIdeal cS => ‖summand a s I‖) := by
  let incl : ExteriorIdeal cS → NonzeroIdeal F := fun I => ⟨I.val, I.property.1⟩
  have hi : Function.Injective incl := by
    intro I J h
    exact Subtype.ext (congrArg (fun J : NonzeroIdeal F => J.val) h)
  exact ((ideal_norm_rpow_summable F s.re hs).comp_injective hi).of_nonneg_of_le
    (fun I => norm_nonneg _) (norm_summand_le a ha s)

theorem norm_primeTerm_lt_one {cS : Ideal (𝓞 F)}
    (a : ExteriorIdeal cS → ℂ) (ha : IsCoefficient a) (s : ℂ) (hs : 1 < s.re)
    (p : PrimeIndex cS) : ‖primeTerm a s p‖ < 1 := by
  have hq : 2 ≤ idealNorm p.val.val := idealNorm_prime_ge_two _ p.property
  have hq0 : 0 < idealNorm p.val.val := by linarith
  calc
    ‖primeTerm a s p‖ ≤ (idealNorm p.val.val) ^ (-s.re) := norm_summand_le a ha s p.val
    _ ≤ (idealNorm p.val.val) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (idealNorm p.val.val)⁻¹ := Real.rpow_neg_one _
    _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq
    _ < 1 := by norm_num

theorem summable_norm_primeTerm {cS : Ideal (𝓞 F)}
    (a : ExteriorIdeal cS → ℂ) (ha : IsCoefficient a) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun p : PrimeIndex cS => ‖primeTerm a s p‖) :=
  (summable_norm_summand a ha s hs).comp_injective Subtype.val_injective

theorem inverse_factors_hasProd_ne_zero {cS : Ideal (𝓞 F)}
    (a : ExteriorIdeal cS → ℂ) (ha : IsCoefficient a) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : PrimeIndex cS => 1 - primeTerm a s p)
      (∏' (p : PrimeIndex cS), (1 - primeTerm a s p)) ∧
      (∏' (p : PrimeIndex cS), (1 - primeTerm a s p)) ≠ 0 := by
  have hn : Summable (fun p : PrimeIndex cS => ‖-primeTerm a s p‖) := by
    simpa using summable_norm_primeTerm a ha s hs
  have hne (p : PrimeIndex cS) : 1 + -primeTerm a s p ≠ 0 := by
    rw [← sub_eq_add_neg, sub_ne_zero]
    intro h
    have hb := norm_primeTerm_lt_one a ha s hs p
    rw [← h, norm_one] at hb
    exact lt_irrefl _ hb
  simpa only [← sub_eq_add_neg] using
    And.intro (multipliable_one_add_of_summable hn).hasProd
      (tprod_one_add_ne_zero_of_summable hne hn)

theorem factors_hasProd {cS : Ideal (𝓞 F)}
    (a : ExteriorIdeal cS → ℂ) (ha : IsCoefficient a) (s : ℂ) (hs : 1 < s.re) :
    HasProd (factor a s) (∏' (p : PrimeIndex cS), (1 - primeTerm a s p))⁻¹ :=
  (inverse_factors_hasProd_ne_zero a ha s hs).1.inv₀
    (inverse_factors_hasProd_ne_zero a ha s hs).2

theorem exterior_ideal_euler {cS : Ideal (𝓞 F)}
    (a : ExteriorIdeal cS → ℂ) (ha : IsCoefficient a)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I : ExteriorIdeal cS => ‖summand a s I‖) ∧
    HasProd (factor a s) (∑' I : ExteriorIdeal cS, summand a s I) ∧
    (∑' I : ExteriorIdeal cS, summand a s I) ≠ 0 ∧
    HasProd (fun p : PrimeIndex cS => 1 - primeTerm a s p)
      (∑' I : ExteriorIdeal cS, summand a s I)⁻¹ := by
  let e := ExteriorEulerPrimeIndex.exponentEquiv cS
  let r : ExteriorEulerPrimeIndex.exteriorPrimeRawIndex cS → ℂ := primeTerm a s
  let g : (ExteriorEulerPrimeIndex.exteriorPrimeRawIndex cS →₀ ℕ) → ℂ :=
    fun v => v.prod (fun p k => r p ^ k)
  have hfac (I : ExteriorIdeal cS) : summand a s I = g (e I) :=
    ExteriorEulerPrimeIndex.coefficient_factorization (summand a s)
      (summand_one a ha s) (summand_mul a ha s) (summand_prime_pow a ha s) I
  have hn := summable_norm_summand a ha s hs
  have hg : Summable (fun v => ‖g v‖) := by
    apply e.summable_iff.mp
    simpa only [Function.comp_def, ← hfac] using hn
  have ht : (∑' v, g v) = ∑' I : ExteriorIdeal cS, summand a s I := by
    rw [← e.tsum_eq g]
    exact tsum_congr (fun I => (hfac I).symm)
  have hp : HasProd (factor a s) (∑' I : ExteriorIdeal cS, summand a s I) := by
    have h := ExteriorEulerGeometricProduct.hasProd_geometric r
      (norm_primeTerm_lt_one a ha s hs) hg
    rw [ht] at h
    exact h
  have hi := inverse_factors_hasProd_ne_zero a ha s hs
  have heq : (∑' I : ExteriorIdeal cS, summand a s I) =
      (∏' (p : PrimeIndex cS), (1 - primeTerm a s p))⁻¹ :=
    hp.unique (factors_hasProd a ha s hs)
  refine ⟨hn, hp, ?_, ?_⟩
  · rw [heq]
    exact inv_ne_zero hi.2
  · rw [heq, inv_inv]
    exact hi.1

theorem constant_one_isCoefficient (cS : Ideal (𝓞 F)) :
    IsCoefficient (fun _ : ExteriorIdeal cS => (1 : ℂ)) := by
  constructor <;> intros <;> simp

def zeroMaskedRayCoefficient {cS : Ideal (𝓞 F)}
    {𝔪 : Ideal (𝓞 F)} (η : RayClassCharacter F 𝔪)
    (mask : Ideal (𝓞 F)) (I : ExteriorIdeal cS) : ℂ :=
  if I.val ⊔ mask = ⊤ then η I.val else 0

theorem zeroMaskedRay_isCoefficient {cS : Ideal (𝓞 F)}
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (mask : Ideal (𝓞 F)) :
    IsCoefficient (zeroMaskedRayCoefficient (cS := cS) η mask) := by
  have hmul (I J : Ideal (𝓞 F)) :
      I * J ⊔ mask = ⊤ ↔ I ⊔ mask = ⊤ ∧ J ⊔ mask = ⊤ := by
    constructor
    · intro h
      exact ⟨top_unique (h ▸ sup_le_sup_right Ideal.mul_le_left mask),
        top_unique (h ▸ sup_le_sup_right Ideal.mul_le_right mask)⟩
    · rintro ⟨hI, hJ⟩
      rw [Ideal.mul_sup_eq_of_coprime_left hI]
      exact hJ
  constructor
  · simp [zeroMaskedRayCoefficient, one, η.map_top']
  · intro I J _
    simp only [zeroMaskedRayCoefficient, mul, hmul, η.map_mul']
    split_ifs <;> simp_all
  · intro I
    unfold zeroMaskedRayCoefficient
    split_ifs
    · exact RayUnitary.ray_character_norm_le_one F 𝔪 h𝔪 η I.val
    · simp
  · intro p k
    have hη : η (p.val.val ^ k) = η p.val.val ^ k := by
      induction k with
      | zero => simp [η.map_top']
      | succ k ih => rw [pow_succ, η.map_mul', ih, pow_succ]
    by_cases hk : k = 0
    · simp [hk, zeroMaskedRayCoefficient, pow, η.map_top']
    have hpow : p.val.val ^ k ⊔ mask = ⊤ ↔ p.val.val ⊔ mask = ⊤ := by
      constructor
      · intro h
        have hle : p.val.val ^ k ⊔ mask ≤ p.val.val ⊔ mask :=
          sup_le_sup_right (Ideal.pow_le_self hk) mask
        rw [h] at hle
        exact top_unique hle
      · exact Ideal.pow_sup_eq_top
    simp only [zeroMaskedRayCoefficient, pow, hpow, hη]
    split_ifs <;> simp [hk]

end
end DedekindZetaZeroFree.ExteriorIdealEuler

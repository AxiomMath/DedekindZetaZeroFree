module
public import Mathlib.GroupTheory.ArchimedeanDensely

public import DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerLocalization.Denominator

@[expose] public section

open scoped NumberField Classical WithZero nonZeroDivisors
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SIntegerLocalization
noncomputable section
variable {F : Type} [Field F] [NumberField F]

private theorem exists_pow_mul_le_one (a b : ℤᵐ⁰) (ha : a < 1) (hb : b ≠ 0) :
    ∃ n : ℕ, a ^ n * b ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_pow_lt₀ ha (Units.mk0 b⁻¹ (inv_ne_zero hb))
  exact ⟨n, (lt_of_lt_of_eq (mul_lt_mul_of_pos_right hn (zero_lt_iff.mpr hb))
    (inv_mul_cancel₀ hb)).le⟩

theorem exists_denominator_power (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : (S : Set (HeightOneSpectrum (𝓞 F))).integer F) :
    ∃ n : ℕ, ∃ a : 𝓞 F,
      algebraMap (𝓞 F) F a = (algebraMap (𝓞 F) F (denominator S)) ^ n * (x : F) := by
  by_cases hx : (x : F) = 0
  · exact ⟨0, 0, by simp [hx]⟩
  have hn (v : S) : ∃ n : ℕ,
      (v.val.valuation F (algebraMap (𝓞 F) F (denominator S))) ^ n *
        v.val.valuation F (x : F) ≤ 1 :=
    exists_pow_mul_le_one _ _ (valuation_denominator_lt_one S v.val v.property)
      ((Valuation.ne_zero_iff _).mpr hx)
  choose n hn using hn
  let N := ∑ v : S, n v
  have hval (v : HeightOneSpectrum (𝓞 F)) :
      v.valuation F ((algebraMap (𝓞 F) F (denominator S)) ^ N * (x : F)) ≤ 1 := by
    rw [map_mul, map_pow]
    by_cases hv : v ∈ S
    · have hnN : n ⟨v, hv⟩ ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      have hp : (v.valuation F (algebraMap (𝓞 F) F (denominator S))) ^ N ≤
          (v.valuation F (algebraMap (𝓞 F) F (denominator S))) ^ n ⟨v, hv⟩ :=
        pow_le_pow_of_le_one (zero_le : 0 ≤ v.valuation F (algebraMap (𝓞 F) F (denominator S)))
          (v.valuation_le_one (denominator S)) hnN
      exact (mul_le_mul_of_nonneg_right hp
        (zero_le : 0 ≤ v.valuation F (x : F))).trans (hn ⟨v, hv⟩)
    · rw [valuation_denominator_eq_one S v hv, one_pow, one_mul]
      exact x.property v hv
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hval
  exact ⟨N, a, ha⟩

theorem isLocalization_away (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsLocalization.Away (denominator S)
      ((S : Set (HeightOneSpectrum (𝓞 F))).integer F) := by
  change IsLocalization (Submonoid.powers (denominator S)) _
  rw [isLocalization_iff]
  constructor
  · intro y
    obtain ⟨n, hn⟩ := y.property
    change IsUnit (algebraMap (𝓞 F) _ (y : 𝓞 F))
    rw [← hn, map_pow]
    let t := denominator S
    let ti : (S : Set (HeightOneSpectrum (𝓞 F))).integer F :=
      ⟨(algebraMap (𝓞 F) F t)⁻¹, fun v hv => by
        rw [map_inv₀, valuation_denominator_eq_one S v hv, inv_one]⟩
    have hunit : IsUnit (algebraMap (𝓞 F)
        ((S : Set (HeightOneSpectrum (𝓞 F))).integer F) t) := by
      apply isUnit_iff_exists_inv.mpr
      exact ⟨ti, Subtype.ext (mul_inv_cancel₀
        ((IsFractionRing.injective (𝓞 F) F).ne (denominator_ne_zero S)))⟩
    simpa using hunit.pow n
  constructor
  · intro x
    obtain ⟨n, a, ha⟩ := exists_denominator_power S x
    refine ⟨(a, ⟨denominator S ^ n, ⟨n, rfl⟩⟩), ?_⟩
    apply Subtype.ext
    simpa [map_pow, mul_comm] using ha.symm
  · intro x y h
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_one, one_mul]
    apply IsFractionRing.injective (𝓞 F) F
    exact congrArg (fun r : (S : Set (HeightOneSpectrum (𝓞 F))).integer F => (r : F)) h

end
end DedekindZetaZeroFree.SIntegerLocalization

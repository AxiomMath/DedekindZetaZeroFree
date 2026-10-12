module

public import DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerLocalization.IdealCorrespondence
public import DedekindZetaZeroFree.Arithmetic.Ideals.ExteriorIdeals.EulerWeights

@[expose] public section

open scoped NumberField Classical WithZero
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SIntegerLocalization
noncomputable section
variable {F : Type} [Field F] [NumberField F]

 def boundIdeal (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) (n : ℕ) :
    Ideal ((S : Set (HeightOneSpectrum (𝓞 F))).integer F) where
  carrier := {a | v.valuation F (a : F) ≤ WithZero.exp (-(n : ℤ))}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change v.valuation F ((a : F) + (b : F)) ≤ _
    exact (ValuationClass.map_add_le_max _ _ _).trans (max_le ha hb)
  smul_mem' := by
    intro a b hb
    change v.valuation F ((a : F) * (b : F)) ≤ _
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (a.property v hv) zero_le).trans (by simpa using hb)

theorem generator_valuation (S : Finset (HeightOneSpectrum (𝓞 F)))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (r : (S : Set (HeightOneSpectrum (𝓞 F))).integer F) (hr : r ≠ 0)
    (hspan : Ideal.span {r} = Ideal.map (algebraMap (𝓞 F) _) I)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    v.valuation F (r : F) = WithZero.exp (-(idealPrimeExponent v.asIdeal I : ℤ)) := by
  let n := idealPrimeExponent v.asIdeal I
  have hdvd (k : ℕ) : v.asIdeal ^ k ∣ I ↔ k ≤ n := by
    rw [pow_dvd_iff_le_emultiplicity,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hI]
    simp [n, idealPrimeExponent]
  have hIn : I ≤ v.asIdeal ^ n := Ideal.dvd_iff_le.mp ((hdvd n).mpr le_rfl)
  have hnot : ¬ I ≤ v.asIdeal ^ (n + 1) := by
    rw [← Ideal.dvd_iff_le, hdvd]; omega
  have hmap : Ideal.map (algebraMap (𝓞 F) _) I ≤ boundIdeal S v hv n := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change v.valuation F (a : F) ≤ WithZero.exp (-(n : ℤ))
    rw [v.valuation_of_algebraMap]
    exact (v.intValuation_le_pow_iff_mem a n).mpr (hIn ha)
  have hrv : v.valuation F (r : F) ≤ WithZero.exp (-(n : ℤ)) := by
    apply hmap
    rw [← hspan]
    exact Ideal.subset_span (Set.mem_singleton r)
  obtain ⟨a, ha, han⟩ : ∃ a : 𝓞 F, a ∈ I ∧ a ∉ v.asIdeal ^ (n + 1) := by
    contrapose! hnot
    exact hnot
  have ham : algebraMap (𝓞 F) _ a ∈ Ideal.span ({r} : Set _) := by
    rw [hspan]
    exact Ideal.mem_map_of_mem _ ha
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp ham
  have hav : v.valuation F (a : F) ≤ v.valuation F (r : F) := by
    have hh := congrArg (fun t : (S : Set (HeightOneSpectrum (𝓞 F))).integer F => (t : F)) hy
    change (a : F) = (r : F) * (y : F) at hh
    rw [hh, map_mul]
    exact (mul_le_mul_of_nonneg_left (y.property v hv) zero_le).trans (by simp)
  have hrv' : ¬ v.valuation F (r : F) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    intro h
    apply han
    apply (v.intValuation_le_pow_iff_mem a (n + 1)).mp
    rw [← v.valuation_of_algebraMap (K := F)]
    exact hav.trans h
  have hnz : v.valuation F (r : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr
    (fun h => hr (Subtype.ext h))
  rw [← WithZero.exp_log hnz, WithZero.exp_le_exp] at hrv hrv'
  have he : WithZero.log (v.valuation F (r : F)) = -(n : ℤ) := by
    push_cast at hrv'
    omega
  rw [← WithZero.exp_log hnz, he]

theorem generator_completion_valuation (S : Finset (HeightOneSpectrum (𝓞 F)))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (r : (S : Set (HeightOneSpectrum (𝓞 F))).integer F) (hr : r ≠ 0)
    (hspan : Ideal.span {r} = Ideal.map (algebraMap (𝓞 F) _) I)
    (a : Fˣ) (ha : (a : F) = (r : F))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    Valued.v (algebraMap F (v.adicCompletion F) (a : F)) =
      WithZero.exp (-(idealPrimeExponent v.asIdeal I : ℤ)) := by
  change Valued.v ((a : F) : v.adicCompletion F) = _
  rw [HeightOneSpectrum.adicCompletion.valued_coe, ha]
  exact generator_valuation S I hI r hr hspan v hv

end
end DedekindZetaZeroFree.SIntegerLocalization

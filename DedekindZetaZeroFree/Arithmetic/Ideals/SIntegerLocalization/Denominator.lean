module

public import ClassFieldTheory.AlgebraicNumberTheory.SUnit.Rank

@[expose] public section

open scoped NumberField Classical WithZero nonZeroDivisors
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SIntegerLocalization
noncomputable section
variable {F : Type} [Field F] [NumberField F]

theorem exists_denominator (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ t : 𝓞 F, Ideal.span {t} = (∏ v ∈ S, v.asIdeal) ^ classNumber F := by
  have hg (v : S) : ∃ t : 𝓞 F,
      Ideal.span {t} = v.val.asIdeal ^ classNumber F := by
    letI := SUnitGroup.primeIdealPower_classNumber_isPrincipal (K := F) S v
    exact ⟨Submodule.IsPrincipal.generator _, Ideal.span_singleton_generator _⟩
  choose g hspan using hg
  refine ⟨∏ v : S, g v, ?_⟩
  rw [← Finset.prod_pow]
  rw [← Finset.prod_coe_sort (s := S) (f := fun v => v.asIdeal ^ classNumber F)]
  simp_rw [← hspan]
  classical
  let f : (𝓞 F) →* Ideal (𝓞 F) :=
    { toFun := fun x => Ideal.span {x}
      map_one' := by simp
      map_mul' := fun x y => (Ideal.span_singleton_mul_span_singleton x y).symm }
  exact map_prod f _ _

def denominator (S : Finset (HeightOneSpectrum (𝓞 F))) : 𝓞 F :=
  (exists_denominator S).choose

theorem span_denominator (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Ideal.span {denominator S} = (∏ v ∈ S, v.asIdeal) ^ classNumber F :=
  (exists_denominator S).choose_spec

theorem denominator_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F))) :
    denominator S ≠ 0 := by
  apply Ideal.span_singleton_eq_bot.not.mp
  rw [span_denominator]
  exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun v _ => v.ne_bot)

theorem denominator_mem_iff (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) : denominator S ∈ v.asIdeal ↔ v ∈ S := by
  rw [← Ideal.span_singleton_le_iff_mem, span_denominator,
    v.isPrime.pow_le_iff (classNumber_pos F).ne', v.isPrime.prod_le]
  constructor
  · rintro ⟨w, hw, hle⟩
    have heq := w.isMaximal.eq_of_le v.isPrime.ne_top hle
    have : w = v := HeightOneSpectrum.ext heq
    exact this ▸ hw
  · intro hv
    exact ⟨v, hv, le_rfl⟩

theorem valuation_denominator_eq_one (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    v.valuation F (algebraMap (𝓞 F) F (denominator S)) = 1 := by
  exact v.valuation_eq_one_iff_notMem.mpr (fun h => hv ((denominator_mem_iff S v).mp h))

theorem valuation_denominator_lt_one (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ S) :
    v.valuation F (algebraMap (𝓞 F) F (denominator S)) < 1 := by
  exact (v.valuation_lt_one_iff_mem (K := F) _).mpr ((denominator_mem_iff S v).mpr hv)

end
end DedekindZetaZeroFree.SIntegerLocalization

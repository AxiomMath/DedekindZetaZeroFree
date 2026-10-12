module

public import DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerLocalization.LocalizationAway
public import Mathlib.NumberTheory.NumberField.Ideal.Basic

@[expose] public section

open scoped NumberField Classical WithZero nonZeroDivisors
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SIntegerLocalization
noncomputable section
variable {F : Type} [Field F] [NumberField F]

private theorem mem_of_mul_mem_of_sup_span_eq_top (I : Ideal (𝓞 F))
    (t x : 𝓞 F) (hc : I ⊔ Ideal.span {t} = ⊤) (hx : t * x ∈ I) : x ∈ I := by
  have h1 : (1 : 𝓞 F) ∈ I ⊔ Ideal.span {t} := by rw [hc]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hb
  have hmem := I.add_mem (I.mul_mem_right x ha) (I.mul_mem_left c hx)
  have heq : a * x + c * (t * x) = x := by
    calc
      a * x + c * (t * x) = (a + t * c) * x := by ring
      _ = x := by rw [hab, one_mul]
  exact heq ▸ hmem

theorem under_map_exterior (S : Finset (HeightOneSpectrum (𝓞 F)))
    (I : Ideal (𝓞 F)) (hI : I ⊔ (∏ v ∈ S, v.asIdeal) = ⊤) :
    (Ideal.map (algebraMap (𝓞 F) ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) I).under (𝓞 F) = I := by
  letI := isLocalization_away S
  apply le_antisymm _ Ideal.le_comap_map
  intro x hx
  change algebraMap (𝓞 F) _ x ∈ Ideal.map (algebraMap (𝓞 F) _) I at hx
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers (denominator S))] at hx
  obtain ⟨m, ⟨n, rfl⟩, hm⟩ := hx
  apply mem_of_mul_mem_of_sup_span_eq_top I _ x _ hm
  rw [← Ideal.span_singleton_pow, span_denominator, ← pow_mul]
  exact Ideal.sup_pow_eq_top hI

theorem under_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F)))
    (J : Ideal ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) (hJ : J ≠ ⊥) :
    J.under (𝓞 F) ≠ ⊥ := by
  letI := isLocalization_away S
  intro h
  have hh := IsLocalization.map_under (Submonoid.powers (denominator S)) _ J
  rw [h, Ideal.map_bot] at hh
  exact hJ hh.symm

theorem under_exterior (S : Finset (HeightOneSpectrum (𝓞 F)))
    (J : Ideal ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) (hJ : J ≠ ⊥) :
    J.under (𝓞 F) ⊔ (∏ v ∈ S, v.asIdeal) = ⊤ := by
  letI := isLocalization_away S
  let I := J.under (𝓞 F)
  letI : Finite ((𝓞 F) ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient (under_ne_zero S J hJ)
  have hs (x : 𝓞 F) (hx : denominator S * x ∈ I) : x ∈ I := by
    change algebraMap (𝓞 F) _ x ∈ J
    change algebraMap (𝓞 F) _ (denominator S * x) ∈ J at hx
    rw [map_mul] at hx
    exact (J.unit_mul_mem_iff_mem (IsLocalization.Away.algebraMap_isUnit (denominator S))).mp hx
  have hu : IsUnit (Ideal.Quotient.mk I (denominator S)) := by
    apply IsRightRegular.isUnit_of_finite
    intro x y h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply hs
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    rw [map_mul, map_sub, mul_sub, sub_eq_zero]
    simpa only [mul_comm] using h
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hmem : 1 - denominator S * a ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_one, map_mul, hb, sub_self]
  have htop : I ⊔ Ideal.span {denominator S} = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have ha : denominator S * a ∈ Ideal.span {denominator S} :=
      Ideal.mem_span_singleton.mpr ⟨a, rfl⟩
    have := Submodule.add_mem_sup hmem ha
    simpa using this
  apply top_unique
  rw [← htop, span_denominator S]
  exact sup_le_sup_left (Ideal.pow_le_self (classNumber_pos F).ne') _

end
end DedekindZetaZeroFree.SIntegerLocalization

module

public import DedekindZetaZeroFree.ZeroDetection.Conductors.FrequencyLocalComponents
public import DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerPrincipalIdealIndex

@[expose] public section

open scoped NumberField
open IsDedekindDomain

namespace DedekindZetaZeroFree.Detector.Conductor.RadicalQuotient

 noncomputable def valuationIdeal (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) : Ideal (S.integer F) where
  carrier := {a | v.valuation F (a : F) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change v.valuation F ((x : F) + (y : F)) < 1
    exact lt_of_le_of_lt (ValuationClass.map_add_le_max _ _ _) (max_lt hx hy)
  smul_mem' := by
    intro x y hy
    change v.valuation F ((x : F) * (y : F)) < 1
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (x.property v hv) zero_le)
      (by simpa using hy)

private lemma valuationIdeal_prime (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    (valuationIdeal F S v hv).IsPrime := by
  constructor
  · intro h
    have hh : (1 : S.integer F) ∈ valuationIdeal F S v hv := by rw [h]; trivial
    change v.valuation F (1 : F) < 1 at hh
    simpa using hh
  · intro x y hxy
    change v.valuation F ((x : F) * (y : F)) < 1 at hxy
    change v.valuation F (x : F) < 1 ∨ v.valuation F (y : F) < 1
    by_contra h
    have h' := not_or.mp h
    have hx : v.valuation F (x : F) = 1 := le_antisymm (x.property v hv) (le_of_not_gt h'.1)
    have hy : v.valuation F (y : F) = 1 := le_antisymm (y.property v hv) (le_of_not_gt h'.2)
    simpa [map_mul, hx, hy] using hxy

private lemma valuationIdeal_comap (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    Ideal.comap (algebraMap (𝓞 F) (S.integer F)) (valuationIdeal F S v hv) = v.asIdeal := by
  ext r
  change v.valuation F (algebraMap (𝓞 F) (S.integer F) r : F) < 1 ↔ r ∈ v.asIdeal
  change v.valuation F (r : F) < 1 ↔ r ∈ v.asIdeal
  exact v.valuation_lt_one_iff_mem r

theorem exterior_prime_product_le_radical_index
    (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    [IsPrincipalIdealRing (S.integer F)]
    (a : S.integer F) (ha : a ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ v ∈ T, v ∉ S ∧ v.valuation F (a : F) < 1) :
    (∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ)) ≤
      (Nat.card ((S.integer F) ⧸ (Ideal.span {a}).radical) : ℝ) := by
  classical
  let R := S.integer F
  let J : Ideal R := (Ideal.span {a}).radical
  let I : Ideal (𝓞 F) := Ideal.comap (algebraMap (𝓞 F) R) J
  have hfinite : Finite (R ⧸ Ideal.span {a}) := by
    obtain ⟨Sf, hSf⟩ := hS.exists_finset_coe
    subst S
    exact (sProductModulus_eq_principalIdeal_index F Sf a ha).1
  have hfiniteJ : Finite (R ⧸ J) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective
      (Ideal.le_radical (I := Ideal.span {a})))
  letI := hfiniteJ
  have hIJ : Nat.card ((𝓞 F) ⧸ I) ≤ Nat.card (R ⧸ J) :=
    Nat.card_le_card_of_injective _ (Ideal.quotientMap_injective (f := algebraMap (𝓞 F) R) (I := J))
  have hIp : ∀ v ∈ T, I ≤ v.asIdeal := by
    intro v hv
    have hvS := (hT v hv).1
    have hle : Ideal.span {a} ≤ valuationIdeal F S v hvS := by
      rw [Ideal.span_le]
      intro x hx
      have heq : x = a := Set.mem_singleton_iff.mp hx
      subst x
      exact (hT v hv).2
    have hr : J ≤ valuationIdeal F S v hvS :=
      (valuationIdeal_prime F S v hvS).radical_le_iff.mpr hle
    exact (Ideal.comap_mono hr).trans_eq (valuationIdeal_comap F S v hvS)
  let P : T → Ideal (𝓞 F) := fun v => v.val.asIdeal
  have hpair : Pairwise (fun v w => IsCoprime (P v) (P w)) := by
    intro v w hn
    rw [Ideal.isCoprime_iff_sup_eq]
    exact v.val.isMaximal.coprime_of_ne w.val.isMaximal
      (fun h => hn (Subtype.ext (HeightOneSpectrum.ext h)))
  have hprod : (∏ v : T, P v) = ⨅ v : T, P v := by
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := Finset.univ) (J := P) (fun v _ w _ hn => hpair hn)
  have hPI : (∏ v : T, P v) ≥ I := by
    rw [hprod]
    exact le_iInf fun v => hIp v.val v.property
  have hdiv : Ideal.absNorm (∏ v : T, P v) ∣ Ideal.absNorm I :=
    Ideal.absNorm_dvd_absNorm_of_le hPI
  have hnorm : Ideal.absNorm (∏ v : T, P v) ≤ Nat.card (R ⧸ J) := by
    calc
      _ ≤ Ideal.absNorm I := Nat.le_of_dvd (by
        letI : Finite ((𝓞 F) ⧸ I) := Finite.of_injective _
          (Ideal.quotientMap_injective (f := algebraMap (𝓞 F) R) (I := J))
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
        exact Nat.card_pos) hdiv
      _ = Nat.card ((𝓞 F) ⧸ I) := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      _ ≤ _ := hIJ
  simpa only [map_prod, Finset.prod_coe_sort, Nat.cast_prod, P, R, J] using
    (show (Ideal.absNorm (∏ v : T, P v) : ℝ) ≤ (Nat.card (R ⧸ J) : ℝ) from
      Nat.cast_le.mpr hnorm)

end DedekindZetaZeroFree.Detector.Conductor.RadicalQuotient

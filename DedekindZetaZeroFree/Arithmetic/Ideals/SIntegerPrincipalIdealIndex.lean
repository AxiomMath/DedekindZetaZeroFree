module

public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.ProductFormula

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

open NumberField IsDedekindDomain WithZero

private theorem simultaneous_integer_approximation
    (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (RingOfIntegers F))) (x : F)
    (hx : ∀ v ∈ T, v.valuation F x ≤ 1)
    (e : HeightOneSpectrum (RingOfIntegers F) → ℕ) :
    ∃ r : RingOfIntegers F, ∀ v ∈ T,
      v.valuation F ((r : F) - x) ≤ WithZero.exp (-(e v : ℤ)) := by
  classical
  have hl : ∀ v : T, ∃ r : RingOfIntegers F,
      v.val.valuation F ((r : F) - x) < WithZero.exp (-(e v.val : ℤ)) := by
    intro v
    exact v.val.exists_valuation_sub_lt_of_integer (hx v.val v.property)
      (Units.mk0 (WithZero.exp (-(e v.val : ℤ))) WithZero.coe_ne_zero)
  choose r hr using hl
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (fun v : HeightOneSpectrum (RingOfIntegers F) => v.asIdeal) e
    (fun v _ => v.prime) (fun v _ w _ h => fun hvw => h (HeightOneSpectrum.ext hvw)) r
  refine ⟨b, fun v hv => ?_⟩
  have hbr : v.valuation F ((b : F) - (r ⟨v, hv⟩ : F)) ≤ WithZero.exp (-(e v : ℤ)) := by
    rw [← map_sub (algebraMap (RingOfIntegers F) F), v.valuation_of_algebraMap]
    exact (v.intValuation_le_pow_iff_mem _ _).mpr (hb v hv)
  have hadd := (v.valuation F).map_add ((b : F) - (r ⟨v, hv⟩ : F))
    ((r ⟨v, hv⟩ : F) - x)
  rw [sub_add_sub_cancel] at hadd
  exact hadd.trans (max_le hbr (hr ⟨v, hv⟩).le)

private theorem span_singleton_mem_iff_valuations
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (a y : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F)
    (ha : a ≠ 0) :
    y ∈ Ideal.span {a} ↔ ∀ v ∉ S, v.valuation F (y : F) ≤ v.valuation F (a : F) := by
  have haF : (a : F) ≠ 0 := by exact_mod_cast ha
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨z, rfl⟩ v hv
    change v.valuation F ((a : F) * (z : F)) ≤ _
    rw [map_mul]
    simpa [mul_comm] using mul_le_mul_left (z.property v hv) (v.valuation F (a : F))
  · intro hy
    have hz : ((y : F) / (a : F)) ∈ (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F := by
      intro v hv
      rw [map_div₀]
      exact (div_le_one₀ ((Valuation.ne_zero_iff _).mpr haF).bot_lt).mpr (hy v hv)
    refine ⟨⟨(y : F) / (a : F), hz⟩, ?_⟩
    apply Subtype.ext
    exact (mul_div_cancel₀ _ haF).symm

private theorem valuation_eq_exp_neg_toNat
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) (a : F) (ha : a ≠ 0)
    (hv : v.valuation F a ≤ 1) :
    v.valuation F a = WithZero.exp (-((-WithZero.log (v.valuation F a)).toNat : ℤ)) := by
  have hn : v.valuation F a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  have hlog : WithZero.log (v.valuation F a) ≤ 0 := by
    have h := (WithZero.exp_le_exp).mp (show WithZero.exp (WithZero.log (v.valuation F a)) ≤ WithZero.exp (0 : ℤ) by simpa [WithZero.exp_log hn] using hv)
    exact h
  rw [Int.toNat_of_nonneg (neg_nonneg.mpr hlog), neg_neg, WithZero.exp_log hn]

private theorem finite_valuation_mulSupport
    (F : Type) [Field F] [NumberField F] (a : F) (ha : a ≠ 0) :
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (RingOfIntegers F) => v.valuation F a) := by
  have hfin := (FinitePlace.hasFiniteMulSupport ha).comp_of_injective
    (FinitePlace.equivHeightOneSpectrum.symm.injective)
  apply hfin.subset
  intro v hv
  change FinitePlace.mk v a ≠ 1
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding']
  intro h
  apply hv
  have h' : (WithZeroMulInt.toNNReal (e := (Ideal.absNorm v.asIdeal : NNReal)) (ne_of_gt (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)))) (v.valuation F a) = 1 := by exact_mod_cast h
  exact (WithZeroMulInt.toNNReal_eq_one_iff _ _ (ne_of_gt ((NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)))).mp h'

private theorem principal_quotient_comap_surjective
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (a : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F)
    (ha : a ≠ 0) :
    Function.Surjective (Ideal.quotientMap (Ideal.span {a})
      (algebraMap (RingOfIntegers F) ((S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F)) le_rfl) := by
  classical
  let R := (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F
  have haF : (a : F) ≠ 0 := by exact_mod_cast ha
  let T := (finite_valuation_mulSupport F (a : F) haF).toFinset \ S
  let e := fun v : HeightOneSpectrum (RingOfIntegers F) => (-WithZero.log (v.valuation F (a : F))).toNat
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨r, hr⟩ := simultaneous_integer_approximation F T (x : F)
    (fun v hv => x.property v (Finset.mem_sdiff.mp hv).2) e
  refine ⟨Ideal.Quotient.mk _ r, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  apply (span_singleton_mem_iff_valuations F S a _ ha).mpr
  intro v hv
  change v.valuation F ((r : F) - (x : F)) ≤ _
  by_cases hval : v.valuation F (a : F) = 1
  · rw [hval]
    exact (v.valuation F).map_sub_le (v.valuation_le_one r) (x.property v hv)
  · have hvT : v ∈ T := Finset.mem_sdiff.mpr ⟨(Set.Finite.mem_toFinset _).mpr hval, hv⟩
    rw [valuation_eq_exp_neg_toNat F v (a : F) haF (a.property v hv)]
    exact hr v hvT

private theorem comap_principal_eq_product
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (a : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F)
    (ha : a ≠ 0) :
    Ideal.comap (algebraMap (RingOfIntegers F) ((S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F)) (Ideal.span {a}) =
      (by classical exact ∏ v ∈ (finite_valuation_mulSupport F (a : F) (by exact_mod_cast ha)).toFinset \ S,
        v.asIdeal ^ (-WithZero.log (v.valuation F (a : F))).toNat) := by
  classical
  have haF : (a : F) ≠ 0 := by exact_mod_cast ha
  let T := (finite_valuation_mulSupport F (a : F) haF).toFinset \ S
  let e := fun v : HeightOneSpectrum (RingOfIntegers F) => (-WithZero.log (v.valuation F (a : F))).toNat
  have hp : (T : Set (HeightOneSpectrum (RingOfIntegers F))).Pairwise
      (fun v w => IsCoprime (v.asIdeal ^ e v) (w.asIdeal ^ e w)) := by
    intro v hv w hw hne
    apply IsCoprime.pow
    rw [Ideal.isCoprime_iff_sup_eq]
    exact v.isMaximal.coprime_of_ne w.isMaximal (fun h => hne (HeightOneSpectrum.ext h))
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hp]
  ext r
  rw [Ideal.mem_comap, span_singleton_mem_iff_valuations F S a _ ha]
  simp only [Ideal.mem_iInf]
  constructor
  · intro hr v hv
    have hn := (Finset.mem_sdiff.mp hv).2
    apply (v.intValuation_le_pow_iff_mem _ _).mp
    have hr' := hr v hn
    change v.valuation F (r : F) ≤ v.valuation F (a : F) at hr'
    rw [v.valuation_of_algebraMap] at hr'
    rw [valuation_eq_exp_neg_toNat F v (a : F) haF (a.property v hn)] at hr'
    exact hr'
  · intro hr v hv
    by_cases hval : v.valuation F (a : F) = 1
    · rw [hval]
      exact v.valuation_le_one r
    · have hvT : v ∈ T := Finset.mem_sdiff.mpr ⟨(Set.Finite.mem_toFinset _).mpr hval, hv⟩
      rw [valuation_eq_exp_neg_toNat F v (a : F) haF (a.property v hv)]
      have hr' := (v.intValuation_le_pow_iff_mem _ _).mpr (hr v hvT)
      change v.valuation F (r : F) ≤ _
      rw [v.valuation_of_algebraMap]
      exact hr'

private theorem place_mul_norm_power
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) (a : F) (ha : a ≠ 0)
    (hv : v.valuation F a ≤ 1) :
    FinitePlace.mk v a * (Ideal.absNorm v.asIdeal : ℝ) ^
      (-WithZero.log (v.valuation F a)).toNat = 1 := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding']
  rw [WithZeroMulInt.toNNReal_neg_apply _ ((Valuation.ne_zero_iff _).mpr ha)]
  have hlog : WithZero.log (v.valuation F a) = -((-WithZero.log (v.valuation F a)).toNat : ℤ) := by
    conv_lhs => rw [valuation_eq_exp_neg_toNat F v a ha hv, WithZero.log_exp]
  conv_lhs => lhs; rw [hlog]
  simp only [NNReal.coe_zpow, NNReal.coe_natCast, zpow_neg, zpow_natCast]
  have hn : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by exact_mod_cast
    (ne_of_gt (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)))
  exact inv_mul_cancel₀ (pow_ne_zero _ hn)

private theorem quotient_card_eq_comap_norm
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (a : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F)
    (ha : a ≠ 0) :
    Finite (((S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F) ⧸ Ideal.span {a}) ∧
    Nat.card (((S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F) ⧸ Ideal.span {a}) =
      Ideal.absNorm (Ideal.comap
        (algebraMap (RingOfIntegers F) ((S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F)) (Ideal.span {a})) := by
  classical
  let I := Ideal.comap
    (algebraMap (RingOfIntegers F) ((S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F)) (Ideal.span {a})
  have hI : I ≠ ⊥ := by
    change Ideal.comap _ (Ideal.span {a}) ≠ ⊥
    rw [comap_principal_eq_product F S a ha]
    exact Finset.prod_ne_zero_iff.mpr (fun v hv => pow_ne_zero _ v.ne_bot)
  letI : Finite ((RingOfIntegers F) ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hI
  let eqv := RingEquiv.ofBijective (Ideal.quotientMap (Ideal.span {a})
    (algebraMap (RingOfIntegers F) ((S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F)) le_rfl)
    ⟨Ideal.quotientMap_injective, principal_quotient_comap_surjective F S a ha⟩
  refine ⟨Finite.of_equiv _ eqv.toEquiv, ?_⟩
  rw [← Nat.card_congr eqv.toEquiv, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem sProductModulus_eq_principalIdeal_index
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (a : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F)
    (ha : a ≠ 0) :
    Finite (((S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F) ⧸
      Ideal.span ({a} : Set ((S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F))) ∧
    (∏ v : InfinitePlace F, v (a : F) ^ v.mult) *
      (∏ v ∈ S, FinitePlace.mk v (a : F)) =
      (Nat.card (((S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F) ⧸
        Ideal.span ({a} : Set ((S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F))) : ℝ) := by
  classical
  obtain ⟨hfinite, hcard⟩ := quotient_card_eq_comap_norm F S a ha
  refine ⟨hfinite, ?_⟩
  rw [hcard, comap_principal_eq_product F S a ha]
  have haF : (a : F) ≠ 0 := by exact_mod_cast ha
  let T₀ := (finite_valuation_mulSupport F (a : F) haF).toFinset
  let T := T₀ \ S
  let N := ∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ) ^ (-WithZero.log (v.valuation F (a : F))).toNat
  simp only [map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
  change _ = N
  have hfull : (∏ᶠ w : FinitePlace F, w (a : F)) =
      (∏ v ∈ S, FinitePlace.mk v (a : F)) * ∏ v ∈ T, FinitePlace.mk v (a : F) := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    change (∏ᶠ v : HeightOneSpectrum (RingOfIntegers F), FinitePlace.mk v (a : F)) = _
    rw [finprod_eq_prod_of_mulSupport_subset (s := S ∪ T)]
    · rw [Finset.prod_union Finset.disjoint_sdiff]
    · intro v hv
      have hval : v.valuation F (a : F) ≠ 1 := by
        intro h
        apply hv
        change FinitePlace.mk v (a : F) = 1
        rw [FinitePlace.mk_apply, FinitePlace.norm_embedding', h]
        simp
      have hv₀ : v ∈ T₀ := (Set.Finite.mem_toFinset _).mpr hval
      by_cases hvS : v ∈ S
      · exact Finset.mem_union_left _ hvS
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv₀, hvS⟩)
  have hTN : (∏ v ∈ T, FinitePlace.mk v (a : F)) * N = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro v hv
    exact place_mul_norm_power F v (a : F) haF (a.property v (Finset.mem_sdiff.mp hv).2)
  have hprod := NumberField.prod_abs_eq_one haF
  rw [hfull, ← mul_assoc] at hprod
  apply mul_right_cancel₀ (left_ne_zero_of_mul (hTN.trans_ne one_ne_zero))
  rw [hprod, mul_comm N, hTN]

end DedekindZetaZeroFree

end

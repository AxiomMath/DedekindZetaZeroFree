module

public import DedekindZetaZeroFree.Arithmetic.Ideals.SSupportedDenominators
public import DedekindZetaZeroFree.Adeles.Approximation.IntegralLocalCongruences
public import ClassFieldTheory.AlgebraicNumberTheory.SUnit.Rank
public import DedekindZetaZeroFree.Adeles.Characters.CompactCoordinateAnnihilators

@[expose] public section

section

noncomputable section
open scoped Classical nonZeroDivisors
open NumberField IsDedekindDomain Topology Filter

namespace DedekindZetaZeroFree.PoissonFinite.BallExpansion

section Helpers

variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
set_option quotPrecheck false
local notation "X" => ((v : S) → v.val.adicCompletion F)
private lemma small {s : Set X} (hs : s ∈ 𝓝 (0 : X)) :
    ∃ k : S → ℤ, {x : X | ∀ v, Valued.v (x v) ≤ WithZero.exp (-k v)} ⊆ s := by
  rw [nhds_pi] at hs
  obtain ⟨I, t, ht, hts⟩ := Filter.mem_pi'.mp hs
  have hh (v : S) : ∃ k : ℤ, {x : v.val.adicCompletion F | Valued.v x ≤ WithZero.exp (-k)} ⊆ t v := by
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp (ht v)
    have hn : MonoidWithZeroHom.ValueGroup₀.embedding γ.val ≠ 0 := by
      simpa using γ.ne_zero
    obtain ⟨n, hn'⟩ := WithZero.exists_exp_neg_natCast_lt hn
    refine ⟨n, fun x hx => hγ ?_⟩
    rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact hx.trans_lt hn'
  choose k hk using hh
  exact ⟨k, fun x hx => hts (fun v _ => hk v (hx v))⟩
private lemma openBall (k : S → ℤ) (b : X) :
    IsOpen {x : X | ∀ v, Valued.v (x v - b v) ≤ WithZero.exp (-k v)} := by
  have ho (v : S) : IsOpen {x : v.val.adicCompletion F | Valued.v x ≤ WithZero.exp (-k v)} := by
    obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v.val (WithZero.exp (-k v))
    have hn : (Valued.v.restrict a) ≠ 0 := by
      intro h
      have ha0 : a = 0 := (Valued.v.restrict.map_eq_zero_iff).mp h
      exact WithZero.exp_ne_zero (ha.symm.trans (by simp [ha0]))
    convert Valued.isOpen_closedBall (v.val.adicCompletion F) hn using 1
    ext x
    simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff, ha]
  convert isOpen_iInter_of_finite (fun v : S => (ho v).preimage (by fun_prop : Continuous (fun x : X => x v - b v))) using 1
  ext x
  simp
private lemma uniform (φ : X → ℂ) (hl : IsLocallyConstant φ) (hc : HasCompactSupport φ) :
    ∃ k : S → ℤ, ∀ x y : X, (∀ v, Valued.v (x v - y v) ≤ WithZero.exp (-k v)) → φ x = φ y := by
  letI : UniformSpace ℂ := ⊥
  letI : TopologicalSpace ℂ := (inferInstance : UniformSpace ℂ).toTopologicalSpace
  have hu : UniformContinuous φ := hc.uniformContinuous_of_continuous hl.continuous
  have hd : {p : ℂ × ℂ | p.1 = p.2} ∈ uniformity ℂ := by
    change _ ∈ 𝓟 (Set.diagonal ℂ)
    exact Set.Subset.rfl
  have he := uniformContinuous_def.mp hu _ hd
  rw [uniformity_eq_comap_nhds_zero X] at he
  obtain ⟨s, hs, hse⟩ := Filter.mem_comap.mp he
  obtain ⟨k, hk⟩ := small F S hs
  refine ⟨k, fun x y h => ?_⟩
  have hh : (x, y) ∈ (fun p : X × X => p.2 - p.1) ⁻¹' s :=
    hk (fun v => by simpa only [Pi.sub_apply, Valuation.map_sub_swap] using h v)
  exact hse hh
private lemma transBall (k : S → ℤ) (x y z : X)
    (hxy : ∀ v, Valued.v (x v - y v) ≤ WithZero.exp (-k v))
    (hyz : ∀ v, Valued.v (y v - z v) ≤ WithZero.exp (-k v)) :
    ∀ v, Valued.v (x v - z v) ≤ WithZero.exp (-k v) := by
  intro v
  rw [show x v - z v = (x v - y v) + (y v - z v) by ring]
  exact (Valued.v.map_add _ _).trans (max_le (hxy v) (hyz v))

end Helpers

theorem exists_uniform_ball_expansion
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (φ : ((v : S) → v.val.adicCompletion F) → ℂ) (hlocal : IsLocallyConstant φ)
    (hsupport : HasCompactSupport φ) :
    ∃ (k : S → ℤ) (n : ℕ) (b : Fin n → ((v : S) → v.val.adicCompletion F)) (c : Fin n → ℂ),
      ∀ x : ((v : S) → v.val.adicCompletion F),
        φ x = ∑ j, c j *
          (if ∀ v : S,
            (Valued.v (x v - b j v) : WithZero (Multiplicative ℤ)) ≤
              WithZero.exp (-k v) then (1 : ℂ) else 0) := by
  obtain ⟨k, hk⟩ := uniform F S φ hlocal hsupport
  let r : Setoid ((v : S) → v.val.adicCompletion F) :=
    { r := fun x y => ∀ v : S, Valued.v (x v - y v) ≤ WithZero.exp (-k v)
      iseqv := ⟨fun x v => by simp,
        fun h v => by rw [Valuation.map_sub_swap]; exact h v,
        fun h₁ h₂ => transBall F S k _ _ _ h₁ h₂⟩ }
  let q : ((v : S) → v.val.adicCompletion F) → Quotient r := Quotient.mk r
  letI : TopologicalSpace (Quotient r) := ⊥
  letI : DiscreteTopology (Quotient r) := discreteTopology_bot _
  have hql : IsLocallyConstant q := by
    apply IsLocallyConstant.iff_isOpen_fiber_apply.mpr
    intro x
    convert openBall F S k x using 1
    ext y
    exact Quotient.eq
  have hf : (q '' tsupport φ).Finite :=
    isCompact_iff_finite.mp (hsupport.image hql.continuous)
  let t := hf.toFinset
  have hmem (x : ((v : S) → v.val.adicCompletion F)) (hx : φ x ≠ 0) : q x ∈ t := by
    exact hf.mem_toFinset.mpr ⟨x, subset_tsupport φ hx, rfl⟩
  have heq (x : ((v : S) → v.val.adicCompletion F)) (j : Quotient r) :
      (∀ v : S, Valued.v (x v - j.out v) ≤ WithZero.exp (-k v)) ↔ q x = j := by
    change r.r x j.out ↔ _
    rw [← Quotient.eq]
    change q x = Quotient.mk r j.out ↔ q x = j
    rw [Quotient.out_eq]
  have hsum (x : ((v : S) → v.val.adicCompletion F)) : φ x = ∑ j : t, φ j.val.out *
      (if ∀ v : S, Valued.v (x v - j.val.out v) ≤ WithZero.exp (-k v) then (1 : ℂ) else 0) := by
    simp_rw [heq]
    by_cases hx : q x ∈ t
    · let j : t := ⟨q x, hx⟩
      rw [Finset.sum_eq_single j]
      · simp only [j, ↓reduceIte, mul_one]
        exact hk x (q x).out ((heq x (q x)).mpr rfl)
      · intro i _ hij
        have hne : q x ≠ i.val := by
          intro hi
          apply hij
          exact Subtype.ext hi.symm
        simp [hne]
      · simp
    · have hz : φ x = 0 := by
        by_contra h
        exact hx (hmem x h)
      rw [hz]
      symm
      apply Finset.sum_eq_zero
      intro j _
      have hne : q x ≠ j.val := fun h => hx (h.symm ▸ j.property)
      simp [hne]
  let e := (Fintype.equivFin t).symm
  refine ⟨k, Fintype.card t, fun j => (e j).val.out, fun j => φ (e j).val.out, fun x => ?_⟩
  rw [hsum x]
  exact (Equiv.sum_comp e _).symm

end DedekindZetaZeroFree.PoissonFinite.BallExpansion

end

end

section

noncomputable section
open scoped Classical nonZeroDivisors
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PoissonFinite.BallExpansion

private theorem le_of_counts (F : Type) [Field F] [NumberField F]
    (I J : FractionalIdeal (RingOfIntegers F)⁰ F) (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v, FractionalIdeal.count F v J ≤ FractionalIdeal.count F v I) : I ≤ J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' F hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' F hJ]
  have hs (A : FractionalIdeal (RingOfIntegers F)⁰ F) :
      Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (RingOfIntegers F) =>
        (FractionalIdeal.coeIdeal v.asIdeal : FractionalIdeal (RingOfIntegers F)⁰ F) ^
          FractionalIdeal.count F v A) := by
    apply Set.Finite.subset (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors A))
    intro v hv hz
    exact hv (by simp [hz])
  apply finprod_le_finprod (hs I) (hs J)
  intro v
  apply zpow_le_zpow_right_of_le_one₀ _ _ (h v)
  · exact bot_lt_iff_ne_bot.mpr (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  · exact FractionalIdeal.coeIdeal_le_one

private theorem mem_iff_valuations (F : Type) [Field F] [NumberField F]
    (I : FractionalIdeal (RingOfIntegers F)⁰ F) (hI : I ≠ 0) (x : F) :
    x ∈ I ↔ ∀ v, v.valuation F x ≤ WithZero.exp (-FractionalIdeal.count F v I) := by
  by_cases hx : x = 0
  · subst x
    simp only [FractionalIdeal.zero_mem, true_iff]
    intro v
    simp
  let P := FractionalIdeal.spanSingleton (RingOfIntegers F)⁰ x
  have hP : P ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx
  have hv (v : HeightOneSpectrum (RingOfIntegers F)) :
      v.valuation F x = WithZero.exp (-FractionalIdeal.count F v P) :=
    SUnitGroup.valuation_eq_exp_neg_count (Units.mk0 x hx) v
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  constructor
  · intro h v
    rw [hv, WithZero.exp_le_exp, neg_le_neg_iff]
    exact FractionalIdeal.count_mono F v hP h
  · intro h
    apply le_of_counts F P I hP hI
    intro v
    simpa only [hv, WithZero.exp_le_exp, neg_le_neg_iff] using h v

private theorem count_ball (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : S → ℤ)
    (w : HeightOneSpectrum (RingOfIntegers F)) :
    FractionalIdeal.count F w (∏ v : S,
      (FractionalIdeal.coeIdeal v.val.asIdeal) ^ k v) =
      if h : w ∈ S then k ⟨w, h⟩ else 0 := by
  rw [FractionalIdeal.count_prod]
  · simp only [FractionalIdeal.count_zpow, FractionalIdeal.count_maximal,
      mul_ite, mul_one, mul_zero]
    by_cases h : w ∈ S
    · rw [dif_pos h]
      have he (v : S) : (v.val = w) ↔ v = ⟨w, h⟩ := by simp [Subtype.ext_iff]
      simp_rw [he]
      simp
    · rw [dif_neg h]
      apply Finset.sum_eq_zero
      intro v _
      rw [if_neg]
      intro he
      exact h (he ▸ v.property)
  · intro v _
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.val.ne_bot)

private theorem mem_ball (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : S → ℤ)
    (m : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F) :
    (m : F) ∈ (∏ v : S, (FractionalIdeal.coeIdeal v.val.asIdeal) ^ k v :
      FractionalIdeal (RingOfIntegers F)⁰ F) ↔
    ∀ v : S, v.val.valuation F (m : F) ≤ WithZero.exp (-k v) := by
  rw [mem_iff_valuations F _ (Finset.prod_ne_zero_iff.mpr (fun v _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.val.ne_bot)))]
  simp only [count_ball]
  constructor
  · intro h v
    simpa only [dif_pos v.property] using h v.val
  · intro h v
    by_cases hv : v ∈ S
    · simpa only [dif_pos hv] using h ⟨v, hv⟩
    · simpa only [dif_neg hv, neg_zero, WithZero.exp_zero] using m.property v hv

private theorem exists_ball_center (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (k : S → ℤ) (b : (v : S) → v.val.adicCompletion F) :
    ∃ a : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F,
       ∀ v : S, (Valued.v (FinitePlace.embedding v.val (a : F) - b v) : WithZero (Multiplicative ℤ)) ≤
        WithZero.exp (-k v) := by
  obtain ⟨d, hd, _, hout, hin, hclear⟩ := DedekindZetaZeroFree.sSupported_denominator F S
  obtain ⟨t, ht⟩ := hclear b k
  have hdF : (d : F) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (RingOfIntegers F) F)).mpr hd
  let y (v : S) : v.val.adicCompletionIntegers F :=
    ⟨algebraMap F (v.val.adicCompletion F) (d : F) ^ t * b v, (ht v).1⟩
  let n (v : S) : ℕ := (k v + (t : ℤ) * (multiplicity v.val.asIdeal (Ideal.span {d}) : ℤ)).toNat
  obtain ⟨a, ha⟩ := DedekindZetaZeroFree.sIntegral_crt F S y n
  have hquot : ∀ w : HeightOneSpectrum (RingOfIntegers F), w ∉ S →
      w.valuation F ((a : F) / (d : F) ^ t) ≤ 1 := by
    intro w hw
    rw [Valuation.map_div, Valuation.map_pow, w.valuation_of_algebraMap (K := F),
      w.valuation_of_algebraMap (K := F)]
    have hval : w.intValuation d = 1 := by
      by_cases ha : d = 0
      · contradiction
      · rw [w.intValuation_eq_exp_neg_multiplicity ha, hout w hw, Nat.cast_zero,
          neg_zero, WithZero.exp_zero]
    simp [hval, w.intValuation_le_one]
  let center : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F :=
    ⟨(a : F) / (d : F) ^ t, hquot⟩
  refine ⟨center, ?_⟩
  intro v
  have hv : (0 : ℤ) ≤ k v + (t : ℤ) *
      (multiplicity v.val.asIdeal (Ideal.span {d}) : ℤ) := (ht v).2
  have hn : ((n v : ℕ) : ℤ) = k v + (t : ℤ) *
      (multiplicity v.val.asIdeal (Ideal.span {d}) : ℤ) := Int.toNat_of_nonneg hv
  have hdlocal : (Valued.v (algebraMap F (v.val.adicCompletion F) (d : F)) : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-(multiplicity v.val.asIdeal (Ideal.span {d}) : ℤ)) := by
    change Valued.v (FinitePlace.embedding v.val (d : F)) = _
    rw [FinitePlace.embedding_apply, HeightOneSpectrum.adicCompletion.valued_coe,
      v.val.valuation_of_algebraMap (K := F), v.val.intValuation_eq_exp_neg_multiplicity hd]
  have hcr : (Valued.v ((y v : v.val.adicCompletion F) -
      algebraMap F (v.val.adicCompletion F) (a : F)) : WithZero (Multiplicative ℤ)) ≤
      WithZero.exp (-(n v : ℤ)) := ha v
  have hm : algebraMap F (v.val.adicCompletion F) (d : F) ^ t *
      (FinitePlace.embedding v.val (center : F) - b v) =
      algebraMap F (v.val.adicCompletion F) (a : F) - (y v : v.val.adicCompletion F) := by
    dsimp [center, y]
    change algebraMap F (v.val.adicCompletion F) (d : F) ^ t *
      (algebraMap F (v.val.adicCompletion F) ((a : F) / (d : F) ^ t) - b v) = _
    rw [map_div₀ (algebraMap F (v.val.adicCompletion F)), map_pow]
    field_simp [(map_ne_zero (algebraMap F (v.val.adicCompletion F))).mpr hdF]
  have hval := congrArg (fun z : v.val.adicCompletion F =>
      (Valued.v z : WithZero (Multiplicative ℤ))) hm
  rw [map_mul, map_pow, hdlocal] at hval
  rw [← Valuation.map_sub_swap] at hcr
  rw [hn] at hcr
  have hexp : WithZero.exp (-(k v + (t : ℤ) *
      (multiplicity v.val.asIdeal (Ideal.span {d}) : ℤ))) =
      WithZero.exp (-(multiplicity v.val.asIdeal (Ideal.span {d}) : ℤ)) ^ t *
        WithZero.exp (-k v) := by
    rw [← WithZero.exp_nsmul, ← WithZero.exp_add]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  rw [hexp, ← hval] at hcr
  exact (mul_le_mul_iff_right₀ (pow_pos (bot_lt_iff_ne_bot.mpr WithZero.exp_ne_zero) t)).mp hcr

theorem valuation_ball_fiber_eq_ideal_coset
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (k : S → ℤ) (b : ((v : S) → v.val.adicCompletion F)) :
    ∃ t : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F,
      ∀ m : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F,
        (∀ v : S,
          (Valued.v (NumberField.FinitePlace.embedding v.val (m : F) - b v) : WithZero (Multiplicative ℤ)) ≤
            WithZero.exp (-k v)) ↔
        (m : F) - (t : F) ∈
          (∏ v : S, (FractionalIdeal.coeIdeal v.val.asIdeal) ^ k v :
            FractionalIdeal (RingOfIntegers F)⁰ F) := by
  obtain ⟨t, ht⟩ := exists_ball_center F S k b
  refine ⟨t, fun m => ?_⟩
  let mt : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F := m - t
  change (∀ v : S, Valued.v (FinitePlace.embedding v.val (m : F) - b v) ≤
    WithZero.exp (-k v)) ↔ (mt : F) ∈ _
  rw [mem_ball F S k mt]
  have hval (v : S) : Valued.v (FinitePlace.embedding v.val (mt : F)) =
      v.val.valuation F (mt : F) := HeightOneSpectrum.adicCompletion.valued_coe _ _ _
  simp_rw [← hval]
  have hcoe : (mt : F) = (m : F) - (t : F) := rfl
  constructor
  · intro hm v
    have heq : FinitePlace.embedding v.val (mt : F) =
        (FinitePlace.embedding v.val (m : F) - b v) -
        (FinitePlace.embedding v.val (t : F) - b v) := by
      rw [hcoe, map_sub]; ring
    rw [heq]
    exact Valuation.map_sub_le _ (hm v) (ht v)
  · intro hm v
    have heq : FinitePlace.embedding v.val (m : F) - b v =
        FinitePlace.embedding v.val (mt : F) + (FinitePlace.embedding v.val (t : F) - b v) := by
      rw [hcoe, map_sub]; ring
    rw [heq]
    exact Valuation.map_add_le _ (hm v) (ht v)

end DedekindZetaZeroFree.PoissonFinite.BallExpansion

end

end

section

noncomputable section
open scoped Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PoissonFinite.BallExpansion

open scoped Topology
open Set

private theorem compact_support_periods {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (φ : G → ℂ) (hlocal : IsLocallyConstant φ) (hsupport : HasCompactSupport φ) :
    ∃ U : AddSubgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, ∀ x, φ (u + x) = φ x := by
  let U : AddSubgroup G :=
    { carrier := {u | ∀ x, φ (u + x) = φ x}
      zero_mem' := by simp
      add_mem' := by
        intro u v hu hv x
        rw [add_assoc, hu, hv]
      neg_mem' := by
        intro u hu x
        simpa using (hu (-u + x)).symm }
  have hn : IsOpen {p : G × G | φ (p.1 + p.2) = φ p.2} := by
    exact ((hlocal.comp_continuous (continuous_fst.add continuous_snd)).prodMk
      (hlocal.comp_continuous continuous_snd)) {q : ℂ × ℂ | q.1 = q.2}
  obtain ⟨V, W, hVo, hWo, h0V, hKW, hVW⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : G))) hsupport.isCompact hn
      (by
        intro p hp
        have hp0 : p.1 = 0 := hp.1
        change φ (p.1 + p.2) = φ p.2
        rw [hp0, zero_add])
  have h0 : (0 : G) ∈ V := h0V (by simp)
  have hN : V ∩ (fun u : G => -u) ⁻¹' V ∈ 𝓝 (0 : G) :=
    (hVo.inter (hVo.preimage continuous_neg)).mem_nhds (by simpa using And.intro h0 h0)
  have hNU : V ∩ (fun u : G => -u) ⁻¹' V ⊆ (U : Set G) := by
    intro u hu x
    by_cases hx : φ x = 0
    · by_cases hux : φ (u + x) = 0
      · rw [hx, hux]
      · have hK : u + x ∈ tsupport φ := subset_closure hux
        have heq := hVW (show (-u, u + x) ∈ V ×ˢ W from ⟨hu.2, hKW hK⟩)
        simpa using heq.symm
    · exact hVW (show (u, x) ∈ V ×ˢ W from ⟨hu.1, hKW (subset_closure hx)⟩)
  exact ⟨U, U.isOpen_of_mem_nhds (Filter.mem_of_superset hN hNU), fun _ hu => hu⟩

theorem exists_open_period_subgroup
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (φ : ((v : S) → v.val.adicCompletion F) → ℂ) (hlocal : IsLocallyConstant φ)
    (hsupport : HasCompactSupport φ) :
    ∃ U : AddSubgroup (((v : S) → v.val.adicCompletion F)), IsOpen (U : Set (((v : S) → v.val.adicCompletion F))) ∧
      ∀ u ∈ U, ∀ x : ((v : S) → v.val.adicCompletion F), φ (u + x) = φ x := by
  exact compact_support_periods φ hlocal hsupport

end DedekindZetaZeroFree.PoissonFinite.BallExpansion

end

end

section

noncomputable section
open scoped Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PoissonFinite.BallExpansion

theorem isCompact_phase_annihilator
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (hne : ∀ v, ∃ x, e v x ≠ 1)
    (U : AddSubgroup (((v : S) → v.val.adicCompletion F))) (hopen : IsOpen (U : Set (((v : S) → v.val.adicCompletion F)))) :
    IsCompact {y : ((v : S) → v.val.adicCompletion F) | ∀ u ∈ U,
      (∏ v : S, (e v (-u v * y v) : ℂ)) = 1} := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 U.zero_mem
  choose t ht using hne
  have hclosed : IsClosed {y : ((v : S) → v.val.adicCompletion F) | ∀ u ∈ U,
      (∏ v : S, (e v (-u v * y v) : ℂ)) = 1} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun u => isClosed_iInter fun _ => ?_
    apply isClosed_eq _ continuous_const
    exact continuous_finset_prod _ fun v _ =>
      (continuous_subtype_val.comp (he v)).comp
        (continuous_const.mul (continuous_apply v))
  have hcompact : IsCompact {y : ((v : S) → v.val.adicCompletion F) |
      ∀ v, y v ∈ Metric.closedBall 0 (‖t v‖ / ε)} :=
    isCompact_pi_infinite fun v => isCompact_closedBall _ _
  apply hcompact.of_isClosed_subset hclosed
  intro y hy v
  simp only [Metric.mem_closedBall, dist_zero_right]
  by_contra! hlarge
  have hyv : y v ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hlarge
    exact (not_lt_of_ge (div_nonneg (norm_nonneg _) hε.le)) hlarge
  have hsmall : ‖-t v / y v‖ < ε := by
    rw [norm_div, norm_neg]
    exact (div_lt_iff₀ (norm_pos_iff.mpr hyv)).mpr
      (by simpa only [mul_comm] using (div_lt_iff₀ hε).mp hlarge)
  have hu : Pi.single v (-t v / y v) ∈ U := by
    apply hball
    simpa only [Metric.mem_ball, dist_zero_right, Pi.norm_single] using hsmall
  have hphase := hy _ hu
  have hprod : (∏ w : S, (e w (-((Pi.single v (-t v / y v) : ((w : S) → w.val.adicCompletion F)) w) * y w) : ℂ)) =
      (e v (t v) : ℂ) := by
    rw [Finset.prod_eq_single v]
    · simp [hyv]
    · intro w _ hw
      simp [Pi.single_eq_of_ne hw]
    · simp
  rw [hprod] at hphase
  exact ht v (Circle.coe_injective (by simpa using hphase))

end DedekindZetaZeroFree.PoissonFinite.BallExpansion

end

end

section

noncomputable section
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PoissonFinite.BallExpansion

theorem finite_completion_sigmaCompact
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    SigmaCompactSpace (v.adicCompletion F) := by
  infer_instance

end DedekindZetaZeroFree.PoissonFinite.BallExpansion

end

end

section

noncomputable section
open scoped Classical nonZeroDivisors
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree
namespace PoissonFinite

variable (F : Type) [Field F] [NumberField F]

abbrev Space (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :=
  (v : S) → v.val.adicCompletion F

def diagonal (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (m : F) : Space F S :=
  fun v => NumberField.FinitePlace.embedding v.val m

def idealCosetIndicator (I : FractionalIdeal (RingOfIntegers F)⁰ F) (t m : F) : ℂ :=
  if m - t ∈ I then 1 else 0

theorem exists_ideal_coset_decomposition
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (φ : Space F S → ℂ)
    (hlocal : IsLocallyConstant φ) (hsupport : HasCompactSupport φ) :
    ∃ (I : FractionalIdeal (RingOfIntegers F)⁰ F) (n : ℕ)
      (t : Fin n → F) (c : Fin n → ℂ), I ≠ 0 ∧
      ∀ m : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F,
        φ (diagonal F S m) = ∑ j, c j * idealCosetIndicator F I (t j) m := by
  obtain ⟨k, n, b, c, hφ⟩ := BallExpansion.exists_uniform_ball_expansion F S φ hlocal hsupport
  have hfiber := fun j : Fin n => BallExpansion.valuation_ball_fiber_eq_ideal_coset F S k (b j)
  choose t ht using hfiber
  let I : FractionalIdeal (RingOfIntegers F)⁰ F :=
    ∏ v : S, (FractionalIdeal.coeIdeal v.val.asIdeal) ^ k v
  refine ⟨I, n, (fun j => (t j : F)), c, ?_, ?_⟩
  · apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    apply zpow_ne_zero
    exact FractionalIdeal.coeIdeal_ne_zero.mpr v.val.ne_bot
  · intro m
    rw [hφ]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    simp only [idealCosetIndicator, diagonal, ht j m, I]

theorem product_exists_ideal_coset_decomposition
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v)) :
    ∃ (I : FractionalIdeal (RingOfIntegers F)⁰ F) (n : ℕ)
      (t : Fin n → F) (c : Fin n → ℂ), I ≠ 0 ∧
      ∀ m : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F,
        (∏ v : S, φ v (NumberField.FinitePlace.embedding v.val m)) =
          ∑ j, c j * idealCosetIndicator F I (t j) m := by
  let ψ : Space F S → ℂ := fun x => ∏ v : S, φ v (x v)
  have hψlocal : IsLocallyConstant ψ := by
    apply (IsLocallyConstant.iff_eventually_eq ψ).2
    intro x
    have h : ∀ v : S, ∀ᶠ y in nhds x, φ v (y v) = φ v (x v) := by
      intro v
      exact ((hlocal v).comp_continuous (continuous_apply v)).eventually_eq x
    filter_upwards [Filter.eventually_all.mpr h] with y hy
    exact Finset.prod_congr rfl (fun v _ => hy v)
  have hψsupport : HasCompactSupport ψ := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_pi_infinite (fun v : S => (hsupport v).isCompact))
    intro x hx v
    apply subset_tsupport
    exact (Finset.prod_ne_zero_iff.mp hx) v (Finset.mem_univ v)
  exact exists_ideal_coset_decomposition F S ψ hψlocal hψsupport

section Fourier

local instance completionMeasurable (v : HeightOneSpectrum (RingOfIntegers F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance completionBorel (v : HeightOneSpectrum (RingOfIntegers F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def fourierIntegral (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → MeasureTheory.Measure (v.val.adicCompletion F))
    (φ : Space F S → ℂ) (y : Space F S) : ℂ :=
  ∫ x, φ x * ∏ v : S, (e v (-x v * y v) : ℂ) ∂MeasureTheory.Measure.pi μ

theorem fourierIntegral_eq_zero_of_period (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → MeasureTheory.Measure (v.val.adicCompletion F))
    [(MeasureTheory.Measure.pi μ).IsAddLeftInvariant]
    (φ : Space F S → ℂ) (u y : Space F S)
    (hu : ∀ x, φ (u + x) = φ x)
    (hne : (∏ v : S, (e v (-u v * y v) : ℂ)) ≠ 1) :
    fourierIntegral F S e μ φ y = 0 := by
  let a : ℂ := ∏ v : S, (e v (-u v * y v) : ℂ)
  have ht (x : Space F S) :
      φ (u + x) * ∏ v : S, (e v (-(u + x) v * y v) : ℂ) =
        a * (φ x * ∏ v : S, (e v (-x v * y v) : ℂ)) := by
    rw [hu x]
    have hp : (∏ v : S, (e v (-(u + x) v * y v) : ℂ)) =
        a * ∏ v : S, (e v (-x v * y v) : ℂ) := by
      simp only [Pi.add_apply, neg_add, add_mul, AddChar.map_add_eq_mul,
        Circle.coe_mul, Finset.prod_mul_distrib, a]
    rw [hp]
    ring
  have hi := MeasureTheory.integral_add_left_eq_self (μ := MeasureTheory.Measure.pi μ)
    (fun x : Space F S => φ x * ∏ v : S, (e v (-x v * y v) : ℂ)) u
  simp_rw [ht] at hi
  rw [MeasureTheory.integral_const_mul] at hi
  change a * fourierIntegral F S e μ φ y = fourierIntegral F S e μ φ y at hi
  by_contra h
  exact hne ((mul_eq_right₀ h).mp hi)

theorem fourierIntegral_add_of_support_phase (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → MeasureTheory.Measure (v.val.adicCompletion F))
    (φ : Space F S → ℂ) (u y : Space F S)
    (hu : ∀ x ∈ Function.support φ, (∏ v : S, (e v (-x v * u v) : ℂ)) = 1) :
    fourierIntegral F S e μ φ (y + u) = fourierIntegral F S e μ φ y := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  by_cases hx : φ x = 0
  · simp [hx]
  · have hp : (∏ v : S, (e v (-x v * (y + u) v) : ℂ)) =
        (∏ v : S, (e v (-x v * y v) : ℂ)) *
          ∏ v : S, (e v (-x v * u v) : ℂ) := by
      simp only [Pi.add_apply, mul_add, AddChar.map_add_eq_mul,
        Circle.coe_mul, Finset.prod_mul_distrib]
    rw [hp, hu x hx, mul_one]

theorem fourierIntegral_isLocallyConstant_of_open_phase (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → MeasureTheory.Measure (v.val.adicCompletion F))
    (φ : Space F S → ℂ) (U : AddSubgroup (Space F S))
    (hopen : IsOpen (U : Set (Space F S)))
    (hphase : ∀ u ∈ U, ∀ x ∈ Function.support φ,
      (∏ v : S, (e v (-x v * u v) : ℂ)) = 1) :
    IsLocallyConstant (fourierIntegral F S e μ φ) := by
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro y
  have hnb : {z : Space F S | z - y ∈ U} ∈ nhds y :=
    (hopen.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  filter_upwards [hnb] with z hz
  have h := fourierIntegral_add_of_support_phase F S e μ φ (z - y) y (hphase _ hz)
  simpa only [add_sub_cancel] using h

theorem fourierIntegral_hasCompactSupport_of_period (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → MeasureTheory.Measure (v.val.adicCompletion F))
    [(MeasureTheory.Measure.pi μ).IsAddLeftInvariant]
    (φ : Space F S → ℂ) (U : AddSubgroup (Space F S))
    (hperiod : ∀ u ∈ U, ∀ x, φ (u + x) = φ x)
    (hcompact : IsCompact {y : Space F S | ∀ u ∈ U,
      (∏ v : S, (e v (-u v * y v) : ℂ)) = 1}) :
    HasCompactSupport (fourierIntegral F S e μ φ) := by
  apply HasCompactSupport.of_support_subset_isCompact hcompact
  intro y hy u hu
  by_contra hne
  exact hy (fourierIntegral_eq_zero_of_period F S e μ φ u y (hperiod u hu) hne)

end Fourier

end PoissonFinite
end DedekindZetaZeroFree

end

end

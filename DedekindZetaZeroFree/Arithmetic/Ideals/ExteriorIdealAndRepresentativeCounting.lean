module

public import DedekindZetaZeroFree.Arithmetic.Kummer.FrequencyClassesAndCharacterRigidity
public import DedekindZetaZeroFree.Arithmetic.Ideals.Counting.NormSeries

@[expose] public section

section

namespace DedekindZetaZeroFree.ProbeExteriorPrincipalIdealFibers

theorem finite_preimage_card_bound {ι κ : Type*} (f : ι → κ) (M : ℕ)
    (hf : ∀ b : κ, {i : ι | f i = b}.Finite ∧ Nat.card {i : ι // f i = b} ≤ M)
    (B : Set κ) (hB : B.Finite) :
    {i : ι | f i ∈ B}.Finite ∧
      Nat.card {i : ι // f i ∈ B} ≤ M * Nat.card B := by
  classical
  have hEq : {i : ι | f i ∈ B} = ⋃ b ∈ B, {i : ι | f i = b} := by
    ext i
    simp
  have hfin : {i : ι | f i ∈ B}.Finite := by
    rw [hEq]
    exact hB.biUnion fun b _ => (hf b).1
  refine ⟨hfin, ?_⟩
  have hcard : Nat.card {i : ι // f i ∈ B} = ({i : ι | f i ∈ B} : Set ι).ncard :=
    Nat.card_coe_set_eq _
  rw [hcard, hEq]
  have h1 : (⋃ b ∈ B, {i : ι | f i = b}).ncard ≤
      ∑ b ∈ hB.toFinset, ({i : ι | f i = b} : Set ι).ncard := by
    simpa [hB.coe_toFinset] using
      Finset.set_ncard_biUnion_le hB.toFinset (fun b => {i : ι | f i = b})
  have hb : ∀ b ∈ hB.toFinset, ({i : ι | f i = b} : Set ι).ncard ≤ M := by
    intro b _
    exact (hf b).2
  have h2 : ∑ b ∈ hB.toFinset, ({i : ι | f i = b} : Set ι).ncard ≤
      ∑ _b ∈ hB.toFinset, M :=
    Finset.sum_le_sum hb
  have h3 : ∑ _b ∈ hB.toFinset, M = M * Nat.card B := by
    rw [Finset.sum_const_nat (fun _ _ => rfl), Nat.card_coe_set_eq,
      Set.ncard_eq_toFinset_card B hB, Nat.mul_comm]
  exact h1.trans (h2.trans h3.le)

end DedekindZetaZeroFree.ProbeExteriorPrincipalIdealFibers

end

section

noncomputable section
open scoped NumberField Classical WithZero NNReal
open IsDedekindDomain

namespace DedekindZetaZeroFree.ProbeExteriorPrincipalIdealFibers

variable (F : Type) [Field F] [NumberField F]

def exteriorPrincipalIdeal (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ) :
    Ideal (𝓞 F) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F),
    if v ∈ S then (⊤ : Ideal (𝓞 F))
    else v.asIdeal ^ (-WithZero.log (v.valuation F (x : F))).toNat

private theorem localNorm (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ)
    (hx : (x : F) ∈ (S : Set (HeightOneSpectrum (𝓞 F))).integer F)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    idealNorm (v.asIdeal ^ (-WithZero.log (v.valuation F (x : F))).toNat) =
      (NumberField.FinitePlace.mk v (x : F))⁻¹ := by
  have h0 := (v.valuation F).ne_zero_iff.mpr x.ne_zero
  have hl : WithZero.log (v.valuation F (x : F)) ≤ 0 := by
    simpa using (WithZero.log_le_log h0 (one_ne_zero : (1 : ℤᵐ⁰) ≠ 0)).mpr (hx v hv)
  have hn : ((-WithZero.log (v.valuation F (x : F))).toNat : ℤ) =
      -WithZero.log (v.valuation F (x : F)) := Int.toNat_of_nonneg (neg_nonneg.mpr hl)
  rw [NumberField.FinitePlace.mk_apply, NumberField.FinitePlace.norm_embedding',
      WithZeroMulInt.toNNReal_neg_apply _ h0]
  simp only [idealNorm, map_pow, Nat.cast_pow, NNReal.coe_zpow, NNReal.coe_natCast]
  rw [← zpow_natCast, hn, zpow_neg]

private theorem finiteAbv (x : Fˣ) :
    (fun v : HeightOneSpectrum (𝓞 F) => NumberField.FinitePlace.mk v (x : F)).HasFiniteMulSupport := by
  exact (NumberField.FinitePlace.hasFiniteMulSupport x.ne_zero).comp_of_injective
    NumberField.FinitePlace.equivHeightOneSpectrum.symm.injective

theorem exteriorPrincipalIdeal_norm (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : Fˣ) (hx : (x : F) ∈ (S : Set (HeightOneSpectrum (𝓞 F))).integer F) :
    exteriorPrincipalIdeal F S x ≠ ⊥ ∧
      idealNorm (exteriorPrincipalIdeal F S x) =
        (∏ v : NumberField.InfinitePlace F, v (x : F) ^ v.mult) *
          ∏ v ∈ S, NumberField.FinitePlace.mk v (x : F) := by
  let a := fun v : HeightOneSpectrum (𝓞 F) => NumberField.FinitePlace.mk v (x : F)
  let f := fun v : HeightOneSpectrum (𝓞 F) =>
    if v ∈ S then (⊤ : Ideal (𝓞 F))
    else v.asIdeal ^ (-WithZero.log (v.valuation F (x : F))).toNat
  let e := fun v : HeightOneSpectrum (𝓞 F) => if v ∈ S then (1 : ℝ) else a v
  let s := fun v : HeightOneSpectrum (𝓞 F) => if v ∈ S then a v else (1 : ℝ)
  have ha : a.HasFiniteMulSupport := finiteAbv F x
  have hlocal (v : HeightOneSpectrum (𝓞 F)) : idealNorm (f v) = (e v)⁻¹ := by
    by_cases hv : v ∈ S
    · simp [f, e, hv, idealNorm]
    · simpa [f, e, a, hv] using localNorm F S x hx v hv
  have hf : f.HasFiniteMulSupport := by
    apply ha.subset
    intro v hv
    change a v ≠ 1
    intro hav
    have hn : idealNorm (f v) = 1 := by
      rw [hlocal]
      simp [e, hav]
    have hn' : Ideal.absNorm (f v) = 1 := by
      unfold idealNorm at hn
      exact_mod_cast hn
    have ht : f v = ⊤ := Ideal.absNorm_eq_one_iff.mp hn'
    exact hv (by simpa using ht)
  have he : e.HasFiniteMulSupport := by
    apply ha.subset
    intro v hv
    by_cases h : v ∈ S <;> simp_all [e, Function.mem_mulSupport]
  have hs : s.HasFiniteMulSupport := by
    apply S.finite_toSet.subset
    intro v hv
    by_contra h
    exact hv (by simp [s, show v ∉ S from h])
  constructor
  · change (∏ᶠ v, f v) ≠ ⊥
    apply finprod_ne_zero
    intro v
    by_cases hv : v ∈ S
    · simp [f, hv]
    · simpa [f, hv] using pow_ne_zero
        (-WithZero.log (v.valuation F (x : F))).toNat v.ne_bot
  · have hn : idealNorm (exteriorPrincipalIdeal F S x) = (∏ᶠ v, e v)⁻¹ := by
      change ((Nat.castRingHom ℝ).toMonoidHom.comp Ideal.absNorm.toMonoidHom)
        (∏ᶠ v, f v) = _
      rw [MonoidHom.map_finprod _ hf]
      simp only [MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_coe]
      change (∏ᶠ v, idealNorm (f v)) = _
      simp_rw [hlocal]
      exact finprod_inv_distrib e
    have hp : (∏ᶠ v, a v) = (∏ᶠ v, e v) * ∏ v ∈ S, a v := by
      calc
        (∏ᶠ v, a v) = ∏ᶠ v, e v * s v := by
          apply finprod_congr
          intro v
          by_cases hv : v ∈ S <;> simp [e, s, hv]
        _ = (∏ᶠ v, e v) * ∏ᶠ v, s v := finprod_mul_distrib he hs
        _ = _ := by
          congr 1
          rw [finprod_eq_prod_of_mulSupport_subset s]
          · apply Finset.prod_congr rfl
            intro v hv
            simp [s, hv]
          · intro v hv
            by_contra h
            exact hv (by simp [s, show v ∉ S from h])
    have hpf := NumberField.prod_abs_eq_one x.ne_zero
    rw [← finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm] at hpf
    change (∏ v : NumberField.InfinitePlace F, v (x : F) ^ v.mult) *
      (∏ᶠ v, a v) = 1 at hpf
    rw [hp] at hpf
    rw [hn]
    apply inv_eq_of_mul_eq_one_left
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hpf

end DedekindZetaZeroFree.ProbeExteriorPrincipalIdealFibers

end

end

section

noncomputable section
open scoped NumberField Classical nonZeroDivisors
open IsDedekindDomain

namespace DedekindZetaZeroFree.ProbeExteriorPrincipalIdealFibers

private theorem val_support (F : Type) [Field F] [NumberField F] (a : F) (ha : a ≠ 0) :
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 F) => v.valuation F a) := by
  have hfin := (NumberField.FinitePlace.hasFiniteMulSupport ha).comp_of_injective
    (NumberField.FinitePlace.equivHeightOneSpectrum.symm.injective)
  apply hfin.subset
  intro v hv
  change NumberField.FinitePlace.mk v a ≠ 1
  rw [NumberField.FinitePlace.mk_apply, NumberField.FinitePlace.norm_embedding']
  intro h
  apply hv
  have h' : (WithZeroMulInt.toNNReal (e := (Ideal.absNorm v.asIdeal : NNReal))
      (ne_of_gt (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v))))
      (v.valuation F a) = 1 := by exact_mod_cast h
  exact (WithZeroMulInt.toNNReal_eq_one_iff _ _
    (ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v))).mp h'

private theorem ideal_count (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ S) :
    FractionalIdeal.count F v (exteriorPrincipalIdeal F S x : FractionalIdeal (𝓞 F)⁰ F) =
      ((-WithZero.log (v.valuation F (x : F))).toNat : ℤ) := by
  let e : HeightOneSpectrum (𝓞 F) → ℤ := fun w =>
    if w ∈ S then 0 else ((-WithZero.log (w.valuation F (x : F))).toNat : ℤ)
  have he : ∀ᶠ w in Filter.cofinite, e w = 0 := by
    have h := val_support F (x : F) x.ne_zero
    filter_upwards [Filter.eventually_cofinite.mpr h] with w hw
    have hw' : w.valuation F (x : F) = 1 := by
      simpa only [Function.mem_mulSupport, not_not] using hw
    simp [e, hw']
  have hcast : (exteriorPrincipalIdeal F S x : FractionalIdeal (𝓞 F)⁰ F) =
      ∏ᶠ w : HeightOneSpectrum (𝓞 F), (w.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ e w := by
    rw [exteriorPrincipalIdeal, FractionalIdeal.coeIdeal_finprod (𝓞 F)⁰ F le_rfl]
    apply finprod_congr
    intro w
    by_cases hw : w ∈ S
    · simp [e, hw]
    · simp only [e, if_neg hw, FractionalIdeal.coeIdeal_pow, zpow_natCast]
  rw [hcast, FractionalIdeal.count_finprod F v e he]
  simp [e, hv]

private theorem equal_ideal_unit (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : Detector.FrequencyRepresentatives F (S : Set (HeightOneSpectrum (𝓞 F))))
    (u w : U.carrier) (h : exteriorPrincipalIdeal F S u.val = exteriorPrincipalIdeal F S w.val) :
    u.val / w.val ∈ (S : Set (HeightOneSpectrum (𝓞 F))).unit F := by
  intro v hv
  obtain ⟨a, ha⟩ := (U.power_free u.val u.property).2 v hv
  obtain ⟨b, hb⟩ := (U.power_free w.val w.property).2 v hv
  have he := congrArg (fun I : Ideal (𝓞 F) =>
    FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F)) h
  rw [ideal_count F S u.val v hv, ideal_count F S w.val v hv, ha, hb] at he
  simp only [WithZero.log_exp, neg_neg, Int.toNat_natCast] at he
  rw [Units.val_div_eq_div_val, map_div₀, ha, hb]
  have hab : a.val = b.val := by exact_mod_cast he
  rw [hab, div_self WithZero.exp_ne_zero]

theorem representative_ideal_fibers (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ M : ℕ, ∀ U : Detector.FrequencyRepresentatives F (S : Set (HeightOneSpectrum (𝓞 F))),
      ∀ I : NonzeroIdeal F,
        {u : U.carrier | exteriorPrincipalIdeal F S u.val = I.val}.Finite ∧
        Nat.card {u : U.carrier // exteriorPrincipalIdeal F S u.val = I.val} ≤ M := by
  let H := SUnitGroup (K := F) S
  let P : Subgroup H := (powMonoidHom 6 : H →* H).range
  let Q := H ⧸ P
  haveI : Finite Q := KummerTheory.finite_sUnit_nthPowerQuotient S (6 : ℕ+)
  refine ⟨Nat.card Q, ?_⟩
  intro U I
  let B := {u : U.carrier // exteriorPrincipalIdeal F S u.val = I.val}
  by_cases hB : Nonempty B
  · let b : B := Classical.choice hB
    let r : B → H := fun u => ⟨u.val.val / b.val.val,
      equal_ideal_unit F S U u.val b.val (u.property.trans b.property.symm)⟩
    let f : B → Q := fun u => QuotientGroup.mk (r u)
    have hf : Function.Injective f := by
      intro u w huw
      have hp : r u / r w ∈ P := QuotientGroup.eq_iff_div_mem.mp huw
      obtain ⟨a, ha⟩ := hp
      apply Subtype.ext
      apply Detector.frequency_representatives_power_injective F (S : Set (HeightOneSpectrum (𝓞 F))) U
      refine ⟨a.val, ?_⟩
      have h := congrArg (fun z : H => z.val) ha
      change a.val ^ 6 = (u.val.val / b.val.val) / (w.val.val / b.val.val) at h
      simpa only [div_div_div_cancel_right] using h.symm
    haveI : Finite B := Finite.of_injective f hf
    refine ⟨?_, Nat.card_le_card_of_injective f hf⟩
    exact Set.finite_coe_iff.mp (show Finite B from inferInstance)
  · haveI : IsEmpty B := not_nonempty_iff.mp hB
    refine ⟨?_, ?_⟩
    · exact Set.finite_coe_iff.mp (show Finite B from inferInstance)
    · change Nat.card B ≤ Nat.card Q
      simp

end DedekindZetaZeroFree.ProbeExteriorPrincipalIdealFibers

end

end

section

noncomputable section
set_option maxHeartbeats 800000

namespace DedekindZetaZeroFree.ProbeExteriorIdealCount

open scoped NumberField
open IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

def elementNorm (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ) : ℝ :=
  (∏ v : NumberField.InfinitePlace F, v (x : F) ^ v.mult) *
    ∏ v ∈ S, NumberField.FinitePlace.mk v (x : F)

theorem ideal_count_linear (cS : Ideal (𝓞 F)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      {a : ExteriorIdeal cS | idealNorm a.val ≤ T}.Finite ∧
      (Nat.card {a : ExteriorIdeal cS // idealNorm a.val ≤ T} : ℝ) ≤ C * T := by
  classical
  unfold ExteriorIdeal
  obtain ⟨C, C', hC, _, hbound⟩ := ideal_counting_harmonic_bounds F
  refine ⟨C, hC.le, ?_⟩
  intro T hT
  let f : ExteriorIdeal cS → NonzeroIdeal F := fun a => ⟨a.val, a.property.1⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (congrArg (fun z : NonzeroIdeal F => z.val) h)
  have hfinite : {a : ExteriorIdeal cS | idealNorm a.val ≤ T}.Finite :=
    (normBoundedIdeals_finite F T).preimage hf.injOn
  refine ⟨hfinite, ?_⟩
  change (Nat.card ↥{a : ExteriorIdeal cS | idealNorm a.val ≤ T} : ℝ) ≤ C * T
  rw [Nat.card_coe_set_eq]
  have hn := Set.ncard_le_ncard_of_injOn f (fun a ha => ha) hf.injOn
    (normBoundedIdeals_finite F T)
  have hb := (hbound Set.univ).1 T hT
  simp only [Set.univ_inter] at hb
  exact (Nat.cast_le.mpr hn).trans hb

theorem ideal_norm_summable (cS : Ideal (𝓞 F)) (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun a : ExteriorIdeal cS => (idealNorm a.val) ^ (-σ)) := by
  let f : ExteriorIdeal cS → NonzeroIdeal F := fun a => ⟨a.val, a.property.1⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (congrArg (fun z : NonzeroIdeal F => z.val) h)
  change Summable ((fun I : NonzeroIdeal F => idealNorm I.val ^ (-σ)) ∘ f)
  simpa only [Real.rpow_eq_pow] using
    (ideal_norm_rpow_summable F σ hσ).comp_injective hf

theorem ideal_count_annulus (cS : Ideal (𝓞 F))
    (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 1 ≤ Y →
      {a : ExteriorIdeal cS | c₀ * Y ≤ idealNorm a.val ∧ idealNorm a.val ≤ c₁ * Y}.Finite ∧
      (Nat.card {a : ExteriorIdeal cS //
        c₀ * Y ≤ idealNorm a.val ∧ idealNorm a.val ≤ c₁ * Y} : ℝ) ≤ C * Y := by
  classical
  unfold ExteriorIdeal
  obtain ⟨C, hC, hbound⟩ := ideal_count_linear F cS
  refine ⟨C * max c₁ 1, mul_nonneg hC (le_max_of_le_right zero_le_one), ?_⟩
  intro Y hY
  have hMY : 1 ≤ max c₁ 1 * Y := by
    nlinarith [le_max_right c₁ (1 : ℝ)]
  obtain ⟨hf, hb⟩ := hbound (max c₁ 1 * Y) hMY
  have hsub : {a : ExteriorIdeal cS | c₀ * Y ≤ idealNorm a.val ∧ idealNorm a.val ≤ c₁ * Y} ⊆
      {a : ExteriorIdeal cS | idealNorm a.val ≤ max c₁ 1 * Y} := by
    intro a ha
    exact ha.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  refine ⟨hf.subset hsub, ?_⟩
  change (Nat.card ↥{a : ExteriorIdeal cS | c₀ * Y ≤ idealNorm a.val ∧ idealNorm a.val ≤ c₁ * Y} : ℝ) ≤ _
  change (Nat.card ↥{a : ExteriorIdeal cS | idealNorm a.val ≤ max c₁ 1 * Y} : ℝ) ≤ _ at hb
  rw [Nat.card_coe_set_eq] at hb ⊢
  exact (Nat.cast_le.mpr (Set.ncard_le_ncard hsub hf)).trans (by simpa [mul_assoc] using hb)

theorem representative_count_linear (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ U : Detector.FrequencyRepresentatives F (S : Set (HeightOneSpectrum (𝓞 F))),
      ∀ T : ℝ, 1 ≤ T →
        {u : U.carrier | elementNorm F S u.val ≤ T}.Finite ∧
        (Nat.card {u : U.carrier // elementNorm F S u.val ≤ T} : ℝ) ≤ C * T := by
  classical
  obtain ⟨M, hM⟩ := ProbeExteriorPrincipalIdealFibers.representative_ideal_fibers F S
  obtain ⟨K, K', hK, _, hcount⟩ := ideal_counting_harmonic_bounds F
  refine ⟨(M : ℝ) * K, mul_nonneg (Nat.cast_nonneg _) hK.le, ?_⟩
  intro U T hT
  let f : U.carrier → NonzeroIdeal F := fun u =>
    ⟨ProbeExteriorPrincipalIdealFibers.exteriorPrincipalIdeal F S u.val,
      (ProbeExteriorPrincipalIdealFibers.exteriorPrincipalIdeal_norm F S u.val
        (U.power_free u.val u.property).1).1⟩
  have hnorm (u : U.carrier) : idealNorm (f u).val = elementNorm F S u.val :=
    (ProbeExteriorPrincipalIdealFibers.exteriorPrincipalIdeal_norm F S u.val
      (U.power_free u.val u.property).1).2
  have hf : ∀ I : NonzeroIdeal F,
      {u : U.carrier | f u = I}.Finite ∧ Nat.card {u : U.carrier // f u = I} ≤ M := by
    intro I
    have he : ∀ u : U.carrier, f u = I ↔
        ProbeExteriorPrincipalIdealFibers.exteriorPrincipalIdeal F S u.val = I.val := by
      intro u
      exact Subtype.ext_iff
    simpa only [he] using hM U I
  obtain ⟨hfinite, hcard⟩ := ProbeExteriorPrincipalIdealFibers.finite_preimage_card_bound
    f M hf (normBoundedIdeals F T) (normBoundedIdeals_finite F T)
  have he : ∀ u : U.carrier, f u ∈ normBoundedIdeals F T ↔ elementNorm F S u.val ≤ T := by
    intro u
    change idealNorm (f u).val ≤ T ↔ _
    rw [hnorm]
  simp only [he] at hfinite hcard
  refine ⟨hfinite, ?_⟩
  have hb : (Nat.card (normBoundedIdeals F T) : ℝ) ≤ K * T := by
    rw [Nat.card_coe_set_eq]
    simpa using (hcount Set.univ).1 T hT
  have hcast : (Nat.card {u : U.carrier // elementNorm F S u.val ≤ T} : ℝ) ≤
      (M : ℝ) * (Nat.card (normBoundedIdeals F T) : ℝ) := by
    exact_mod_cast hcard
  exact hcast.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg M))

end DedekindZetaZeroFree.ProbeExteriorIdealCount

end

end

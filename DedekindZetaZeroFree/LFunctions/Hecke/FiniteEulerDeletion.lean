module

public import DedekindZetaZeroFree.ZeroDetection.Conductors.FrequencyTwistsAndLocalCharacters
public import DedekindZetaZeroFree.ZeroDetection.Conductors.FrequencyDyadCounts
public import DedekindZetaZeroFree.LFunctions.Hecke.OmittedEulerProductBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.DirichletSeriesRightEdgeBounds

@[expose] public section

open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.Detector

noncomputable section

private lemma absNorm_prime_ge_two (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    intro h; rw [Ideal.absNorm_eq_zero_iff] at h; exact v.ne_bot h
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    intro h; rw [Ideal.absNorm_eq_one_iff] at h
    exact (Ideal.IsMaximal.ne_top v.isMaximal) h
  omega

private lemma absNorm_prime_gt_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h : (2:ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast absNorm_prime_ge_two F v
  linarith

private lemma absNorm_prime_rpow_lt_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {σ : ℝ} (hσ : 0 < σ) :
    (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (absNorm_prime_gt_one F v) (by linarith)

def exteriorFrequencyPrimeSupport (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (u : S.integer F) :
    Set (HeightOneSpectrum (𝓞 F)) :=
  {v | v ∉ S ∧ v.valuation F (u : F) < 1}

def finiteEulerLocalFactor (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a s : ℂ) : ℂ :=
  1 - a * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)

def finiteEulerPlusMajorant (F : Type) [Field F] [NumberField F]
    (D : Set (HeightOneSpectrum (𝓞 F))) (σ : ℝ) : ℝ :=
  ∏ᶠ v : D, (1 + (Ideal.absNorm v.val.asIdeal : ℝ) ^ (-σ))

def finiteEulerInverseMajorant (F : Type) [Field F] [NumberField F]
    (D : Set (HeightOneSpectrum (𝓞 F))) (σ : ℝ) : ℝ :=
  ∏ᶠ v : D, (1 - (Ideal.absNorm v.val.asIdeal : ℝ) ^ (-σ))⁻¹

def finiteEulerDeletionMask (F : Type) [Field F] [NumberField F]
    (D : Set (HeightOneSpectrum (𝓞 F)))
    (a : HeightOneSpectrum (𝓞 F) → ℂ) (s : ℂ) : ℂ :=
  ∏ᶠ v : D, finiteEulerLocalFactor F v.val (a v.val) s

def deletedPrimitiveIdealCoefficient (F : Type) [Field F] [NumberField F]
    (ω : PrimitiveFrequencyCharacter F) (D : Set (HeightOneSpectrum (𝓞 F)))
    (I : Ideal (𝓞 F)) : ℂ :=
  if ∃ v ∈ D, I ≤ v.asIdeal then 0 else ω.character I

theorem exterior_frequency_support_finite_norm_pos
    (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (u : S.integer F) (hu : u ≠ 0) :
    (exteriorFrequencyPrimeSupport F S u).Finite ∧
      Finite ((S.integer F) ⧸ Ideal.span {u}) ∧
      1 ≤ frequencyNorm F S u := by
  classical
  have huF : (u : F) ≠ 0 := by exact_mod_cast hu
  have hfin := HeightOneSpectrum.Support.finite (𝓞 F) ((u : F)⁻¹)
  have hext : (exteriorFrequencyPrimeSupport F S u).Finite := hfin.subset (by
    intro v hv
    exact ((v.valuation F).val_lt_one_iff huF).mp hv.2)
  obtain ⟨Sf, hSf⟩ := hS.exists_finset_coe
  have hq : Finite ((S.integer F) ⧸ Ideal.span {u}) := by
    subst S
    exact (sProductModulus_eq_principalIdeal_index F Sf u hu).1
  letI := hq
  exact ⟨hext, hq, Nat.card_pos⟩

theorem finite_euler_local_factor_nonzero
    (F : Type) [Field F] [NumberField F]
    (σ : ℝ) (hσ : 0 < σ) (v : HeightOneSpectrum (𝓞 F))
    (a s : ℂ) (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    0 < 1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) ∧
      1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) ≤
        ‖finiteEulerLocalFactor F v a s‖ ∧
      finiteEulerLocalFactor F v a s ≠ 0 := by
  have hv : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hp : 0 < 1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hv (neg_neg_of_pos hσ))
  have hb : ‖a * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ ≤
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by exact_mod_cast (lt_trans zero_lt_one hv)),
      Complex.neg_re]
    calc
      ‖a‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤
          1 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (by positivity) _)
      _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
        simpa using Real.rpow_le_rpow_of_exponent_le hv.le (neg_le_neg hs)
  have hl : 1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) ≤
      ‖finiteEulerLocalFactor F v a s‖ := by
    calc
      _ ≤ 1 - ‖a * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ := sub_le_sub_left hb 1
      _ ≤ ‖finiteEulerLocalFactor F v a s‖ := by
        simpa [finiteEulerLocalFactor] using
          (norm_sub_norm_le (1 : ℂ) (a * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))
  exact ⟨hp, hl, norm_pos_iff.mp (lt_of_lt_of_le hp hl)⟩

private theorem exterior_prime_divides_comap
    (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (u : S.integer F)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ exteriorFrequencyPrimeSupport F S u) :
    v.asIdeal ∣ Ideal.comap (algebraMap (𝓞 F) (S.integer F)) (Ideal.span {u}) := by
  apply Ideal.dvd_iff_le.mpr
  intro x hx
  have hx' : (algebraMap (𝓞 F) (S.integer F)) x ∈ Ideal.span {u} := hx
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hx'
  apply (v.valuation_lt_one_iff_mem (K := F) x).mp
  have hvb : v.valuation F (b : F) ≤ 1 := b.property v hv.1
  have hmul : v.valuation F (x : F) =
      v.valuation F (u : F) * v.valuation F (b : F) := by
    have hbF : (x : F) = (u : F) * (b : F) := by
      have h := congrArg (fun y : S.integer F => (y : F)) hb
      simpa only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap] using h
    rw [hbF, map_mul]
  rw [hmul]
  have hle : v.valuation F (u : F) * v.valuation F (b : F) ≤ v.valuation F (u : F) :=
    by simpa [mul_comm] using mul_le_mul_left hvb (v.valuation F (u : F))
  exact hle.trans_lt hv.2

private theorem exterior_comap_ne_bot
    (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (u : S.integer F) (hu : u ≠ 0) :
    Ideal.comap (algebraMap (𝓞 F) (S.integer F)) (Ideal.span {u}) ≠ ⊥ := by
  have huF : (u : F) ≠ 0 := by exact_mod_cast hu
  obtain ⟨⟨n, ⟨d, hd⟩⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 F)) (u : F)
  have hn : n ≠ 0 := by
    intro hn
    have hdF : (d : F) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hd
    simp only [hn, map_zero] at h
    exact (mul_ne_zero huF hdF) h
  intro hbot
  have hnmem : n ∈ Ideal.comap (algebraMap (𝓞 F) (S.integer F)) (Ideal.span {u}) := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨algebraMap (𝓞 F) (S.integer F) d, ?_⟩
    apply Subtype.ext
    simpa only [Subalgebra.coe_algebraMap, Subalgebra.coe_mul] using h.symm
  rw [hbot] at hnmem
  exact hn hnmem

private theorem exterior_ideal_norm_le_frequencyNorm
    (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) (u : S.integer F) (hu : u ≠ 0) :
    Ideal.absNorm (Ideal.comap (algebraMap (𝓞 F) (S.integer F)) (Ideal.span {u})) ≤
      frequencyNorm F S u := by
  classical
  let I : Ideal (𝓞 F) := Ideal.comap (algebraMap (𝓞 F) (S.integer F)) (Ideal.span {u})
  have hR : Finite ((S.integer F) ⧸ Ideal.span {u}) := by
    exact (exterior_frequency_support_finite_norm_pos F S hS u hu).2.1
  have hmap : Function.Injective (Ideal.quotientMap (Ideal.span {u})
      (algebraMap (𝓞 F) (S.integer F)) le_rfl) := Ideal.quotientMap_injective
  letI : Finite ((𝓞 F) ⧸ I) := Finite.of_injective _ hmap
  simpa [I, Ideal.absNorm_apply, frequencyNorm, Submodule.cardQuot_apply] using
    Nat.card_le_card_of_injective _ hmap

private theorem finite_masks_comparison
    (F : Type) [Field F] [NumberField F]
    (D : Set (HeightOneSpectrum (𝓞 F))) (hD : D.Finite)
    (σ : ℝ) (hσ : 0 < σ) (a : HeightOneSpectrum (𝓞 F) → ℂ) (s : ℂ)
    (ha : ∀ v ∈ D, ‖a v‖ ≤ 1) (hs : σ ≤ s.re) :
    finiteEulerDeletionMask F D a s ≠ 0 ∧
    ‖finiteEulerDeletionMask F D a s‖ ≤ finiteEulerPlusMajorant F D σ ∧
    ‖(finiteEulerDeletionMask F D a s)⁻¹‖ ≤ finiteEulerInverseMajorant F D σ := by
  letI := hD.fintype
  have hl (v : D) := finite_euler_local_factor_nonzero F σ hσ v.val (a v.val) s
    (ha _ v.property) hs
  simp only [finiteEulerDeletionMask, finiteEulerPlusMajorant, finiteEulerInverseMajorant,
    finprod_eq_prod_of_fintype, norm_inv, norm_prod, ← Finset.prod_inv_distrib]
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun v _ => (hl v).2.2), ?_, ?_⟩
  · apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro v _
    have hv : 1 < (Ideal.absNorm v.val.asIdeal : ℝ) := absNorm_prime_gt_one F v.val
    have hb : ‖a v.val * (Ideal.absNorm v.val.asIdeal : ℂ) ^ (-s)‖ ≤
        (Ideal.absNorm v.val.asIdeal : ℝ) ^ (-σ) := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by have := absNorm_prime_ge_two F v.val; omega), Complex.neg_re]
      calc
        _ ≤ 1 * (Ideal.absNorm v.val.asIdeal : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (ha _ v.property) (by positivity)
        _ ≤ (Ideal.absNorm v.val.asIdeal : ℝ) ^ (-σ) := by
          simpa using Real.rpow_le_rpow_of_exponent_le hv.le (neg_le_neg hs)
    exact (norm_sub_le _ _).trans (by simpa using add_le_add_left hb 1)
  · apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
    intro v _
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hl v).2.2) (hl v).1).mpr (hl v).2.1

theorem frequency_finite_euler_masks_subpower
    (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : S.integer F), u ≠ 0 →
      finiteEulerPlusMajorant F (exteriorFrequencyPrimeSupport F S u) σ ≤
        C * (frequencyNorm F S u : ℝ) ^ ε ∧
      finiteEulerInverseMajorant F (exteriorFrequencyPrimeSupport F S u) σ ≤
        C * (frequencyNorm F S u : ℝ) ^ ε ∧
      ∀ (D : Set (HeightOneSpectrum (𝓞 F))),
        D ⊆ S ∪ exteriorFrequencyPrimeSupport F S u →
        ∀ (a : HeightOneSpectrum (𝓞 F) → ℂ) (s : ℂ),
          (∀ v ∈ D, ‖a v‖ ≤ 1) → σ ≤ s.re →
          finiteEulerDeletionMask F D a s ≠ 0 ∧
          ‖finiteEulerDeletionMask F D a s‖ ≤
            C * (frequencyNorm F S u : ℝ) ^ ε ∧
          ‖(finiteEulerDeletionMask F D a s)⁻¹‖ ≤
            C * (frequencyNorm F S u : ℝ) ^ ε := by
  classical
  let τ := min σ (1 / 2 : ℝ)
  have hτ : 0 < τ := lt_min hσ (by norm_num)
  have hτ1 : τ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨B, hB, hb⟩ := omitted_prime_euler_subpolynomial F τ hτ hτ1 ε hε
  let J : Ideal (𝓞 F) := ∏ v ∈ hS.toFinset, v.asIdeal
  have hJ : J ≠ ⊥ := Finset.prod_ne_zero_iff.mpr (fun v _ => v.ne_bot)
  have hJN : 0 < idealNorm J := lt_of_lt_of_le zero_lt_one (idealNorm_ge_one J hJ)
  refine ⟨B * (idealNorm J) ^ ε, mul_pos hB (Real.rpow_pos_of_pos hJN _), ?_⟩
  intro u hu
  let E := exteriorFrequencyPrimeSupport F S u
  have hE := (exterior_frequency_support_finite_norm_pos F S hS u hu).1
  let I := Ideal.comap (algebraMap (𝓞 F) (S.integer F)) (Ideal.span {u})
  have hI : I ≠ ⊥ := exterior_comap_ne_bot F S u hu
  have hq : idealNorm I ≤ (frequencyNorm F S u : ℝ) := by
    dsimp [idealNorm, I]
    exact_mod_cast exterior_ideal_norm_le_frequencyNorm F S hS u hu
  have hIN : 0 ≤ idealNorm I := by dsimp [idealNorm]; positivity
  have hnorm : B * (idealNorm (I * J)) ^ ε ≤
      B * (idealNorm J) ^ ε * (frequencyNorm F S u : ℝ) ^ ε := by
    have hmul : idealNorm (I * J) = idealNorm I * idealNorm J := by
      simp [idealNorm, map_mul]
    rw [hmul, Real.mul_rpow hIN hJN.le]
    calc
      _ ≤ B * ((frequencyNorm F S u : ℝ) ^ ε * (idealNorm J) ^ ε) := by
        gcongr
      _ = _ := by ring
  have hmajor : ∀ D : Set (HeightOneSpectrum (𝓞 F)), D ⊆ S ∪ E →
      finiteEulerPlusMajorant F D σ ≤ B * (idealNorm J) ^ ε * (frequencyNorm F S u : ℝ) ^ ε ∧
      finiteEulerInverseMajorant F D σ ≤ B * (idealNorm J) ^ ε * (frequencyNorm F S u : ℝ) ^ ε := by
    intro D hD
    have hDf := (hS.union hE).subset hD
    letI := hDf.fintype
    let V := hDf.toFinset
    let T := V.image (fun v => v.asIdeal)
    have hT : ∀ p ∈ T, Prime p ∧ p ∣ I * J := by
      intro p hp
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
      refine ⟨Ideal.prime_of_isPrime v.ne_bot v.isPrime, ?_⟩
      rcases hD (hDf.mem_toFinset.mp hv) with hvS | hvE
      · apply dvd_mul_of_dvd_right
        exact Finset.dvd_prod_of_mem _ (hS.mem_toFinset.mpr hvS)
      · exact dvd_mul_of_dvd_left (exterior_prime_divides_comap F S u v hvE) J
    have hbound := hb (I * J) (mul_ne_zero hI hJ) T hT
    have hplus : finiteEulerPlusMajorant F D σ ≤ ∏ p ∈ T, (1 + idealNorm p ^ (-τ)) := by
      simp only [finiteEulerPlusMajorant, finprod_eq_prod_of_fintype]
      rw [← Finset.prod_subtype hDf.toFinset (fun v => hDf.mem_toFinset)
        (fun v => 1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ))]
      dsimp [T, V]
      rw [Finset.prod_image (by intro v _ w _ h; exact HeightOneSpectrum.ext h)]
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro v _
      simpa [idealNorm, add_comm, τ] using add_le_add_left
        (Real.rpow_le_rpow_of_exponent_le
          (absNorm_prime_gt_one F v).le (neg_le_neg (min_le_left σ (1 / 2 : ℝ)))) 1
    have hinv : finiteEulerInverseMajorant F D σ ≤ ∏ p ∈ T, (1 - idealNorm p ^ (-τ))⁻¹ := by
      simp only [finiteEulerInverseMajorant, finprod_eq_prod_of_fintype]
      rw [← Finset.prod_subtype hDf.toFinset (fun v => hDf.mem_toFinset)
        (fun v => (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ))⁻¹)]
      dsimp [T, V]
      rw [Finset.prod_image (by intro v _ w _ h; exact HeightOneSpectrum.ext h)]
      apply Finset.prod_le_prod₀
      · intro v _; exact inv_nonneg.mpr (sub_pos.mpr (absNorm_prime_rpow_lt_one F v hσ)).le
      · intro v _
        apply (inv_le_inv₀ (sub_pos.mpr (absNorm_prime_rpow_lt_one F v hσ))
          (sub_pos.mpr (absNorm_prime_rpow_lt_one F v hτ))).mpr
        exact sub_le_sub_left (Real.rpow_le_rpow_of_exponent_le
          (absNorm_prime_gt_one F v).le (neg_le_neg (min_le_left _ _))) 1
    exact ⟨hplus.trans (hbound.1.trans hnorm), hinv.trans (hbound.2.trans hnorm)⟩
  have hExt := hmajor E (Set.subset_union_right)
  refine ⟨hExt.1, hExt.2, ?_⟩
  intro D hD a s ha hs
  have hDf := (hS.union hE).subset hD
  obtain ⟨hn, hp, hi⟩ := finite_masks_comparison F D hDf σ hσ a s ha hs
  exact ⟨hn, hp.trans (hmajor D hD).1, hi.trans (hmajor D hD).2⟩

private theorem finite_prime_delete_hasSum
    (F : Type) [Field F] [NumberField F]
    (W : Ideal (𝓞 F) → ℂ) (W0 : W ⊥ = 0)
    (Wmul : ∀ a b, W (a * b) = W a * W b)
    (L : ℂ) (hW : HasSum W L) (V : Finset (HeightOneSpectrum (𝓞 F))) :
    HasSum (fun I => if ∃ v ∈ V, I ≤ v.asIdeal then 0 else W I)
      (L * ∏ v ∈ V, (1 - W v.asIdeal)) := by
  induction V using Finset.induction_on with
  | empty => simpa using hW
  | @insert p V hp ih =>
    let G : Ideal (𝓞 F) → ℂ := fun I => if ∃ v ∈ V, I ≤ v.asIdeal then 0 else W I
    have G0 : G ⊥ = 0 := by simp [G, W0]
    have Gmul (I : Ideal (𝓞 F)) : G (I * p.asIdeal) = G I * W p.asIdeal := by
      have he : (∃ v ∈ V, I * p.asIdeal ≤ v.asIdeal) ↔ ∃ v ∈ V, I ≤ v.asIdeal := by
        constructor
        · rintro ⟨v, hv, h⟩
          have hprime := Ideal.prime_of_isPrime v.ne_bot v.isPrime
          have hd : v.asIdeal ∣ I * p.asIdeal := Ideal.dvd_iff_le.mpr h
          rcases hprime.dvd_or_dvd hd with hd | hd
          · exact ⟨v, hv, Ideal.dvd_iff_le.mp hd⟩
          · have heq : v = p := HeightOneSpectrum.ext ((Ideal.IsMaximal.eq_of_le p.isMaximal (Ideal.IsMaximal.ne_top v.isMaximal) (Ideal.dvd_iff_le.mp hd)).symm)
            exact (hp (heq ▸ hv)).elim
        · rintro ⟨v, hv, h⟩
          exact ⟨v, hv, (Ideal.mul_le_left).trans h⟩
      simp only [G, he]
      split_ifs <;> simp [Wmul]
    let H : Ideal (𝓞 F) → ℂ := fun I => if I ≤ p.asIdeal then G I else 0
    have hH : HasSum H ((L * ∏ v ∈ V, (1 - W v.asIdeal)) * W p.asIdeal) := by
      have hi : Function.Injective (fun I : Ideal (𝓞 F) => I * p.asIdeal) := mul_left_injective₀ p.ne_bot
      apply (hi.hasSum_iff ?_).mp
      · have heq : H ∘ (fun I : Ideal (𝓞 F) => I * p.asIdeal) = fun I => G I * W p.asIdeal := by
          funext I
          simp [H, Function.comp_def, Ideal.mul_le_right, Gmul]
        rw [heq]
        exact ih.mul_right _
      · intro I hI
        have hn : ¬ I ≤ p.asIdeal := by
          intro h
          obtain ⟨a, ha⟩ := Ideal.dvd_iff_le.mpr h
          exact hI ⟨a, by simpa [mul_comm] using ha.symm⟩
        simp [H, hn]
    have hh := ih.sub hH
    have heq : (fun I => (if ∃ v ∈ V, I ≤ v.asIdeal then 0 else W I) - H I) =
        (fun I => if ∃ v ∈ insert p V, I ≤ v.asIdeal then 0 else W I) := by
      funext I
      by_cases hI : I ≤ p.asIdeal <;> by_cases hV : ∃ v ∈ V, I ≤ v.asIdeal <;>
        simp [H, G, hI, hV, Finset.exists_mem_insert]
    rw [heq] at hh
    convert hh using 1
    rw [Finset.prod_insert hp]
    ring

theorem deleted_primitive_L_euler_identity
    (F : Type) [Field F] [NumberField F]
    (ω : PrimitiveFrequencyCharacter F)
    (D : Set (HeightOneSpectrum (𝓞 F))) (hD : D.Finite)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 F) =>
      deletedPrimitiveIdealCoefficient F ω D I * (Ideal.absNorm I : ℂ) ^ (-s)) ∧
    (∑' I : Ideal (𝓞 F),
      deletedPrimitiveIdealCoefficient F ω D I * (Ideal.absNorm I : ℂ) ^ (-s)) =
      (∑' I : Ideal (𝓞 F), ω.character I * (Ideal.absNorm I : ℂ) ^ (-s)) *
        finiteEulerDeletionMask F D (fun v => ω.character v.asIdeal) s := by
  classical
  let W : Ideal (𝓞 F) → ℂ := fun I => ω.character I * (Ideal.absNorm I : ℂ) ^ (-s)
  have W0 : W ⊥ = 0 := by
    have h0 : ω.character ⊥ = 0 := (ω.character.eq_zero_iff' ⊥).mpr (Or.inl rfl)
    simp [W, h0]
  have Wmul (a b : Ideal (𝓞 F)) : W (a * b) = W a * W b := by
    dsimp [W]
    rw [ω.character.map_mul', map_mul Ideal.absNorm, Nat.cast_mul]
    have hp : ((Ideal.absNorm a : ℂ) * (Ideal.absNorm b : ℂ)) ^ (-s) =
        (Ideal.absNorm a : ℂ) ^ (-s) * (Ideal.absNorm b : ℂ) ^ (-s) := by
      exact_mod_cast Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg (Ideal.absNorm a) : (0 : ℝ) ≤ Ideal.absNorm a)
        (Nat.cast_nonneg (Ideal.absNorm b) : (0 : ℝ) ≤ Ideal.absNorm b) (-s)
    rw [hp]
    ring
  have hW := (heckeDirichlet_right_edge F s.re hs ω.conductor ω.conductor_ne_zero ω.character s le_rfl).1
  have hh := finite_prime_delete_hasSum F W W0 Wmul (∑' I, W I) hW.hasSum hD.toFinset
  have heq : (fun I => if ∃ v ∈ hD.toFinset, I ≤ v.asIdeal then 0 else W I) =
      (fun I => deletedPrimitiveIdealCoefficient F ω D I * (Ideal.absNorm I : ℂ) ^ (-s)) := by
    funext I
    simp only [deletedPrimitiveIdealCoefficient, hD.mem_toFinset]
    split_ifs <;> simp [W]
  rw [heq] at hh
  have hmask : (∏ v ∈ hD.toFinset, (1 - W v.asIdeal)) =
      finiteEulerDeletionMask F D (fun v => ω.character v.asIdeal) s := by
    letI := hD.fintype
    simp only [finiteEulerDeletionMask, finprod_eq_prod_of_fintype]
    rw [← Finset.prod_subtype hD.toFinset (fun v => hD.mem_toFinset)
      (fun v => finiteEulerLocalFactor F v (ω.character v.asIdeal) s)]
    rfl
  rw [hmask] at hh
  exact ⟨hh.summable, hh.tsum_eq⟩

theorem deleted_primitive_L_continuation
    (F : Type) [Field F] [NumberField F]
    (ω : PrimitiveFrequencyCharacter F)
    (D : Set (HeightOneSpectrum (𝓞 F))) (hD : D.Finite)
    (Ω : Set ℂ) (L : ℂ → ℂ) (hL : MeromorphicOn L Ω)
    (hseries : ∀ s : ℂ, 1 < s.re → HasSum
      (fun I : Ideal (𝓞 F) => ω.character I * (Ideal.absNorm I : ℂ) ^ (-s)) (L s)) :
    Differentiable ℂ (finiteEulerDeletionMask F D (fun v => ω.character v.asIdeal)) ∧
    MeromorphicOn
      (fun s => L s * finiteEulerDeletionMask F D (fun v => ω.character v.asIdeal) s) Ω ∧
    ∀ s : ℂ, 1 < s.re → HasSum
      (fun I : Ideal (𝓞 F) =>
        deletedPrimitiveIdealCoefficient F ω D I * (Ideal.absNorm I : ℂ) ^ (-s))
      (L s * finiteEulerDeletionMask F D (fun v => ω.character v.asIdeal) s) := by
  classical
  haveI : Fintype D := hD.fintype
  have hfun : finiteEulerDeletionMask F D (fun v => ω.character v.asIdeal) =
      fun s : ℂ => ∏ v : D, finiteEulerLocalFactor F v.val (ω.character v.val.asIdeal) s := by
    funext s; rw [finiteEulerDeletionMask, finprod_eq_prod_of_fintype]
  have hmaskdiff : Differentiable ℂ (finiteEulerDeletionMask F D (fun v => ω.character v.asIdeal)) := by
    rw [hfun]
    have hd : Differentiable ℂ (∏ v ∈ (Finset.univ : Finset D),
        fun s : ℂ => finiteEulerLocalFactor F v.val (ω.character v.val.asIdeal) s) := by
      apply Differentiable.finsetProd
      intro v _
      have hc : (Ideal.absNorm v.val.asIdeal : ℂ) ≠ 0 := by
        have h2 : 2 ≤ Ideal.absNorm v.val.asIdeal := by
          have h0 : Ideal.absNorm v.val.asIdeal ≠ 0 := by
            intro h; rw [Ideal.absNorm_eq_zero_iff] at h; exact v.val.ne_bot h
          have h1 : Ideal.absNorm v.val.asIdeal ≠ 1 := by
            intro h; rw [Ideal.absNorm_eq_one_iff] at h
            exact (Ideal.IsMaximal.ne_top v.val.isMaximal) h
          omega
        exact_mod_cast (by omega : Ideal.absNorm v.val.asIdeal ≠ 0)
      have hdc : Differentiable ℂ (fun s : ℂ => (Ideal.absNorm v.val.asIdeal : ℂ) ^ (-s)) :=
        Differentiable.const_cpow differentiable_neg (Or.inl hc)
      have hfe : (fun s : ℂ => finiteEulerLocalFactor F v.val (ω.character v.val.asIdeal) s) =
          fun s : ℂ => 1 - ω.character v.val.asIdeal * (Ideal.absNorm v.val.asIdeal : ℂ) ^ (-s) := by
        funext s; rfl
      rw [hfe]
      exact (differentiable_const (c := (1:ℂ))).sub
        ((differentiable_const (c := ω.character v.val.asIdeal)).mul hdc)
    have hd' : (∏ v ∈ (Finset.univ : Finset D),
        fun s : ℂ => finiteEulerLocalFactor F v.val (ω.character v.val.asIdeal) s) =
        (fun s : ℂ => ∏ v : D, finiteEulerLocalFactor F v.val (ω.character v.val.asIdeal) s) := by
      funext s; simp [Finset.prod_apply]
    rwa [hd'] at hd
  refine ⟨hmaskdiff, ?_, ?_⟩
  · have hmaskmero : MeromorphicOn
        (finiteEulerDeletionMask F D (fun v => ω.character v.asIdeal)) Ω :=
      fun x _ => (Complex.analyticAt_iff_eventually_differentiableAt.mpr
        (Filter.Eventually.of_forall (fun z => hmaskdiff z))).meromorphicAt
    exact hL.mul hmaskmero
  · intro s hs
    obtain ⟨hsum, htsum⟩ := deleted_primitive_L_euler_identity F ω D hD s hs
    have hLeq : (∑' I : Ideal (𝓞 F), ω.character I * (Ideal.absNorm I : ℂ) ^ (-s)) = L s :=
      (hseries s hs).tsum_eq
    rw [hLeq] at htsum
    rw [← htsum]
    exact hsum.hasSum

private theorem positive_representative (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (a : 𝓞 F) :
    ∃ b : 𝓞 F, b - a ∈ m ∧ ∀ φ : F →+* ℝ, 0 < φ (b : F) := by
  have hn : 0 < Ideal.absNorm m := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hm)
  have hb : ∃ B : ℝ, ∀ φ : F →+* ℝ, -φ (a : F) < B := by
    exact ⟨∑ φ : F →+* ℝ, |φ (a : F)| + 1, fun φ => by
      have ht := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => abs_nonneg ((i : F →+* ℝ) (a : F))) (Finset.mem_univ φ)
      linarith [neg_le_abs (φ (a : F))]⟩
  obtain ⟨B, hB⟩ := hb
  obtain ⟨n, hnB⟩ := exists_nat_gt B
  let b : 𝓞 F := a + (n * Ideal.absNorm m : ℕ)
  have hp (φ : F →+* ℝ) : 0 < φ (b : F) := by
    have hN : (1 : ℝ) ≤ Ideal.absNorm m := by exact_mod_cast hn
    have hnb : (n : ℝ) ≤ (n : ℝ) * Ideal.absNorm m := by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    change 0 < (φ.comp (algebraMap (𝓞 F) F)) (a + (n * Ideal.absNorm m : ℕ))
    rw [map_add, map_natCast]
    simp only [Nat.cast_mul, RingHom.comp_apply]
    linarith [hB φ]
  refine ⟨b, ?_, hp⟩
  have hh : ((n * Ideal.absNorm m : ℕ) : 𝓞 F) ∈ m := by
    simpa only [Nat.cast_mul] using m.mul_mem_left (n : 𝓞 F) m.absNorm_mem
  simpa [b] using hh
private theorem coprime_of_sub_one_mem {R : Type*} [CommRing R]
    (m : Ideal R) (a : R) (h : a - 1 ∈ m) : Ideal.span {a} ⊔ m = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have ha : a ∈ Ideal.span {a} ⊔ m := Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)
  have hb : a - 1 ∈ Ideal.span {a} ⊔ m := Ideal.mem_sup_right h
  simpa using (Ideal.span {a} ⊔ m).sub_mem ha hb

private theorem nonzero_of_sub_one_mem {R : Type*} [CommRing R]
    (m : Ideal R) (hm : m ≠ ⊤) (a : R) (h : a - 1 ∈ m) : a ≠ 0 := by
  intro ha
  subst a
  apply hm
  apply (Ideal.eq_top_iff_one _).mpr
  simpa using m.neg_mem h

private theorem ray_congruent_positive
    (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hmt : m ≠ ⊤) (χ : RayClassCharacter F m)
    (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hpa : ∀ φ : F →+* ℝ, 0 < φ (a : F))
    (hpb : ∀ φ : F →+* ℝ, 0 < φ (b : F))
    (hcop : Ideal.span {a} ⊔ m = ⊤) (hab : a - b ∈ m) :
    χ (Ideal.span {a}) = χ (Ideal.span {b}) := by
  have hone : (1 : 𝓞 F) ∈ Ideal.span {a} ⊔ m := by rw [hcop]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hone
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hx
  have hac : a * c - 1 ∈ m := by
    have heq : a * c - 1 = -y := by linear_combination hxy
    rw [heq]
    exact m.neg_mem hy
  obtain ⟨d, hdc, hpd⟩ := positive_representative F m hm c
  have had : a * d - 1 ∈ m := by
    have heq : a * d - 1 = (a * c - 1) + a * (d - c) := by ring
    rw [heq]; exact m.add_mem hac (m.mul_mem_left a hdc)
  have hbd : b * d - 1 ∈ m := by
    have heq : b * d - 1 = (a * d - 1) - (a - b) * d := by ring
    rw [heq]; exact m.sub_mem had (m.mul_mem_right d hab)
  have had0 := nonzero_of_sub_one_mem m hmt (a*d) had
  have hbd0 := nonzero_of_sub_one_mem m hmt (b*d) hbd
  have hca : χ (Ideal.span {a}) * χ (Ideal.span {d}) = 1 := by
    rw [← χ.map_mul', Ideal.span_singleton_mul_span_singleton]
    apply χ.map_span' (a*d) had0 had
    intro φ
    change 0 < (φ.comp (algebraMap (𝓞 F) F)) (a * d)
    rw [map_mul]
    exact mul_pos (hpa φ) (hpd φ)
  have hcb : χ (Ideal.span {b}) * χ (Ideal.span {d}) = 1 := by
    rw [← χ.map_mul', Ideal.span_singleton_mul_span_singleton]
    apply χ.map_span' (b*d) hbd0 hbd
    intro φ
    change 0 < (φ.comp (algebraMap (𝓞 F) F)) (b * d)
    rw [map_mul]
    exact mul_pos (hpb φ) (hpd φ)
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one hca) (hca.trans hcb.symm)

theorem finite_mask_twist_conductor_le
    (F : Type) [Field F] [NumberField F]
    (η χ ψ : PrimitiveFrequencyCharacter F)
    (hTwist : IsPrimitiveFrequencyTwist F η χ ψ) :
    η.conductor * χ.conductor ≤ ψ.conductor := by
  by_cases hf : ψ.conductor = ⊤
  · simp [hf]
  by_contra hle
  have hlt : ψ.conductor < ψ.conductor ⊔ (η.conductor * χ.conductor) :=
    lt_of_le_of_ne le_sup_left (fun heq => hle (le_sup_right.trans_eq heq.symm))
  obtain ⟨a, ha, ham, hpos, hcop, hne⟩ := ψ.primitive _ hlt
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ham
  obtain ⟨b, hby, hposb⟩ := positive_representative F
    (ψ.conductor * (η.conductor * χ.conductor))
    (mul_ne_zero ψ.conductor_ne_zero (mul_ne_zero η.conductor_ne_zero χ.conductor_ne_zero)) (1+y)
  have hab : a - b ∈ ψ.conductor := by
    have heq : a - b = x - (b - (1+y)) := by linear_combination -hxy
    rw [heq]; exact ψ.conductor.sub_mem hx (Ideal.mul_le_left hby)
  have hbm : b - 1 ∈ η.conductor * χ.conductor := by
    have heq : b - 1 = y + (b - (1+y)) := by ring
    rw [heq]; exact (η.conductor * χ.conductor).add_mem hy (Ideal.mul_le_right hby)
  have hbcop : Ideal.span {b} ⊔ ψ.conductor = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have hba : a ∈ Ideal.span {b} ⊔ ψ.conductor := by
      have hb := Ideal.mem_sup_left (T := ψ.conductor) (Ideal.mem_span_singleton_self b)
      have hd := Ideal.mem_sup_right (S := Ideal.span {b}) hab
      simpa using (Ideal.span {b} ⊔ ψ.conductor).add_mem hb hd
    have hle' : Ideal.span {a} ⊔ ψ.conductor ≤ Ideal.span {b} ⊔ ψ.conductor :=
      sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hba) le_sup_right
    rw [hcop] at hle'
    exact hle' (by trivial)
  have hb0 : b ≠ 0 := by
    intro hb0
    simp [hb0] at hbcop
    exact hf hbcop
  have hcopm := coprime_of_sub_one_mem (η.conductor * χ.conductor) b hbm
  have hcopall : Ideal.span {b} ⊔ (η.conductor * χ.conductor * ψ.conductor) = ⊤ := by
    apply IsCoprime.sup_eq
    exact (Ideal.isCoprime_iff_sup_eq.mpr hcopm).mul_right
      (Ideal.isCoprime_iff_sup_eq.mpr hbcop)
  have hη : η.character (Ideal.span {b}) = 1 :=
    η.character.map_span' b hb0 (Ideal.mul_le_left hbm) hposb
  have hχ : χ.character (Ideal.span {b}) = 1 :=
    χ.character.map_span' b hb0 (Ideal.mul_le_right hbm) hposb
  have hψ := hTwist (Ideal.span {b}) (by simpa using hb0) hcopall
  have heq := ray_congruent_positive F ψ.conductor ψ.conductor_ne_zero hf ψ.character a b ha hb0 hpos hposb hcop hab
  apply hne
  rw [heq, hψ, hη, hχ, map_one, mul_one]

end

end DedekindZetaZeroFree.Detector

module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Identification
public import DedekindZetaZeroFree.Moments.Principal.Contour.ResidueFormulas

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RightHeckeBounds

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

section Helpers

open scoped Classical NumberField Topology
open IsDedekindDomain Filter

private theorem fpd_hasSum
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

private theorem norm_power (q : ℝ) (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ s = comparisonRealPower q s := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne')]
  rw [← Complex.ofReal_log hq.le]
  unfold comparisonRealPower
  congr 1
  ring

private theorem L_eq_zeta (R : PrincipalMellin.ActualRecipe S η)
    (s : ℂ) (hs : 1 < s.re) : R.L s = InitialSeparatedEuler.zetaS R.A s := by
  let W : Ideal (𝓞 F) → ℂ := fun I => R.target I * (Ideal.absNorm I : ℂ) ^ (-s)
  have hW0 : W ⊥ = 0 := by simp [W, (R.target.eq_zero_iff' ⊥).mpr (Or.inl rfl)]
  have hWmul (a b : Ideal (𝓞 F)) : W (a*b) = W a * W b := by
    dsimp [W]
    rw [R.target.map_mul', map_mul Ideal.absNorm, Nat.cast_mul]
    have hp : ((Ideal.absNorm a : ℂ) * (Ideal.absNorm b : ℂ)) ^ (-s) =
        (Ideal.absNorm a : ℂ) ^ (-s) * (Ideal.absNorm b : ℂ) ^ (-s) := by
      exact_mod_cast Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg (Ideal.absNorm a) : (0 : ℝ) ≤ Ideal.absNorm a)
        (Nat.cast_nonneg (Ideal.absNorm b) : (0 : ℝ) ≤ Ideal.absNorm b) (-s)
    rw [hp]; ring
  have hdel := fpd_hasSum F W hW0 hWmul _
    (R.continuation.series s hs) R.A.Sf
  let g : Ideal (𝓞 F) → ℂ := fun I => if ∃ v ∈ R.A.Sf, I ≤ v.asIdeal then 0 else W I
  have hg : Function.support g ⊆ {I | I ≠ ⊥ ∧ I ⊔ R.A.cS = ⊤} := by
    intro I hI
    have hi : I ≠ ⊥ := by intro h; subst I; simpa [g, W, hW0] using hI
    refine ⟨hi, ?_⟩
    apply (R.A.exterior_iff ⟨I, hi⟩).mpr
    intro v hv
    have hn : ¬ I ≤ v.asIdeal := by
      intro h
      exact hI (by simp [g, show ∃ v ∈ R.A.Sf, I ≤ v.asIdeal from ⟨v,hv,h⟩])
    by_contra ht
    have he := v.isMaximal.eq_of_le ht le_sup_right
    exact hn (by rw [he]; exact le_sup_left)
  have hext := (hasSum_subtype_iff_of_support_subset hg).mpr hdel
  have heq (I : R.A.Exterior) : g I.val = (Ideal.absNorm I.val : ℂ)^(-s) := by
    have hn : ¬ ∃ v ∈ R.A.Sf, I.val ≤ v.asIdeal := by
      rintro ⟨v,hv,h⟩
      have ht := (R.A.exterior_iff ⟨I.val,I.property.1⟩).mp I.property.2 v hv
      have : I.val ⊔ v.asIdeal ≤ v.asIdeal := sup_le h le_rfl
      rw [ht] at this
      exact v.isMaximal.ne_top (top_unique this)
    rw [show g I.val = W I.val by simp [g,hn]]
    dsimp [W]
    rw [R.probe.principal I.val I.property.1 ?_, one_mul]
    by_contra h
    obtain ⟨p,hp,hle⟩ := Ideal.exists_le_maximal (I.val ⊔ R.A.modulus) h
    have hmod : R.A.modulus ≤ p := le_sup_right.trans hle
    have hp0 : p ≠ ⊥ := ne_bot_of_le_ne_bot R.A.modulus_ne_zero hmod
    let v : HeightOneSpectrum (𝓞 F) := ⟨p,hp.isPrime,hp0⟩
    have ht := (R.A.exterior_iff ⟨I.val,I.property.1⟩).mp I.property.2 v
      (R.A.modulus_support v hmod)
    have : I.val ⊔ p ≤ p := sup_le (le_sup_left.trans hle) le_rfl
    rw [ht] at this
    exact hp.ne_top (top_unique this)
  have hres := hext.tsum_eq.symm
  simp only [Function.comp_def] at hres
  change _ = ∑' I : R.A.Exterior, g I.val at hres
  simp_rw [heq] at hres
  convert hres using 1
  · unfold PrincipalMellin.ActualRecipe.L comparisonPrincipalIncompleteL
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    dsimp [W, idealNorm]
    rw [← norm_power (Ideal.absNorm v.asIdeal : ℝ) (by
      exact_mod_cast (lt_trans Nat.zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)))]
    simp only [Complex.ofReal_natCast]
  · rfl

end Helpers

section Euler

open scoped Classical NumberField

theorem euler_data {cS : Ideal (𝓞 F)} (a : ExteriorIdeal cS → ℂ)
    (ha : ExteriorIdealEuler.IsCoefficient a) (σ : ℝ) (hσ : 1 < σ) (s : ℂ) (hs : σ ≤ s.re) :
    (∑' I : ExteriorIdeal cS, ExteriorIdealEuler.summand a s I) ≠ 0 ∧
    ‖∑' I : ExteriorIdeal cS, ExteriorIdealEuler.summand a s I‖ ≤
      Real.exp ((3 / 2 : ℝ) * ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-σ)) ∧
    ‖(∑' I : ExteriorIdeal cS, ExteriorIdealEuler.summand a s I)⁻¹‖ ≤
      Real.exp ((3 / 2 : ℝ) * ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-σ)) := by
  have hs1 : 1 < s.re := lt_of_lt_of_le hσ hs
  have h := HeckeLogProof.exp_eulerLog a ha s hs1
  have hL := HeckeLogProof.eulerLog_norm_le a ha σ hσ s hs
  rw [← h]
  refine ⟨Complex.exp_ne_zero _, ?_, ?_⟩
  · rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hL)
  · rw [← Complex.exp_neg, Complex.norm_exp]
    refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
    rw [norm_neg]
    exact hL

variable {A : SArithmeticData F} {σ : F →+* ℂ} {η' : RayClassCharacter F A.modulus}
  {hS : A.ContainsTraceBadPlaces} {C : A.GeneralArithmeticContext σ η' hS}

theorem incompleteL_plus_eq (U : CorrectionFactors.Frequency C) (s : ℂ) :
    MaskedHeckeMeromorphic.incompleteL U MaskedHeckeMeromorphic.Row.plus s =
      ∑' I : A.Exterior, ExteriorIdealEuler.summand
        (FrequencyCharacterMasks.plusExteriorCoefficient U) s I := by
  have hsupport : Function.support (fun I : Ideal (𝓞 F) =>
      MaskedHeckeMeromorphic.coefficient U MaskedHeckeMeromorphic.Row.plus I *
        (Ideal.absNorm I : ℂ) ^ (-s)) ⊆ {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ A.cS = ⊤} := by
    intro I hI
    by_contra hn
    change ¬ (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) at hn
    apply hI
    simp [MaskedHeckeMeromorphic.coefficient, FrequencyCharacterMasks.plusCoefficient, hn]
  have he := (tsum_subtype_eq_of_support_subset hsupport).symm
  unfold MaskedHeckeMeromorphic.incompleteL
  rw [he]
  apply tsum_congr
  intro I
  simp [MaskedHeckeMeromorphic.coefficient, FrequencyCharacterMasks.plusCoefficient,
    I.property.1, I.property.2, ExteriorIdealEuler.summand]

theorem incompleteL_minus_eq (U : CorrectionFactors.Frequency C) (s : ℂ) :
    MaskedHeckeMeromorphic.incompleteL U MaskedHeckeMeromorphic.Row.minus s =
      ∑' I : A.Exterior, ExteriorIdealEuler.summand
        (FrequencyCharacterMasks.minusExteriorCoefficient U) s I := by
  have hsupport : Function.support (fun I : Ideal (𝓞 F) =>
      MaskedHeckeMeromorphic.coefficient U MaskedHeckeMeromorphic.Row.minus I *
        (Ideal.absNorm I : ℂ) ^ (-s)) ⊆ {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ A.cS = ⊤} := by
    intro I hI
    by_contra hn
    change ¬ (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) at hn
    apply hI
    simp [MaskedHeckeMeromorphic.coefficient, FrequencyCharacterMasks.plusCoefficient,
      FrequencyCharacterMasks.minusCoefficient, hn]
  have he := (tsum_subtype_eq_of_support_subset hsupport).symm
  unfold MaskedHeckeMeromorphic.incompleteL
  rw [he]
  apply tsum_congr
  intro I
  simp [MaskedHeckeMeromorphic.coefficient, FrequencyCharacterMasks.plusCoefficient,
    FrequencyCharacterMasks.minusCoefficient, FrequencyCharacterMasks.minusExteriorCoefficient,
    I.property.1, I.property.2, ExteriorIdealEuler.summand]

theorem Lpsi_eq_tsum (u : D.Row) (s : ℂ) (hs : 1 < s.re) :
    D.Lpsi u s = ∑' I : D.recipe.A.Exterior, ExteriorIdealEuler.summand
      (FrequencyCharacterMasks.plusExteriorCoefficient u.toFrequency) s I := by
  rw [D.Lpsi_eq_raw u s hs]
  exact incompleteL_plus_eq u.toFrequency s

theorem Llam_eq_tsum (u : D.Row) (s : ℂ) (hs : 1 < s.re) :
    D.Llam u s = ∑' I : D.recipe.A.Exterior, ExteriorIdealEuler.summand
      (FrequencyCharacterMasks.minusExteriorCoefficient u.toFrequency) s I := by
  rw [D.Llam_eq_raw u s hs]
  exact incompleteL_minus_eq u.toFrequency s

theorem zetaS_eq_tsum (s : ℂ) :
    D.zetaS s = ∑' I : D.recipe.A.Exterior,
      ExteriorIdealEuler.summand (fun _ => (1 : ℂ)) s I := by
  unfold FixedData.zetaS InitialSeparatedEuler.zetaS
  exact tsum_congr (fun I => by simp [ExteriorIdealEuler.summand])

end Euler

theorem zetaSCont_eq_zetaS (s : ℂ) (hs : 1 < s.re) : D.zetaSCont s = D.zetaS s :=
  L_eq_zeta D.recipe s hs

theorem Lpsi_ne_zero_of_one_lt (u : D.Row) (s : ℂ) (hs : 1 < s.re) : D.Lpsi u s ≠ 0 := by
  rw [Lpsi_eq_tsum D u s hs]
  exact (euler_data _ (FrequencyCharacterMasks.actual_coefficients_multiplicative
    u.toFrequency).1 s.re hs s le_rfl).1

theorem Llam_ne_zero_of_one_lt (u : D.Row) (s : ℂ) (hs : 1 < s.re) : D.Llam u s ≠ 0 := by
  rw [Llam_eq_tsum D u s hs]
  exact (euler_data _ (FrequencyCharacterMasks.actual_coefficients_multiplicative
    u.toFrequency).2.1 s.re hs s le_rfl).1

theorem zetaSCont_ne_zero_of_one_lt (s : ℂ) (hs : 1 < s.re) : D.zetaSCont s ≠ 0 := by
  rw [zetaSCont_eq_zetaS D s hs, zetaS_eq_tsum D s]
  exact (euler_data _ (ExteriorIdealEuler.constant_one_isCoefficient D.recipe.A.cS)
    s.re hs s le_rfl).1

theorem Lpsi_norm_le_right (a : ℝ) (ha : 1 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : D.Row) (s : ℂ), a ≤ s.re → ‖D.Lpsi u s‖ ≤ C := by
  refine ⟨Real.exp ((3 / 2 : ℝ) * ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-a)),
    Real.exp_pos _, fun u s hs => ?_⟩
  rw [Lpsi_eq_tsum D u s (lt_of_lt_of_le ha hs)]
  exact (euler_data _ (FrequencyCharacterMasks.actual_coefficients_multiplicative
    u.toFrequency).1 a ha s hs).2.1

theorem Llam_inv_norm_le_right (a : ℝ) (ha : 1 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : D.Row) (s : ℂ), a ≤ s.re → ‖(D.Llam u s)⁻¹‖ ≤ C := by
  refine ⟨Real.exp ((3 / 2 : ℝ) * ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-a)),
    Real.exp_pos _, fun u s hs => ?_⟩
  rw [Llam_eq_tsum D u s (lt_of_lt_of_le ha hs)]
  exact (euler_data _ (FrequencyCharacterMasks.actual_coefficients_multiplicative
    u.toFrequency).2.1 a ha s hs).2.2

theorem zetaSCont_norm_le_right (a : ℝ) (ha : 1 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → ‖D.zetaSCont s‖ ≤ C := by
  obtain ⟨B, hB, h⟩ := PrincipalNumerator.rightHalfPlane_bound D.recipe a ha
  exact ⟨B, hB, fun s hs => h s hs⟩

theorem zetaSCont_inv_norm_le_right (a : ℝ) (ha : 1 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → ‖(D.zetaSCont s)⁻¹‖ ≤ C := by
  obtain ⟨B, hB, h⟩ := PrincipalNumerator.rightHalfPlane_reciprocal_bound D.recipe a ha
  exact ⟨B, hB, fun s hs => h s hs⟩

theorem zetaSCont_analyticOnNhd :
    AnalyticOnNhd ℂ D.zetaSCont ({s : ℂ | 0 < s.re} \ {1}) := by
  have hopen : IsOpen ({s : ℂ | 0 < s.re} \ {1}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hL : DifferentiableOn ℂ D.recipe.continuation.L ({s : ℂ | 0 < s.re} \ {1}) := by
    refine D.recipe.continuation.L_holo.mono ?_
    intro s hs
    exact ⟨hs.1, hs.2⟩
  have hLa := hL.analyticOnNhd hopen
  intro s hs
  have h1 : AnalyticAt ℂ D.recipe.continuation.L s := hLa s hs
  have h2 : AnalyticAt ℂ (fun z : ℂ => ∏ v ∈ D.recipe.A.Sf,
      (1 - D.recipe.target v.asIdeal *
        comparisonRealPower (idealNorm v.asIdeal) (-z))) s := by
    apply Finset.analyticAt_fun_prod
    intro v _
    refine analyticAt_const.sub (analyticAt_const.mul ?_)
    unfold comparisonRealPower
    exact ((analyticAt_id.neg).mul analyticAt_const).cexp
  exact h1.mul h2

theorem Lpsi_analyticOnNhd_of_nonprincipal (u : D.Row)
    (hnp : ¬ (D.inducers u).plus.character.IsPrincipal) :
    AnalyticOnNhd ℂ (D.Lpsi u) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hJ := (D.rowContinuation u .plus).J_holomorphic s hs
  have hB := (D.rowContinuation u .plus).B_holomorphic s hs
  have hδ : MaskedHeckeMeromorphic.poleIndicator (D.inducers u).plus = 0 := by
    unfold MaskedHeckeMeromorphic.poleIndicator
    exact if_neg hnp
  have h : D.Lpsi u = fun z => (D.rowContinuation u .plus).J z *
      MaskedHeckeMeromorphic.deletionProduct u.toFrequency (D.inducers u)
        MaskedHeckeMeromorphic.Row.plus z := by
    funext z
    rw [D.Lpsi_eq_J_mask u z, hδ, pow_zero, div_one] <;> rfl
  rw [h]
  exact hJ.mul hB

theorem Llam_analyticOnNhd_of_nonprincipal (u : D.Row)
    (hnp : ¬ (D.inducers u).minus.character.IsPrincipal) :
    AnalyticOnNhd ℂ (D.Llam u) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hJ := (D.rowContinuation u .minus).J_holomorphic s hs
  have hB := (D.rowContinuation u .minus).B_holomorphic s hs
  have hδ : MaskedHeckeMeromorphic.poleIndicator (D.omega u) = 0 := by
    unfold MaskedHeckeMeromorphic.poleIndicator
    exact if_neg hnp
  have h : D.Llam u = fun z => (D.rowContinuation u .minus).J z *
      MaskedHeckeMeromorphic.deletionProduct u.toFrequency (D.inducers u)
        MaskedHeckeMeromorphic.Row.minus z := by
    funext z
    rw [D.Llam_eq_J_mask u z, hδ, pow_zero, div_one] <;> rfl
  rw [h]
  exact hJ.mul hB

theorem Lpsi_polynomial_growth_principal (u : D.Row) (hu : u.u = 1) (σ0 σ1 : ℝ)
    (h0 : 0 < σ0) (h01 : σ0 ≤ σ1) (h1 : 1 ∉ Set.Icc σ0 σ1) :
    ∃ (C B : ℝ), 0 < C ∧ ∀ (σ : ℝ) (t : ℝ), σ ∈ Set.Icc σ0 σ1 →
      ‖D.Lpsi u ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ B := by
  obtain ⟨ρ, hρ, hρb⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ σ ∈ Set.Icc σ0 σ1, ρ ≤ |σ - 1| := by
    by_cases hlt : σ1 < 1
    · refine ⟨1 - σ1, by linarith, fun σ hσ => ?_⟩
      rw [abs_of_neg (by linarith [hσ.2])]
      linarith [hσ.2]
    · have hgt : 1 < σ0 := by
        by_contra hc
        exact h1 ⟨by linarith, by linarith⟩
      refine ⟨σ0 - 1, by linarith, fun σ hσ => ?_⟩
      rw [abs_of_pos (by linarith [hσ.1])]
      linarith [hσ.1]
  obtain ⟨B1, d, hB1, hd, hbd⟩ := PrincipalNumerator.stripNumerator_bound_away_pole D.recipe
    (min σ0 4) 4 ρ (lt_min h0 (by norm_num)) (min_le_right _ _) le_rfl hρ
  obtain ⟨K, hK, hKb⟩ := zetaSCont_norm_le_right D 4 (by norm_num)
  have h2d : 0 < (2 : ℝ) ^ d := by positivity
  refine ⟨B1 * 2 ^ d + K, d, by positivity, ?_⟩
  intro σ t hσ
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  have hpos : 0 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by rw [hre]; linarith [hσ.1]
  have hne : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro h
    apply h1
    have hσ1 : σ = 1 := by
      have := congrArg Complex.re h
      rw [hre] at this
      simpa using this
    rw [← hσ1]
    exact hσ
  rw [PrincipalResidueFormulas.Lpsi_principal_eq D u hu _ hpos hne]
  have hp : 0 ≤ (1 + |t|) ^ d := Real.rpow_nonneg (by positivity) d
  have hone : (1 : ℝ) ≤ (1 + |t|) ^ d :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) hd
  by_cases h4 : σ ≤ 4
  · have hsep : ρ ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ := by
      calc ρ ≤ |σ - 1| := hρb σ hσ
        _ = |(((σ : ℂ) + (t : ℂ) * Complex.I) - 1).re| := by simp
        _ ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ := Complex.abs_re_le_norm _
    have h : ‖D.zetaSCont ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        B1 * (2 + |((σ : ℂ) + (t : ℂ) * Complex.I).im|) ^ d :=
      hbd _ (by rw [hre]; exact (min_le_left _ _).trans hσ.1) (by rw [hre]; exact h4) hsep
    rw [him] at h
    have hrp : (2 + |t|) ^ d ≤ 2 ^ d * (1 + |t|) ^ d := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg t]) hd
    calc ‖D.zetaSCont ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B1 * (2 + |t|) ^ d := h
      _ ≤ B1 * (2 ^ d * (1 + |t|) ^ d) := mul_le_mul_of_nonneg_left hrp hB1.le
      _ = B1 * 2 ^ d * (1 + |t|) ^ d := by ring
      _ ≤ (B1 * 2 ^ d + K) * (1 + |t|) ^ d := by nlinarith [mul_nonneg hK.le hp]
  · have h4' : 4 ≤ σ := (not_le.mp h4).le
    have h := hKb ((σ : ℂ) + (t : ℂ) * Complex.I) (by rw [hre]; exact h4')
    calc ‖D.zetaSCont ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K := h
      _ = K * 1 := (mul_one _).symm
      _ ≤ K * (1 + |t|) ^ d := mul_le_mul_of_nonneg_left hone hK.le
      _ ≤ (B1 * 2 ^ d + K) * (1 + |t|) ^ d := by
        nlinarith [mul_nonneg (mul_nonneg hB1.le h2d.le) hp]

end DedekindZetaZeroFree.Quantitative.RightHeckeBounds

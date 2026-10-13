module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.Domain

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PoissonKernel

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def rawRowFactor (u : D.Row) (ξ w z : ℂ) : ℂ :=
  comparisonEulerPoissonSeries F D.recipe.A D.recipe.probe.coefficients (FixedData.Row.u u) ξ w z

def rowFactor (u : D.Row) (ξ w z : ℂ) : ℂ :=
  D.zetaSCont (6 * z) * D.Lpsi u w / D.Llam u ξ * EulerDomain.Hu D u ξ w z

section RowFactorAux

open DedekindZetaZeroFree.MaskedHeckeMeromorphic LocalFiniteSums CorrectionFactors FrequencyCharacterMasks
open IsDedekindDomain Filter
open scoped NumberField Topology

private theorem rf_finite_prime_delete_hasSum
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

private theorem rf_L_eq_zeta (R : PrincipalMellin.ActualRecipe S η)
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
  have hdel := rf_finite_prime_delete_hasSum F W hW0 hWmul _
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

variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η' : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η' hS}

private lemma rf_row_matches (U : Frequency C) (s : ℂ) :
    incompleteL U .principal s = InitialSeparatedEuler.zetaS A s ∧
    incompleteL U .plus s = InitialSeparatedEuler.plusL U s ∧
    incompleteL U .minus s = InitialSeparatedEuler.minusL U s := by
  have hsupport (i : Row) : Function.support (fun I : Ideal (𝓞 F) =>
      coefficient U i I * (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
      {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ A.cS = ⊤} := by
    intro I hI
    by_contra hn
    change ¬ (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) at hn
    apply hI
    cases i <;> simp [coefficient, principalCoefficient, plusCoefficient, minusCoefficient, hn]
  have he (i : Row) := (tsum_subtype_eq_of_support_subset (hsupport i)).symm
  refine ⟨?_, ?_, ?_⟩
  · change incompleteL U .principal s = _
    rw [show incompleteL U .principal s = _ from he .principal]
    unfold InitialSeparatedEuler.zetaS
    apply tsum_congr
    intro I
    simp [coefficient, principalCoefficient, I.property.1, I.property.2]
  · change incompleteL U .plus s = _
    rw [show incompleteL U .plus s = _ from he .plus]
    unfold InitialSeparatedEuler.plusL InitialSeparatedEuler.dirichletSeries
    apply tsum_congr
    intro I
    simp [coefficient, plusCoefficient, I.property.1, I.property.2, InitialSeparatedEuler.plusL,
      InitialSeparatedEuler.dirichletSeries, ExteriorIdealEuler.summand]
  · change incompleteL U .minus s = _
    rw [show incompleteL U .minus s = _ from he .minus]
    unfold InitialSeparatedEuler.minusL InitialSeparatedEuler.dirichletSeries
    apply tsum_congr
    intro I
    simp [coefficient, plusCoefficient, minusCoefficient, I.property.1, I.property.2,
      minusExteriorCoefficient, ExteriorIdealEuler.summand]

end RowFactorAux

theorem rowFactor_eq_raw (u : D.Row) (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re)
    (hz : 2 < z.re) : rowFactor D u ξ w z = rawRowFactor D u ξ w z := by
  have hξ1 : 1 < ξ.re := by linarith
  have hw1 : 1 < w.re := by linarith
  have hz1 : 1 < (6 * z).re := by simp; linarith
  have hD := DedekindZetaZeroFree.PrincipalMellinComparison.principal_arithmetic_compatibility D.recipe D.context rfl
  have hQ := InitialSeparatedEuler.initial_separated_euler_quotient u.toFrequency
    D.recipe.probe.coefficients hD ξ w z hξ hw hz
  have hL := rf_L_eq_zeta D.recipe (6 * z) hz1
  have hP : D.Lpsi u w = InitialSeparatedEuler.plusL u.toFrequency w := by
    rw [FixedData.Lpsi_eq_raw D u w hw1]
    exact (rf_row_matches u.toFrequency w).2.1
  have hM : D.Llam u ξ = InitialSeparatedEuler.minusL u.toFrequency ξ := by
    rw [FixedData.Llam_eq_raw D u ξ hξ1]
    exact (rf_row_matches u.toFrequency ξ).2.2
  unfold rowFactor rawRowFactor
  rw [show FixedData.Row.u u = u.toFrequency.u from rfl, hQ]
  unfold FixedData.zetaSCont EulerDomain.Hu CorrectionFactors.H_u
  rw [hL, hP, hM]
  ring

def kernelWith (Fu : D.Row → ℂ → ℂ → ℂ → ℂ) (u : D.Row) (ξ w z : ℂ) (Z : ℝ) : ℂ :=
  (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w - 1)) *
    Complex.exp ((ξ + z - 1) ^ 2) * D.M z * D.W1Hat w * (D.q u : ℂ) ^ (-z) * Fu u ξ w z

def K (u : D.Row) (ξ w z : ℂ) (Z : ℝ) : ℂ := kernelWith D (rowFactor D) u ξ w z Z

def wzIntegral (u : D.Row) (ξ : ℂ) (y v Z : ℝ) : ℂ :=
  comparisonVerticalIntegral y (fun w =>
    comparisonVerticalIntegral v (fun z => K D u ξ w z Z))

def J (C : Set D.Row) (x y v Z : ℝ) : ℂ :=
  ∑ᶠ u ∈ C, comparisonVerticalIntegral x (fun ξ => wzIntegral D u ξ y v Z)

def principalRows : Set D.Row := {u | FixedData.Row.u u = 1}

def Jpr (Z : ℝ) : ℂ := J D (principalRows D) 4 4 2 Z

def dyadRows (U : ℝ) : Set D.Row := {u | U ≤ D.q u ∧ D.q u < 2 * U}

def Jdyad (U Z : ℝ) : ℂ := J D (dyadRows D U) 4 4 2 Z

def Jcentral (C : Set D.Row) (x y v T Z : ℝ) : ℂ :=
  ∑ᶠ u ∈ C, (2 * (Real.pi : ℂ))⁻¹ *
    ∫ t in Set.Icc (-T) T, wzIntegral D u ((x : ℂ) + (t : ℂ) * Complex.I) y v Z

def Jhoriz (C : Set D.Row) (sgn : ℝ) (x₀ x₁ y v T Z : ℝ) : ℂ :=
  ∑ᶠ u ∈ C, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ σ in x₀..x₁, wzIntegral D u ((σ : ℂ) + (sgn * T : ℝ) * Complex.I) y v Z

end

end DedekindZetaZeroFree.Quantitative.PoissonKernel

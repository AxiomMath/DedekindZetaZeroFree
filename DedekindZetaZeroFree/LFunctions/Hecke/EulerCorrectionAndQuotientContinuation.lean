module

public import DedekindZetaZeroFree.LFunctions.Hecke.NonprincipalMaskedRowInducers
public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalInitialEulerSeparation

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor
noncomputable section
open scoped Classical NumberField Topology
open IsDedekindDomain Filter
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

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
  have hdel := finite_prime_delete_hasSum F W hW0 hWmul _
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

private theorem principal_coefficient_field_trace
    (R : PrincipalMellin.ActualRecipe S η) (x : F) :
    R.probe.coefficients.additiveCharacter x = (R.A.fieldTraceCharacter x : ℂ) := by
  rw [R.probe.sameTrace, PrincipalProbeConstruction.Inputs.fieldTrace_phase]
  congr 1
  funext v
  exact R.normalization.sameFiniteTrace v

private theorem principal_arithmetic_binding (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction) :
    PrincipalProbeConstruction.ArithmeticBinding R.A R.σ R.target R.traceBad
      C R.probe.allowed R.probe.coefficients := by
  refine ⟨R.probe.sameComplement.trans (congrArg (fun D => D.B) hC),
    R.probe.sameGenerator, R.probe.exteriorCharacters, ?_, R.probe.gammaTwo_recipe,
    R.probe.sixthUnitCharacters, principal_coefficient_field_trace R, ?_⟩
  · intro m
    rw [R.probe.theta_principal, hC]
  · intro x
    rw [principal_coefficient_field_trace R,
      PrincipalProbeConstruction.Inputs.fieldTrace_phase]

private theorem principal_arithmetic_compatibility (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction) :
    WeightedFiniteCoefficient.ArithmeticCompatibility R.A R.probe.coefficients
      R.σ R.target R.traceBad C.correction := by
  exact PrincipalCorrection.probe_arithmetic_compatibility C R.probe hC
    (principal_arithmetic_binding R C hC)

theorem initial_continuation_agreement
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (plus minus : Frequency R → ℂ → ℂ)
    (hC : R.probe.correction = C.correction)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val)
    (hplusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      plus u s = AllRowEuler.InitialSeparation.plusL R.σ (U u) s)
    (hminusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      minus u s = AllRowEuler.InitialSeparation.minusL R.σ R.target (U u) s)
    (u : Frequency R) (ξ w z : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) (hz : z.re = 2) :
    separatedSeries R u ξ w z =
      (R.L (6 * z) * plus u w *
        AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z) / minus u ξ := by
  have hD := principal_arithmetic_compatibility R C hC
  have h := AllRowEuler.InitialSeparation.initial_euler_quotient C R.probe.coefficients hD
    (U u) ξ w z hξ hw hz
  rw [hU u] at h
  rw [← L_eq_zeta R (6 * z) (by norm_num [Complex.mul_re, hz])] at h
  rw [← hplusSeries u w (by rw [hw]; norm_num)] at h
  rw [← hminusSeries u ξ (by rw [hξ]; norm_num)] at h
  simpa only [separatedSeries, NormalizedProbe.principalSeparatedMellinSeries,
    NormalizedProbe.separatedMellinSeries] using h

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor
noncomputable section
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem raw_frequency_unit_part_isUnit_of_zero_prime_exponent
    (C : A.GeneralArithmeticContext σ η hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (p : ExteriorPrime A)
    (hp : (U.j p).val = 0) :
    IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) := by
  have hs := AllRowEuler.InitialSeparation.RawFrequency.unitPart_spec C U p
  rw [hs.1, hp, pow_zero, one_mul]
  exact hs.2

theorem raw_local_correction_differentiableOn
    (C : A.GeneralArithmeticContext σ η hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (p : ExteriorPrime A) :
    DifferentiableOn ℂ
      (fun x : CorrectionFactors.Coordinates =>
        AllRowEuler.InitialSeparation.localCorrection C U p x.1 x.2.1 x.2.2)
      CorrectionFactors.Omega := by
  by_cases hj : (U.j p).val = 0
  · have hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) :=
      raw_frequency_unit_part_isUnit_of_zero_prime_exponent C U p hj
    simpa only [AllRowEuler.InitialSeparation.localCorrection, if_pos hj] using
      CorrectionFactors.good_correction_holomorphic C p U.u hu
  · simpa only [AllRowEuler.InitialSeparation.localCorrection, if_neg hj] using
      CorrectionFactors.bad_factor_holomorphic C p (U.j p) hj
        (AllRowEuler.InitialSeparation.RawFrequency.theta C U p)

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor
noncomputable section
open scoped Classical NumberField
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem raw_good_cofinite (U : AllRowEuler.InitialSeparation.RawFrequency A) :
    ∀ᶠ p : ExteriorPrime A in Filter.cofinite, (U.j p).val = 0 := by
  apply Filter.eventually_cofinite.mpr
  have hinj : Function.Injective (fun p : ExteriorPrime A => p.val.asIdeal) :=
    IsDedekindDomain.HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective
  simpa [AllRowEuler.InitialSeparation.RawFrequency.j, idealPrimeExponent,
    Multiset.count_eq_zero] using
    (UniqueFactorizationMonoid.normalizedFactors U.ideal.val).finite_toSet.preimage
      hinj.injOn

private theorem raw_frequency_unit_residue_isUnit_of_zero_prime_exponent (C : A.GeneralArithmeticContext σ η hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (p : ExteriorPrime A)
    (hp : (U.j p).val = 0) :
    IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) := by
  have hs := AllRowEuler.InitialSeparation.RawFrequency.unitPart_spec C U p
  rw [hs.1, hp, pow_zero, one_mul]
  exact hs.2

private theorem raw_good_majorant_summable (M : ℝ) :
    Summable (fun p : ExteriorPrime A =>
      M * (Q p) ^ (-(1 + 1 / 4000 : ℝ))) := by
  let i : ExteriorPrime A → {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // p ∉ A.Sf} :=
    fun p => ⟨p.val, by
      intro hp
      have he := (A.exterior_iff ⟨p.val.asIdeal, p.val.ne_bot⟩).mp p.property p.val hp
      simp only [sup_idem] at he
      exact p.val.isPrime.ne_top he⟩
  have hi : Function.Injective i := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun r : {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // p ∉ A.Sf} => r.val) h
  have hs := (summable_exterior_prime_norm_rpow F A.Sf (1 + 1 / 4000) (by norm_num)).comp_injective hi
  simpa [Function.comp_def, i, Q, SArithmeticData.exteriorNorm, idealNorm, primeIdeal]
    using hs.mul_left M

theorem raw_correction_compact_majorant
    (C : A.GeneralArithmeticContext σ η hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (K : Set CorrectionFactors.Coordinates) (hKO : K ⊆ CorrectionFactors.Omega)
    (hK : IsCompact K) :
    ∃ M : ExteriorPrime A → ℝ, Summable M ∧
      ∀ p x, x ∈ K →
        ‖AllRowEuler.InitialSeparation.localCorrection C U p x.1 x.2.1 x.2.2 - 1‖ ≤ M p := by
  classical
  obtain ⟨M₀, hM₀, hgood⟩ := CorrectionFactors.good_correction_uniform_bound
  obtain ⟨B, hB, hbad⟩ := CorrectionFactors.bad_factor_uniform_estimate C
  refine ⟨fun p => M₀ * (Q p) ^ (-(1 + 1 / 4000 : ℝ)) +
      (if (U.j p).val = 0 then 0 else B * (Q p) ^ (-(1 / 4000 : ℝ))), ?_, ?_⟩
  · have hg : Summable (fun p : ExteriorPrime A =>
        M₀ * (Q p) ^ (-(1 + 1 / 4000 : ℝ))) :=
      raw_good_majorant_summable (A := A) M₀
    have hb : Summable (fun p : ExteriorPrime A =>
        if (U.j p).val = 0 then (0 : ℝ) else B * (Q p) ^ (-(1 / 4000 : ℝ))) := by
      apply summable_of_hasFiniteSupport
      refine Set.Finite.subset (Filter.eventually_cofinite.mp (raw_good_cofinite U)) ?_
      intro p hp
      simp only [Set.mem_setOf_eq, Function.mem_support] at hp ⊢
      intro h0
      rw [if_pos h0] at hp
      exact hp rfl
    exact hg.add hb
  · intro p x hx
    have hxO : x ∈ CorrectionFactors.Omega := hKO hx
    have hQ : (0 : ℝ) ≤ Q p := (A.exteriorNorm_pos (primeIdeal p)).le
    by_cases hp : (U.j p).val = 0
    · have hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) :=
        raw_frequency_unit_residue_isUnit_of_zero_prime_exponent C U p hp
      have hb := hgood F A σ η hS C p U.u hu x hxO
      simp only [AllRowEuler.InitialSeparation.localCorrection, hp, if_true] at hb ⊢
      have h2 : (0 : ℝ) ≤
          (if (U.j p).val = 0 then (0 : ℝ) else B * (Q p) ^ (-(1 / 4000 : ℝ))) := by
        rw [if_pos hp]
      linarith
    · have hb := hbad p (U.j p) hp
          (AllRowEuler.InitialSeparation.RawFrequency.theta C U p) x hxO
      simp only [AllRowEuler.InitialSeparation.localCorrection, hp, if_false] at hb ⊢
      have h2 : (0 : ℝ) ≤ M₀ * (Q p) ^ (-(1 + 1 / 4000 : ℝ)) :=
        mul_nonneg hM₀.le (Real.rpow_nonneg hQ _)
      exact hb.trans (le_add_of_nonneg_left h2)

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor
noncomputable section
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem scalar_numerator_differentiableOn
    (R : PrincipalMellin.ActualRecipe S η)
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g {s : ℂ | 0 < s.re}) :
    DifferentiableOn ℂ
      (fun x : CorrectionFactors.Coordinates => R.L (6 * x.2.2) * g x.2.1)
      CorrectionFactors.omegaFirst := by

  have hRL : DifferentiableOn ℂ R.L {s : ℂ | 1 < s.re} := by
    have hP : DifferentiableOn ℂ R.continuation.L {s : ℂ | 1 < s.re} :=
      R.continuation.L_holo.mono (fun s hs => by
        simp only [Set.mem_setOf_eq] at hs ⊢
        exact ⟨by linarith, fun h => by rw [h] at hs; norm_num at hs⟩)
    have hmask : DifferentiableOn ℂ
        (fun s : ℂ => ∏ v ∈ R.A.Sf,
          (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)))
        {s : ℂ | 1 < s.re} := by
      apply DifferentiableOn.fun_finsetProd
      intro v _
      have hcp : DifferentiableOn ℂ
          (fun s : ℂ => comparisonRealPower (idealNorm v.asIdeal) (-s)) {s : ℂ | 1 < s.re} := by
        show DifferentiableOn ℂ
          (fun s : ℂ => Complex.exp ((-s) * (Real.log (idealNorm v.asIdeal) : ℂ)))
          {s : ℂ | 1 < s.re}
        fun_prop
      exact (differentiableOn_const (1 : ℂ)).sub (hcp.const_mul (R.target v.asIdeal))
    exact hP.mul hmask

  have hL : DifferentiableOn ℂ
      (fun x : CorrectionFactors.Coordinates => R.L (6 * x.2.2))
      CorrectionFactors.omegaFirst := by
    refine hRL.fun_comp ?_ ?_
    · fun_prop
    · intro x hx
      simp only [Set.mem_setOf_eq]
      have hx2 : (2 / 5 : ℝ) - 1 / 100000 < x.2.2.re := hx.2.2
      have hre : (6 * x.2.2).re = 6 * x.2.2.re := by
        rw [Complex.mul_re]; norm_num
      rw [hre]; linarith

  have hgx : DifferentiableOn ℂ (fun x : CorrectionFactors.Coordinates => g x.2.1)
      CorrectionFactors.omegaFirst := by
    refine hg.fun_comp ?_ ?_
    · fun_prop
    · intro x hx
      simp only [Set.mem_setOf_eq]
      have hx2 : (3 / 1000 : ℝ) - 1 / 100000 < x.2.1.re := hx.2.1
      linarith
  exact hL.mul hgx

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
noncomputable section
open scoped Classical
open Filter Set Metric

set_option maxHeartbeats 1500000

private theorem normal_holomorphic {ι : Type*} (g : ι → CorrectionFactors.Coordinates → ℂ)
    (U : Set CorrectionFactors.Coordinates) (hU : IsOpen U) (hg : ∀ i, DifferentiableOn ℂ (g i) U)
    (hM : ∀ K : Set CorrectionFactors.Coordinates, K ⊆ U → IsCompact K →
      ∃ M : ι → ℝ, Summable M ∧ ∀ i x, x ∈ K → ‖g i x‖ ≤ M i) :
    DifferentiableOn ℂ (fun x => ∑' i, g i x) U := by
  intro x hx
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨M, hMs, hMb⟩ := hM (closedBall x r) hsub (isCompact_closedBall x r)
  have hhalf : 0 < r / 2 := by positivity
  have hinside {y : CorrectionFactors.Coordinates} (hy : y ∈ ball x (r / 2)) : y ∈ closedBall x r := by
    exact ball_subset_closedBall (ball_subset_ball (by linarith) hy)
  have hderiv : ∀ i y, y ∈ ball x (r / 2) → ‖fderiv ℂ (g i) y‖ ≤ (4 / r) * M i := by
    intro i y hy
    have hball : ball y (r / 2) ⊆ closedBall x r := by
      intro z hz
      apply mem_closedBall.mpr
      have := dist_triangle z y x
      have hz' := mem_ball.mp hz
      have hy' := mem_ball.mp hy
      linarith
    have hnorm := Complex.norm_fderiv_le_div_of_mapsTo_ball
      ((hg i).mono (fun z hz => hsub (hball hz)))
      (R₂ := 2 * M i) (by
        intro z hz
        apply mem_closedBall.mpr
        calc
          dist (g i z) (g i y) ≤ ‖g i z‖ + ‖g i y‖ := by
            simpa only [dist_eq_norm_sub] using norm_sub_le (g i z) (g i y)
          _ ≤ 2 * M i := by linarith [hMb i z (hball hz), hMb i y (hinside hy)]) hhalf
    convert hnorm using 1 <;> field_simp <;> ring
  have hs := hasFDerivAt_tsum_of_isPreconnected (hMs.mul_left (4 / r)) isOpen_ball
    (convex_ball x (r / 2)).isPreconnected
    (fun i y hy => ((hg i y (hsub (hinside hy))).differentiableAt
      (hU.mem_nhds (hsub (hinside hy)))).hasFDerivAt) hderiv
    (mem_ball_self hhalf)
    (Summable.of_norm_bounded hMs (fun i => hMb i x (mem_closedBall_self hr.le)))
    (mem_ball_self hhalf)
  exact hs.differentiableAt.differentiableWithinAt

private theorem product_differentiableOn {ι : Type*} (f : ι → CorrectionFactors.Coordinates → ℂ)
    (hf : ∀ i, DifferentiableOn ℂ (f i) CorrectionFactors.Omega)
    (hM : ∀ K : Set CorrectionFactors.Coordinates, K ⊆ CorrectionFactors.Omega → IsCompact K →
      ∃ u : ι → ℝ, Summable u ∧ ∀ i x, x ∈ K → ‖f i x - 1‖ ≤ u i) :
    DifferentiableOn ℂ (fun x => ∏' i, f i x) CorrectionFactors.Omega := by
  have hd : DifferentiableOn ℂ
      (fun x => ∑' T : Finset ι, ∏ i ∈ T, (f i x - 1)) CorrectionFactors.Omega := by
    apply normal_holomorphic (fun T x => ∏ i ∈ T, (f i x - 1)) CorrectionFactors.Omega CorrectionFactors.isOpen_Omega
    · intro T
      induction T using Finset.induction_on with
      | empty => simpa using (differentiableOn_const (1 : ℂ))
      | insert i T hi ih =>
        have hEq : (fun x : CorrectionFactors.Coordinates => ∏ j ∈ insert i T, (f j x - 1))
            = (fun x => (f i x - 1) * ∏ j ∈ T, (f j x - 1)) := by
          funext x; rw [Finset.prod_insert hi]
        rw [hEq]
        exact ((hf i).sub_const 1).mul ih
    · intro K hKO hK
      obtain ⟨u, hu, hub⟩ := hM K hKO hK
      refine ⟨fun T => ∏ i ∈ T, max (u i) 0, ?_, ?_⟩
      · exact summable_finsetProd_of_summable_nonneg (fun i => le_max_right _ _)
          (hu.abs.of_nonneg_of_le (fun i => le_max_right _ _)
            (fun i => max_le (le_abs_self _) (abs_nonneg _)))
      · intro T x hx
        exact (Finset.norm_prod_le _ _).trans
          (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
            (fun i _ => (hub i x hx).trans (le_max_left _ _)))
  apply hd.congr
  intro x hx
  have hnorm : Summable (fun i => ‖f i x - 1‖) := by
    obtain ⟨u, hu, hub⟩ := hM {x}
      (fun y hy => by simp only [Set.mem_singleton_iff] at hy; rw [hy]; exact hx)
      isCompact_singleton
    exact hu.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hub i x (mem_singleton x))
  have hh := tprod_one_add (summable_finsetProd_of_summable_norm hnorm)
  simpa using hh

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

variable (R : PrincipalMellin.ActualRecipe S η)
  (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
  (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
  (plus minus : Frequency R → ℂ → ℂ)

def numerator (u : Frequency R) (ξ w z : ℂ) : ℂ :=
  R.L (6 * z) * plus u w *
    AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z

def euler (u : Frequency R) (ξ w z : ℂ) : ℂ :=
  numerator R C U plus u ξ w z / minus u ξ

theorem actual_quotient_corridors
    (hC : R.probe.correction = C.correction)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val)
    (hplus : ∀ u : Frequency R, u ≠ principalFrequency R →
      DifferentiableOn ℂ (plus u) {s : ℂ | 0 < s.re})
    (hminus : ∀ u : Frequency R, u ≠ principalFrequency R →
      DifferentiableOn ℂ (minus u) {s : ℂ | 0 < s.re})
    (hplusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      plus u s = AllRowEuler.InitialSeparation.plusL R.σ (U u) s)
    (hminusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      minus u s = AllRowEuler.InitialSeparation.minusL R.σ R.target (U u) s) :
    ∃ Ω Ωleft : Set (ℂ × ℂ × ℂ),
      (∀ (u : Frequency R) (ξ w z : ℂ), u ≠ principalFrequency R →
        ξ.re = 4 → w.re = 4 → z.re = 2 →
        separatedSeries R u ξ w z = euler R C U plus minus u ξ w z) ∧
      IsOpen Ω ∧
      (∀ ξ w z : ℂ, ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
        w ∈ comparisonClosedStrip (3 / 1000) 4 →
        z ∈ comparisonClosedStrip (2 / 5) 2 → (ξ, w, z) ∈ Ω) ∧
      (∀ u : Frequency R, u ≠ principalFrequency R →
        DifferentiableOn ℂ
          (fun p : ℂ × ℂ × ℂ => euler R C U plus minus u p.1 p.2.1 p.2.2) Ω) ∧
      IsOpen Ωleft ∧
      (∀ ξ w z : ℂ, ξ ∈ comparisonClosedStrip (499 / 500) comparisonSigma₁ →
        w.re = 3 / 1000 → z.re = 2 / 5 → (ξ, w, z) ∈ Ωleft) ∧
      (∀ u : Frequency R, u ≠ principalFrequency R →
        DifferentiableOn ℂ
          (fun p : ℂ × ℂ × ℂ => numerator R C U plus u p.1 p.2.1 p.2.2) Ωleft) := by
  have hcorr (u : Frequency R) : DifferentiableOn ℂ
      (fun p : CorrectionFactors.Coordinates =>
        AllRowEuler.InitialSeparation.correctionProduct C (U u) p.1 p.2.1 p.2.2)
      CorrectionFactors.Omega := by
    exact product_differentiableOn _
      (Corridor.raw_local_correction_differentiableOn C (U u))
      (Corridor.raw_correction_compact_majorant C (U u))
  have hnum (u : Frequency R) (hu : u ≠ principalFrequency R) :
      DifferentiableOn ℂ
        (fun p : CorrectionFactors.Coordinates => numerator R C U plus u p.1 p.2.1 p.2.2)
        CorrectionFactors.omegaFirst := by
    exact (Corridor.scalar_numerator_differentiableOn R (plus u) (hplus u hu)).mul
      ((hcorr u).mono Set.subset_union_left)
  let Ω : Set CorrectionFactors.Coordinates :=
    CorrectionFactors.omegaFirst ∩ {p | 1 < p.1.re}
  have hrightOpen : IsOpen {p : CorrectionFactors.Coordinates | 1 < p.1.re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)
  have hfirstOpen : IsOpen CorrectionFactors.omegaFirst := by
    exact (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
      ((isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_fst.comp continuous_snd))).inter
        (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_snd.comp continuous_snd))))
  refine ⟨Ω, CorrectionFactors.omegaFirst, ?_,
    hfirstOpen.inter hrightOpen, ?_, ?_, hfirstOpen, ?_, ?_⟩
  · intro u ξ w z _ hξ hw hz
    exact Corridor.initial_continuation_agreement R C U plus minus
      hC hU hplusSeries hminusSeries u ξ w z hξ hw hz
  · intro ξ w z hξ hw hz
    change _ ∧ _
    have hξlo := hξ.1
    have hwlo := hw.1
    have hzlo := hz.1
    change comparisonSigma₁ ≤ ξ.re at hξlo
    change (3 / 1000 : ℝ) ≤ w.re at hwlo
    change (2 / 5 : ℝ) ≤ z.re at hzlo
    norm_num [comparisonSigma₁, comparisonDelta] at hξlo
    constructor
    · change _ ∧ _ ∧ _
      constructor
      · norm_num
        linarith
      constructor <;> norm_num <;> linarith
    · change 1 < ξ.re
      linarith
  · intro u hu
    change DifferentiableOn ℂ
      (fun p : CorrectionFactors.Coordinates => euler R C U plus minus u p.1 p.2.1 p.2.2) Ω
    have hden : DifferentiableOn ℂ
        (fun p : CorrectionFactors.Coordinates => minus u p.1) Ω := by
      apply (hminus u hu).comp differentiable_id.fst.differentiableOn
      intro p hp
      change 0 < p.1.re
      have hp1 : 1 < p.1.re := hp.2
      linarith
    have hnz : ∀ p ∈ Ω, minus u p.1 ≠ 0 := by
      intro p hp
      rw [hminusSeries u p.1 hp.2]
      exact AllRowEuler.InitialSeparation.raw_minusL_ne_zero (U u) p.1 hp.2
    change DifferentiableOn ℂ
      (fun p : CorrectionFactors.Coordinates =>
        numerator R C U plus u p.1 p.2.1 p.2.2 * (minus u p.1)⁻¹) Ω
    exact ((hnum u hu).mono (show Ω ⊆ CorrectionFactors.omegaFirst from Set.inter_subset_left)).mul
      (hden.inv hnz)
  · intro ξ w z hξ hw hz
    change _ ∧ _ ∧ _
    have hξlo : (499 / 500 : ℝ) ≤ ξ.re := hξ.1
    constructor
    · norm_num
      linarith
    constructor <;> norm_num <;> linarith
  · exact hnum

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation

end

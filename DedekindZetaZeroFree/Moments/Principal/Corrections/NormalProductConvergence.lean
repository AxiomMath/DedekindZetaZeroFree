module

public import DedekindZetaZeroFree.Moments.Principal.Corrections.GoodPrimeEstimates
public import DedekindZetaZeroFree.Moments.Principal.Corrections.BadPrimeEstimates
public import DedekindZetaZeroFree.Arithmetic.Ideals.PrimeNormSummability

@[expose] public section

open scoped NumberField Classical

noncomputable section
namespace DedekindZetaZeroFree.CorrectionFactors
set_option autoImplicit false

open LocalFiniteSums

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem frequency_good_cofinite
    (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C) :
    ∀ᶠ p : ExteriorPrime A in Filter.cofinite, (U.j p).val = 0 := by
  apply Filter.eventually_cofinite.mpr
  have hinj : Function.Injective (fun p : ExteriorPrime A => p.val.asIdeal) :=
    IsDedekindDomain.HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective
  simpa [Frequency.j, idealPrimeExponent, Multiset.count_eq_zero] using
    (UniqueFactorizationMonoid.normalizedFactors U.ideal.val).finite_toSet.preimage
      hinj.injOn

private theorem frequency_good_unit
    (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C)
    (p : ExteriorPrime A) (hp : (U.j p).val = 0) :
    IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) := by
  have hs := U.unitPart_spec p
  rw [hs.1, hp, pow_zero, one_mul]
  exact hs.2

private theorem exterior_not_mem (p : ExteriorPrime A) : p.val ∉ A.Sf := by
  intro hp
  have he := (A.exterior_iff ⟨p.val.asIdeal, p.val.ne_bot⟩).mp p.property p.val hp
  simp only [sup_idem] at he
  exact p.val.isPrime.ne_top he

private theorem summable_correction_majorant (M : ℝ) :
    Summable (fun p : ExteriorPrime A =>
      M * (Q p) ^ (-(1 + 1 / 4000 : ℝ))) := by
  let i : ExteriorPrime A → {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // p ∉ A.Sf} :=
    fun p => ⟨p.val, exterior_not_mem p⟩
  have hi : Function.Injective i := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun r : {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // p ∉ A.Sf} => r.val) h
  have hs := (summable_exterior_prime_norm_rpow F A.Sf (1 + 1 / 4000) (by norm_num)).comp_injective hi
  simpa [Function.comp_def, i, Q, SArithmeticData.exteriorNorm, idealNorm, primeIdeal]
    using hs.mul_left M

theorem hasProdUniformlyOn_localFactor
    (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C)
    (K : Set Coordinates) (hK : IsCompact K) (hKO : K ⊆ Omega) :
    HasProdUniformlyOn
      (fun (p : ExteriorPrime A) (x : Coordinates) =>
        localFactor C U p x.1 x.2.1 x.2.2)
      (fun x : Coordinates =>
        ∏' p : ExteriorPrime A, localFactor C U p x.1 x.2.1 x.2.2) K := by
  obtain ⟨M, hM, hbound⟩ := good_correction_uniform_bound
  have hb : ∀ᶠ p : ExteriorPrime A in Filter.cofinite, ∀ x ∈ K,
      ‖localFactor C U p x.1 x.2.1 x.2.2 - 1‖ ≤
        M * (Q p) ^ (-(1 + 1 / 4000 : ℝ)) := by
    filter_upwards [frequency_good_cofinite C U] with p hp
    intro x hx
    simpa [localFactor, hp] using
      hbound F A σ η hS C p U.u (frequency_good_unit C U p hp) x (hKO hx)
  have hcts : ∀ p : ExteriorPrime A,
      ContinuousOn (fun x : Coordinates => localFactor C U p x.1 x.2.1 x.2.2 - 1) K := by
    intro p
    have hc : ContinuousOn (fun x : Coordinates => localFactor C U p x.1 x.2.1 x.2.2) Omega := by
      by_cases hp : (U.j p).val = 0
      · simpa [localFactor, hp] using
          (good_correction_holomorphic C p U.u (frequency_good_unit C U p hp)).continuousOn
      · simpa [localFactor, hp] using
          (bad_factor_holomorphic C p (U.j p) hp (U.theta p)).continuousOn
    exact (hc.mono hKO).sub continuousOn_const
  simpa only [add_sub_cancel] using
    (summable_correction_majorant (A := A) M).hasProdUniformlyOn_one_add hK hb hcts

theorem multipliable_localFactor
    (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C)
    (x : Coordinates) (hx : x ∈ Omega) :
    Multipliable (fun p : ExteriorPrime A =>
      localFactor C U p x.1 x.2.1 x.2.2) := by
  exact ((hasProdUniformlyOn_localFactor C U {x}
    isCompact_singleton (Set.singleton_subset_iff.mpr hx)).hasProd (Set.mem_singleton x)).multipliable

theorem hasProdLocallyUniformlyOn_localFactor
    (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C) :
    HasProdLocallyUniformlyOn
      (fun (p : ExteriorPrime A) (x : Coordinates) =>
        localFactor C U p x.1 x.2.1 x.2.2)
      (fun x : Coordinates =>
        ∏' p : ExteriorPrime A, localFactor C U p x.1 x.2.1 x.2.2) Omega := by
  exact hasProdLocallyUniformlyOn_of_forall_compact isOpen_Omega
    (fun K hKO hK => hasProdUniformlyOn_localFactor C U K hK hKO)

end DedekindZetaZeroFree.CorrectionFactors

end

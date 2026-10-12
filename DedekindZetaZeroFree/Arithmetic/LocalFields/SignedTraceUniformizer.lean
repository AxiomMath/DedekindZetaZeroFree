module

public import DedekindZetaZeroFree.Theta.Unfolding.FactorizationAndMellinNormalizationData

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.TraceHaarTransport
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

 theorem divided_negative_trace (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) (t : 𝓞 F) :
    MomentSources.Characters.psi R p (Ideal.Quotient.mk p.val.asIdeal t) =
      (ResidueTrace.localTraceCharacter p.val
        (algebraMap F (p.val.adicCompletion F)
          (-((t : F) / (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)))) : ℂ) := by
  let I := ThetaBranch.primeIdeal R.A p
  let a := R.probe.allowed.generator I
  obtain ⟨b, hb⟩ := R.probe.allowed.generates I
  have hh := R.A.residueTraceCharacter_prime_local R.traceBad R.probe.allowed.B I p.val rfl
    b hb.1 a hb.2 (R.probe.allowed.allowed I) (algebraMap (𝓞 F) R.A.R t)
  rw [R.A.residueTraceCharacter_apply] at hh
  rw [MomentSources.Characters.psi_apply R, PrincipalMellinSource.additiveCharacter_eq_fieldTrace]
  apply congrArg (fun z : Circle => (z : ℂ))
  have ht : ((algebraMap (𝓞 F) R.A.R t) : F) = (t : F) :=
    IsScalarTower.algebraMap_apply (𝓞 F) R.A.R F t
  rw [ht, ← hb.2] at hh
  exact hh

 theorem generator_norm (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) :
    ‖algebraMap F (p.val.adicCompletion F)
      (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)‖ =
      (R.A.exteriorNorm (ThetaBranch.primeIdeal R.A p))⁻¹ := by
  obtain ⟨r, hr, he⟩ := R.probe.allowed.generates (ThetaBranch.primeIdeal R.A p)
  have hv := SIntegerLocalization.generator_completion_valuation R.A.Sf
    (ThetaBranch.primeIdeal R.A p).val (ThetaBranch.primeIdeal R.A p).property.1
    r hr.1 hr.2 _ he p.val p.property
  have hi : idealPrimeExponent p.val.asIdeal (ThetaBranch.primeIdeal R.A p).val = 1 := by
    simp [ThetaBranch.primeIdeal, idealPrimeExponent,
      UniqueFactorizationMonoid.normalizedFactors_irreducible p.val.irreducible]
  rw [hi] at hv
  rw [FinitePlace.norm_def, hv]
  simp [SArithmeticData.exteriorNorm, ThetaBranch.primeIdeal,
    WithZeroMulInt.toNNReal_neg_apply, idealNorm]

 def signedUniformizer (R : PrincipalMellin.ActualRecipe S η) :
    MomentSources.SignedUniformizerTransport R where
  uniformizer p := -(Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom
    (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p)))
  uniformizer_norm p := by simpa using generator_norm R p
  witnessPsi := MomentSources.Characters.psi R
  witnessPsi_trace p t := by
    rw [divided_negative_trace R p t]
    congr 1
    have he := IsScalarTower.algebraMap_apply (𝓞 F) F (p.val.adicCompletion F) t
    simp only [map_neg, map_div₀, div_neg, Units.val_neg, Units.coe_map]
    rw [← he]
    rfl
  delta _ := 1
  delta_actual p t ht := by
    have hm : t - 1 ∈ p.val.asIdeal := Ideal.Quotient.eq_zero_iff_mem.mp (by
      rw [map_sub, map_one, ht]; simp)
    have hz : algebraMap F (p.val.adicCompletion F)
        (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F) ≠ 0 :=
      (map_ne_zero (algebraMap F (p.val.adicCompletion F))).mpr
        (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p)).ne_zero
    change ‖algebraMap (𝓞 F) (p.val.adicCompletion F) t +
      -(algebraMap F (p.val.adicCompletion F)
        (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)) /
      algebraMap F (p.val.adicCompletion F)
        (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)‖ < 1
    rw [neg_div, div_self hz, ← sub_eq_add_neg, ← map_one (algebraMap (𝓞 F) _), ← map_sub]
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (p.val.adicCompletion F),
      Valued.toNormedField.norm_lt_one_iff]
    change Valued.v (((t - 1 : 𝓞 F) : F) : p.val.adicCompletion F) < 1
    rw [HeightOneSpectrum.adicCompletion.valued_coe]
    exact (p.val.valuation_lt_one_iff_mem (K := F) (t - 1)).mpr hm
  signed_shift _ := by ext x; simp [AddChar.mulShift_apply]
end DedekindZetaZeroFree.TraceHaarTransport

end

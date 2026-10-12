module

public import ClassFieldTheory.All

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.PrimitiveRay

variable {F : Type} [Field F] [NumberField F]

 theorem six_ne_zero : (6 : F) ≠ 0 := by norm_num

abbrev sexticExtension (u : Fˣ) : IntermediateField F (SeparableClosure F) :=
  KummerTheory.chosenSimpleKummerExtension F 6 six_ne_zero u

instance sexticExtension_finiteDimensional (u : Fˣ) :
    FiniteDimensional F (sexticExtension u) :=
  KummerTheory.chosenSimpleKummerExtension_finiteDimensional F 6 six_ne_zero u

instance sexticExtension_numberField (u : Fˣ) : NumberField (sexticExtension u) :=
  NumberField.of_module_finite F (sexticExtension u)

theorem sexticExtension_isAbelianGalois (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (u : Fˣ) : IsAbelianGalois F (sexticExtension u) :=
  KummerTheory.chosenSimpleKummerExtension_isAbelianGalois F 6 six_ne_zero
    ⟨ζ ^ 2, (mem_primitiveRoots (by decide)).2
      (hζ.pow (by decide) (by decide : 12 = 2 * 6))⟩ u

def sexticRootCharacter (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (σ : F →+* ℂ) (u : Fˣ) :
    (sexticExtension u ≃ₐ[F] sexticExtension u) →* ℂˣ :=
  let hμ : (primitiveRoots 6 F).Nonempty :=
    ⟨ζ ^ 2, (mem_primitiveRoots (by decide)).2
      (hζ.pow (by decide) (by decide : 12 = 2 * 6))⟩
  let descent : rootsOfUnity 6 (sexticExtension u) ≃* rootsOfUnity 6 F :=
    (rootsOfUnityEquivOfPrimitiveRoots (algebraMap F (sexticExtension u)).injective hμ).symm
  let transport : rootsOfUnity 6 (sexticExtension u) →* ℂˣ :=
    (Units.map σ.toMonoidHom).comp ((rootsOfUnity 6 F).subtype.comp descent.toMonoidHom)
  transport.comp ((KummerTheory.nthRootsSubgroupEquivRootsOfUnity
    (sexticExtension u) 6).toMonoidHom.comp
      (KummerTheory.chosenSimpleKummerRootCharacter F 6 six_ne_zero hμ u))

def sexticArtinCharacter (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (σ : F →+* ℂ) (u : Fˣ) : IdeleClassGroup F →ₜ* ℂˣ :=
  letI := sexticExtension_isAbelianGalois ζ hζ u
  let κ : (sexticExtension u ≃ₐ[F] sexticExtension u) →ₜ* ℂˣ :=
    { sexticRootCharacter ζ hζ σ u with
      continuous_toFun := continuous_of_discreteTopology }
  κ.comp (GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMonoidHom
    F (sexticExtension u))

theorem sexticArtinCharacter_apply (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (σ : F →+* ℂ) (u : Fˣ) (c : IdeleClassGroup F) :
    sexticArtinCharacter ζ hζ σ u c =
      sexticRootCharacter ζ hζ σ u
        (letI := sexticExtension_isAbelianGalois ζ hζ u
         GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMonoidHom
           F (sexticExtension u) c) := rfl

theorem sexticArtinCharacter_pow_six (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (σ : F →+* ℂ) (u : Fˣ) (c : IdeleClassGroup F) :
    sexticArtinCharacter ζ hζ σ u c ^ 6 = 1 := by
  rw [sexticArtinCharacter_apply]
  unfold sexticRootCharacter
  simp only [MonoidHom.comp_apply]
  rw [← map_pow]
  rw [show ((rootsOfUnity 6 F).subtype _) ^ 6 = 1 from
    (mem_rootsOfUnity _ _).mp (Subtype.property _), map_one]

theorem sexticArtinCharacter_prime_eq_inverse_arithmetic
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (σ : F →+* ℂ)
    (u : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    sexticArtinCharacter ζ hζ σ u
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup F) (IdeleGroup.finitePrimeIdele v)) =
      (sexticRootCharacter ζ hζ σ u
        (letI := sexticExtension_isAbelianGalois ζ hζ u
         GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
           (K := F) (L := sexticExtension u) v))⁻¹ := by
  letI := sexticExtension_isAbelianGalois ζ hζ u
  rw [sexticArtinCharacter_apply]
  change sexticRootCharacter ζ hζ σ u
    (GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom F (sexticExtension u)
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup F) (IdeleGroup.finitePrimeIdele v))) = _
  have he := DFunLike.congr_fun
    (GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin
      (K := F) (L := sexticExtension u)) (IdeleGroup.finitePrimeIdele v)
  change GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom F (sexticExtension u) _ = _ at he
  rw [he]
  simp only [GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin,
    GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_apply, map_inv, inv_inv]

private theorem valuation_six (v : HeightOneSpectrum (𝓞 F))
    (hSix : (Ideal.absNorm v.asIdeal).Coprime 6) : v.valuation F (6 : F) = 1 := by
  change v.valuation F (algebraMap (𝓞 F) F (6 : 𝓞 F)) = 1
  apply (v.valuation_eq_one_iff_notMem (K := F)).mpr
  intro h6
  have he := Nat.gcd_eq_gcd_ab (Ideal.absNorm v.asIdeal) 6
  rw [hSix.gcd_eq_one] at he
  have he' : (1 : 𝓞 F) = (Ideal.absNorm v.asIdeal : 𝓞 F) *
      (Nat.gcdA (Ideal.absNorm v.asIdeal) 6 : 𝓞 F) +
      6 * (Nat.gcdB (Ideal.absNorm v.asIdeal) 6 : 𝓞 F) := by exact_mod_cast he
  apply v.isPrime.ne_top
  apply (Ideal.eq_top_iff_one _).mpr
  rw [he']
  exact v.asIdeal.add_mem
    (v.asIdeal.mul_mem_right _ (Ideal.absNorm_mem v.asIdeal))
    (v.asIdeal.mul_mem_right _ h6)

private theorem frob_congruence {E : Type} [Field E] [NumberField E]
    [Algebra F E] [IsAbelianGalois F E] (v : HeightOneSpectrum (𝓞 F))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv F v) E)
    (g : E ≃ₐ[F] E)
    (hg : IsArithFrobAt (𝓞 F) g (finitePlaceExtensionCentre (K := F) (L := E) v w).asIdeal)
    (b : E) (hb : w.val b = 1) (hgb : w.val (g b) = 1) :
    w.val (g b - b ^ Ideal.absNorm v.asIdeal) < 1 := by
  let W := finitePlaceExtensionCentre (K := F) (L := E) v w
  have hbW : W.valuation E b ≤ 1 := by
    have hm : b ∈ finitePlaceExtensionValuationSubring (K := F) (L := E) v w := by
      change w.val b ≤ 1
      exact hb.le
    rw [finitePlaceExtensionValuationSubring_eq_localization,
      W.valuationSubringAtPrime_eq_valuationSubring] at hm
    exact hm
  obtain ⟨n, d, hnd⟩ := W.exists_primeCompl_mul_eq_of_integer b hbW
  have hd : w.val (algebraMap (𝓞 E) E d.val) = 1 := by
    have hn : d.val ∉ W.asIdeal := d.property
    have hle := ringOfIntegers_mem_finitePlaceExtensionValuationSubring (K := F) (L := E) v w d.val
    change w.val (d.val : E) ≤ 1 at hle
    have hnot : ¬ w.val (d.val : E) < 1 := by
      rw [← mem_finitePlaceExtensionCentreIdeal_iff]
      exact hn
    exact le_antisymm hle (le_of_not_gt hnot)
  have hcon (a : 𝓞 E) : w.val (g (a : E) - (a : E)^Ideal.absNorm v.asIdeal) < 1 := by
    have h := hg a
    have hover := finitePlaceExtensionCentre_liesOver (K := F) (L := E) v w
    rw [← hover.over] at h
    change _ - a ^ Ideal.absNorm v.asIdeal ∈ W.asIdeal at h
    have h' := (mem_finitePlaceExtensionCentreIdeal_iff (K := F) (L := E) v w ((NumberField.RingOfIntegers.mapAlgEquiv g) a - a ^ Ideal.absNorm v.asIdeal)).mp h
    exact h'
  have he : (g b - b ^ Ideal.absNorm v.asIdeal) * (d.val : E)^Ideal.absNorm v.asIdeal =
      (g (n : E) - (n : E)^Ideal.absNorm v.asIdeal) +
        g b * ((d.val : E)^Ideal.absNorm v.asIdeal - g (d.val : E)) := by
    have hgnd := congrArg g hnd
    simp only [map_mul] at hgnd
    have hpow := congrArg (fun x : E => x ^ Ideal.absNorm v.asIdeal) hnd
    rw [mul_pow] at hpow
    linear_combination hgnd - hpow
  have hna := LubinTate.Valuations.strong_triangle_of_nonarchimedean w.val (finitePlaceExtension_nonarchimedean (K := F) (L := E) v w)
  have hlt : w.val ((g b - b ^ Ideal.absNorm v.asIdeal) * (d.val : E)^Ideal.absNorm v.asIdeal) < 1 := by
    rw [he]
    apply lt_of_le_of_lt (hna _ _) (max_lt (hcon n) ?_)
    rw [map_mul, hgb, one_mul, AbsoluteValue.map_sub]
    exact hcon d.val
  simpa only [map_mul, map_pow, hd, one_pow, mul_one] using hlt

theorem sexticArtinCharacter_prime (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (σ : F →+* ℂ) (u : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (hSix : (Ideal.absNorm v.asIdeal).Coprime 6)
    (hu : v.valuation F (u : F) = 1) :
    ∃ j : Fin 6,
      v.valuation F ((u : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) -
        (ζ ^ 2) ^ j.val) < 1 ∧
      (sexticArtinCharacter ζ hζ σ u
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
          (IdeleGroup.finitePrimeIdele v)) : ℂ) = (σ ((ζ ^ 2) ^ j.val))⁻¹ := by
  have hn := valuation_six v hSix
  let hμ : (primitiveRoots 6 F).Nonempty := ⟨ζ^2, (mem_primitiveRoots (by decide)).2 (hζ.pow (by decide) (by decide : 12 = 2 * 6))⟩
  letI := sexticExtension_isAbelianGalois ζ hζ u
  let w := chosenFinitePlaceExtension (L := sexticExtension u) v
  let W := finitePlaceExtensionCentre (K := F) (L := sexticExtension u) v w
  let g := GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin (K := F) (L := sexticExtension u) v
  let beta := KummerTheory.chosenSimpleKummerRootUnit F 6 six_ne_zero u
  let descent : rootsOfUnity 6 (sexticExtension u) ≃* rootsOfUnity 6 F := (rootsOfUnityEquivOfPrimitiveRoots (algebraMap F (sexticExtension u)).injective hμ).symm
  let r := descent (KummerTheory.nthRootsSubgroupEquivRootsOfUnity (sexticExtension u) 6 (KummerTheory.chosenSimpleKummerRootCharacter F 6 six_ne_zero hμ u g))
  have hr : Units.map (algebraMap F (sexticExtension u)).toMonoidHom r.val = KummerTheory.rootQuotient (K := F) (L := sexticExtension u) beta g := by
    have he := (rootsOfUnityEquivOfPrimitiveRoots (algebraMap F (sexticExtension u)).injective hμ).apply_symm_apply (KummerTheory.nthRootsSubgroupEquivRootsOfUnity (sexticExtension u) 6 (KummerTheory.chosenSimpleKummerRootCharacter F 6 six_ne_zero hμ u g))
    have he' := congrArg (fun z : rootsOfUnity 6 (sexticExtension u) => z.val) he
    change Units.map (algebraMap F (sexticExtension u)).toMonoidHom r.val = (KummerTheory.chosenSimpleKummerRootCharacter F 6 six_ne_zero hμ u g).val at he'
    rw [KummerTheory.chosenSimpleKummerRootCharacter_apply F 6 six_ne_zero hμ u g] at he'
    exact he'
  have hrpow : (r.val : F)^6 = 1 := by
    have hh := (mem_rootsOfUnity _ _).mp r.property
    exact congrArg Units.val hh
  obtain ⟨j, hj, hjr⟩ := (hζ.pow (by decide) (by decide : 12 = 2 * 6)).eq_pow_of_pow_eq_one hrpow
  refine ⟨⟨j,hj⟩, ?_, ?_⟩
  · have hunram := KummerTheory.chosenSimpleKummerExtension_isUnramifiedAt_at_all_finitePlacesAbove_of_valuation_eq_one (K := F) 6 six_ne_zero hμ u v hu hn W (finitePlaceBelow_finitePlaceExtensionCentre v w)
    have hg : IsArithFrobAt (𝓞 F) g W.asIdeal := by
      dsimp only [g]
      rw [ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt (K := F) (L := sexticExtension u) v W (finitePlaceExtensionCentre_liesOver v w) hunram]
      exact IsArithFrobAt.arithFrobAt (𝓞 F) (sexticExtension u ≃ₐ[F] sexticExtension u) W.asIdeal
    have hbeta : (beta : sexticExtension u)^6 = algebraMap F (sexticExtension u) (u : F) := congrArg Units.val (KummerTheory.chosenSimpleKummerRootUnit_pow F 6 six_ne_zero u)
    have huabs : HeightOneSpectrum.adicAbv F v (u : F) = 1 := by
      simp only [HeightOneSpectrum.adicAbv_def, hu]
      simp
    have hbabs : w.val (beta : sexticExtension u) = 1 := by
      apply (pow_eq_one_iff_of_nonneg (w.val.nonneg _) (by decide : (6 : ℕ) ≠ 0)).mp
      rw [← map_pow, hbeta, w.property, huabs]
    have hgbabs : w.val (g (beta : sexticExtension u)) = 1 := by
      apply (pow_eq_one_iff_of_nonneg (w.val.nonneg _) (by decide : (6 : ℕ) ≠ 0)).mp
      rw [← map_pow, ← map_pow, hbeta, AlgEquiv.commutes, w.property, huabs]
    have hc := frob_congruence v w g hg (beta : sexticExtension u) hbabs hgbabs
    have hq : Ideal.absNorm v.asIdeal = 6 * ((Ideal.absNorm v.asIdeal - 1) / 6) + 1 := by
      have hd := AlgebraicNumberTheory.PowerResidueSymbols.dvd_absNorm_sub_one_of_primitiveRoots F v 6 hμ hSix
      have he := Nat.mul_div_cancel' hd
      have hnq := HeightOneSpectrum.one_lt_absNorm v
      change 6 * ((Ideal.absNorm v.asIdeal - 1) / 6) = Ideal.absNorm v.asIdeal - 1 at he
      omega
    have hroot : g (beta : sexticExtension u) = algebraMap F (sexticExtension u) (r.val : F) * (beta : sexticExtension u) := by
      have he := congrArg Units.val hr
      change algebraMap F (sexticExtension u) (r.val : F) = g (beta : sexticExtension u) / (beta : sexticExtension u) at he
      exact (eq_div_iff (Units.ne_zero beta)).mp he |>.symm
    have he : g (beta : sexticExtension u) - (beta : sexticExtension u)^Ideal.absNorm v.asIdeal =
        algebraMap F (sexticExtension u) ((r.val : F) - (u : F)^((Ideal.absNorm v.asIdeal - 1)/6)) * (beta : sexticExtension u) := by
      rw [hroot]
      conv_lhs => rhs; arg 2; rw [hq]
      rw [pow_add, pow_one, pow_mul, hbeta, map_sub, map_pow]
      ring
    rw [he, map_mul, hbabs, mul_one, w.property, AbsoluteValue.map_sub, ← hjr] at hc
    rw [HeightOneSpectrum.adicAbv_def] at hc
    exact (WithZeroMulInt.toNNReal_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v)).mp (by exact_mod_cast hc)
  · rw [sexticArtinCharacter_prime_eq_inverse_arithmetic]
    have hval : (sexticRootCharacter ζ hζ σ u g : ℂ) = σ (r.val : F) := rfl
    rw [Units.val_inv_eq_inv_val, hval, hjr]

theorem sexticArtinCharacter_unramified (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (σ : F →+* ℂ) (u : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (hSix : (Ideal.absNorm v.asIdeal).Coprime 6)
    (hu : v.valuation F (u : F) = 1)
    (t : (v.adicCompletion F)ˣ)
    (ht : t ∈ (v.adicCompletionIntegers F).units) :
    sexticArtinCharacter ζ hζ σ u (IdeleGroup.finitePlaceIdeleClass v t) = 1 := by
  let hμ : (primitiveRoots 6 F).Nonempty :=
    ⟨ζ ^ 2, (mem_primitiveRoots (by decide)).2
      (hζ.pow (by decide) (by decide : 12 = 2 * 6))⟩
  letI := sexticExtension_isAbelianGalois ζ hζ u
  have hunram := KummerTheory.chosenSimpleKummerExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
    (K := F) 6 six_ne_zero hμ u v hu (valuation_six v hSix)
  have hnorm := adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
    (K := F) (L := sexticExtension u) v hunram ht
  have hlocal : GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom
      (K := F) (L := sexticExtension u) v t = 1 := by
    rw [← GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_ker] at hnorm
    exact MonoidHom.mem_ker.mp hnorm
  rw [sexticArtinCharacter_apply]
  change sexticRootCharacter ζ hζ σ u
    (GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom F (sexticExtension u)
      (IdeleGroup.finitePlaceIdeleClass v t)) = 1
  rw [GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom_finitePlaceIdeleClass_eq_one_of_localArtin_eq_one
    (K := F) (L := sexticExtension u) v t hlocal, map_one]

end DedekindZetaZeroFree.PrimitiveRay

end

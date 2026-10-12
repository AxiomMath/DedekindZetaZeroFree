module

public import ClassFieldTheory.KummerTheory.Concrete.SimpleExtensionLocalBehavior
public import ClassFieldTheory.GlobalClassFieldTheory.Cohomology.CofinitelySplitFiniteExtension
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceAdicLocalField

@[expose] public section

section

open scoped NumberField
open IsDedekindDomain

namespace DedekindZetaZeroFree.Detector.FrequencyLocalPower

theorem global_power_of_cofinite_local_power
    (F : Type) [Field F] [NumberField F] (n : ℕ+)
    (hn : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty) (b : Fˣ)
    (hbad : {v : HeightOneSpectrum (𝓞 F) |
      Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b ∉
        (powMonoidHom (n : ℕ) :
          (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range}.Finite) :
    b ∈ (powMonoidHom (n : ℕ) : Fˣ →* Fˣ).range := by
  let E := KummerTheory.chosenSimpleKummerExtension F n hn b
  letI : FiniteDimensional F E :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional F n hn b
  letI : IsAbelianGalois F E :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois F n hn hmu b
  letI : NumberField E := NumberField.of_module_finite F E
  have hfin : {v : HeightOneSpectrum (𝓞 F) |
      ¬ FinitePlaceSplitsCompletelyInExtension (K := F) (E := E) v}.Finite := by
    apply hbad.subset
    intro v hv
    by_contra hpower
    have hp : Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b ∈
        (powMonoidHom (n : ℕ) : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range :=
      Classical.not_not.mp hpower
    exact hv ((finitePlaceSplitsCompletely_iff_inExtension (K := F) (E := E) v).mp
      (KummerTheory.chosenSimpleKummerExtension_finitePlaceSplitsCompletely_of_mem_nthPowerSubgroup
        n hn hmu b v hp))
  have hdim : Module.finrank F E = 1 :=
    GlobalClassFieldTheory.Cohomology.finrank_eq_one_of_finite_nonSplittingPlaces F E hfin
  have hsurj : Function.Surjective (algebraMap F E) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdim).2
  let β : Eˣ := KummerTheory.chosenSimpleKummerRootUnit F n hn b
  obtain ⟨a, ha⟩ := hsurj (β : E)
  have ha0 : a ≠ 0 := by
    intro h
    exact β.ne_zero (by simpa only [h, map_zero] using ha.symm)
  let aunit : Fˣ := Units.mk0 a ha0
  have hpow : aunit ^ (n : ℕ) = b := by
    apply Units.ext
    apply (FaithfulSMul.algebraMap_injective F E)
    have hr := congrArg (fun z : Eˣ => (z : E))
      (KummerTheory.chosenSimpleKummerRootUnit_pow F n hn b)
    change (algebraMap F E) (a ^ (n : ℕ)) = (algebraMap F E) (b : F)
    rw [map_pow, ha]
    exact hr
  exact ⟨aunit, hpow⟩

end DedekindZetaZeroFree.Detector.FrequencyLocalPower

end

section

open scoped ValuativeRel

namespace DedekindZetaZeroFree.Detector.FrequencyTamePower

open KummerTheory LocalFieldTheory LocalClassFieldTheory.Kummer
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem local_power_of_tame_symbol_one (n : ℕ+)
    (hn : ValuativeRel.valuation K ((n : ℕ) : K) = 1)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (u : 𝒪[K]ˣ)
    (hu : localTamePowerResidueSymbol K n hn hmu u = 1) :
    integerUnitsToFieldUnits K u ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  apply (localHilbertSymbol_left_kernel K n
    (natCast_ne_zero_of_valuation_eq_one K n hn) hmu _).mp
  intro b
  rw [localHilbertSymbol_tame_formula K n hn hmu, hu, one_zpow]

theorem local_power_of_residue_symbol_one (n : ℕ+)
    (hn : ValuativeRel.valuation K ((n : ℕ) : K) = 1)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (u : 𝒪[K]ˣ)
    (hu : letI : Fintype 𝓀[K] := Fintype.ofFinite _
      AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol
        𝓀[K] n
        (by rw [← Nat.card_eq_fintype_card]
            exact dvd_residueCard_sub_one_of_primitiveRoots K n hn hmu)
        (integerUnitsToResidueUnits K u) = 1) :
    integerUnitsToFieldUnits K u ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  apply local_power_of_tame_symbol_one K n hn hmu u
  apply (localNthRootsReductionEquiv K n hn hmu).injective
  rw [map_one, localNthRootsReductionEquiv_localTamePowerResidueSymbol]
  exact hu

theorem local_power_of_residue_power_one (n : ℕ+)
    (hn : ValuativeRel.valuation K ((n : ℕ) : K) = 1)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (u : 𝒪[K]ˣ)
    (hu : (integerUnitsToResidueUnits K u) ^
      ((Nat.card 𝓀[K] - 1) / (n : ℕ)) = 1) :
    integerUnitsToFieldUnits K u ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  apply local_power_of_residue_symbol_one K n hn hmu u
  letI : Fintype 𝓀[K] := Fintype.ofFinite _
  apply Subtype.ext
  change (integerUnitsToResidueUnits K u) ^
    ((Fintype.card 𝓀[K] - 1) / (n : ℕ)) = 1
  simpa only [Nat.card_eq_fintype_card] using hu

end DedekindZetaZeroFree.Detector.FrequencyTamePower

end

section

open scoped NumberField ValuativeRel NNReal
open IsDedekindDomain NumberField
open GlobalClassFieldTheory.Reciprocity
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField

namespace DedekindZetaZeroFree.Detector.FrequencyCompletionResidue

noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem local_power_of_valuation_residue (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (v : HeightOneSpectrum (𝓞 F)) (b : Fˣ)
    (hb : v.valuation F (b : F) = 1)
    (hn : v.valuation F ((n : ℕ) : F) = 1)
    (hr : v.valuation F ((b : F) ^ ((Ideal.absNorm v.asIdeal - 1) / (n : ℕ)) - 1) < 1) :
    Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b ∈
      (powMonoidHom (n : ℕ) : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range := by
  let a := NumberField.HeightOneSpectrum.adicAbv F v
  let C := a.Completion
  letI : Valued C ℝ≥0 := finitePlaceArtinCompletionValued a (HeightOneSpectrum.isNonarchimedean_adicAbv F v)
  letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let ν : Valuation C ℝ≥0 := Valued.v
  letI : ν.Compatible := Valuation.Compatible.ofValuation ν
  have hnorm (x : F) : ‖algebraMap F C x‖ = a x := by
    exact AbsoluteValue.completionAbsoluteValue_coe a x
  have hbnorm : ‖algebraMap F C (b : F)‖ = 1 := by
    rw [hnorm, HeightOneSpectrum.adicAbv_def, hb]
    simp
  let y := Units.map (algebraMap F C).toMonoidHom b
  let u : 𝒪[C]ˣ := {
    val := ⟨(y : C), by
      rw [finitePlaceCompletion_mem_integers_iff_norm_le_one a (HeightOneSpectrum.isNonarchimedean_adicAbv F v)]
      exact hbnorm.le⟩
    inv := ⟨((y : C)⁻¹), by
      rw [finitePlaceCompletion_mem_integers_iff_norm_le_one a (HeightOneSpectrum.isNonarchimedean_adicAbv F v), norm_inv]
      change ‖algebraMap F C (b : F)‖⁻¹ ≤ 1
      rw [hbnorm, inv_one]⟩
    val_inv := by apply Subtype.ext; exact mul_inv_cancel₀ y.ne_zero
    inv_val := by apply Subtype.ext; exact inv_mul_cancel₀ y.ne_zero }
  have hnC : ValuativeRel.valuation C ((n : ℕ) : C) = 1 := by
    rw [← (ValuativeRel.valuation C).map_one, ← (ValuativeRel.valuation C).veq_iff_eq]
    rw [ν.veq_iff_eq]
    change ‖((n : ℕ) : C)‖₊ = ‖(1 : C)‖₊
    apply NNReal.eq
    simp only [coe_nnnorm, norm_one]
    rw [← map_natCast (algebraMap F C), hnorm, HeightOneSpectrum.adicAbv_def, hn]
    simp
  have hmuC : (primitiveRoots (n : ℕ) C).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hmu
    exact ⟨algebraMap F C ζ, (mem_primitiveRoots n.pos).mpr
      (((mem_primitiveRoots n.pos).mp hζ).map_of_injective (algebraMap F C).injective)⟩
  have hcard : Nat.card 𝓀[C] = Ideal.absNorm v.asIdeal := by
    exact finitePlaceCompletion_residueField_card v
  let k := (Ideal.absNorm v.asIdeal - 1) / (n : ℕ)
  have hu : integerUnitsToResidueUnits C u ^ k = 1 := by
    rw [← map_pow, integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one, mem_principalUnits_iff, pow_one]
    apply (Valuation.mem_maximalIdeal_iff C (ValuativeRel.valuation C)).mpr
    rw [← (ValuativeRel.valuation C).vlt_one_iff, ν.vlt_one_iff]
    change ‖(((u ^ k : 𝒪[C]ˣ) : 𝒪[C]) : C) - 1‖₊ < 1
    change ‖algebraMap F C (b : F) ^ k - 1‖₊ < 1
    rw [← map_pow, ← map_one (algebraMap F C), ← map_sub]
    change ‖algebraMap F C ((b : F) ^ k - 1)‖ < 1
    rw [hnorm, HeightOneSpectrum.adicAbv_def]
    exact (WithZeroMulInt.toNNReal_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v)).mpr hr
  have hp := FrequencyTamePower.local_power_of_residue_power_one C n hnC hmuC u (by simpa [hcard, k] using hu)
  obtain ⟨r, hrp⟩ := hp
  let e := relativeFinitePlaceCompletionAlgEquiv v
  refine ⟨Units.map e.toRingHom.toMonoidHom r, ?_⟩
  apply Units.ext
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val]
  change e (r : C) ^ (n : ℕ) = algebraMap F (v.adicCompletion F) (b : F)
  rw [← map_pow e]
  have h : (r : C) ^ (n : ℕ) = algebraMap F C (b : F) :=
    congrArg (fun z : Cˣ => (z : C)) hrp
  rw [h]
  exact e.commutes (b : F)

end
end DedekindZetaZeroFree.Detector.FrequencyCompletionResidue

end

section

open scoped NumberField
open IsDedekindDomain

namespace DedekindZetaZeroFree.Detector.FrequencyDetection

variable {F : Type} [Field F] [NumberField F]

theorem valuation_unit_cofinite (x : Fˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      v.valuation F (x : F) = 1 := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 F) (x : F)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    intro ha
    apply x.ne_zero
    rw [← hab, ha, map_zero, zero_div]
  have hA : Ideal.span {a} ≠ (0 : Ideal (𝓞 F)) := by
    intro h
    exact ha0 (Ideal.span_singleton_eq_bot.mp h)
  have hB : Ideal.span {b} ≠ (0 : Ideal (𝓞 F)) := by
    intro h
    exact hb0 (Ideal.span_singleton_eq_bot.mp h)
  apply Filter.eventually_cofinite.mpr
  apply ((Ideal.finite_factors hA).union (Ideal.finite_factors hB)).subset
  intro v hv
  simp only [Set.mem_setOf_eq, Set.mem_union] at hv ⊢
  by_contra h
  push Not at h
  apply hv
  rw [← hab, map_div₀]
  have hav : v.intValuation a = 1 := by
    apply HeightOneSpectrum.intValuation_eq_one_iff.mpr
    intro ha
    exact h.1 ((Ideal.dvd_span_singleton).mpr ha)
  have hbv : v.intValuation b = 1 := by
    apply HeightOneSpectrum.intValuation_eq_one_iff.mpr
    intro hb
    exact h.2 ((Ideal.dvd_span_singleton).mpr hb)
  rw [v.valuation_of_algebraMap, v.valuation_of_algebraMap, hav, hbv, div_one]

theorem global_power_of_cofinite_residue (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty) (b : Fˣ)
    (hr : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      v.valuation F ((b : F) ^ ((Ideal.absNorm v.asIdeal - 1) / (n : ℕ)) - 1) < 1) :
    ∃ x : Fˣ, x ^ (n : ℕ) = b := by
  have hn : ((n : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  let nu : Fˣ := Units.mk0 ((n : ℕ) : F) hn
  have hp : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b ∈
        (powMonoidHom (n : ℕ) : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range := by
    filter_upwards [hr, valuation_unit_cofinite b, valuation_unit_cofinite nu] with v hrv hbv hnv
    exact FrequencyCompletionResidue.local_power_of_valuation_residue F n hmu v b hbv hnv hrv
  exact FrequencyLocalPower.global_power_of_cofinite_local_power F n hn hmu b
    (Filter.eventually_cofinite.mp hp)

end DedekindZetaZeroFree.Detector.FrequencyDetection

end

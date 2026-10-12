module

public import ClassFieldTheory.All

@[expose] public section

open scoped NumberField Classical ValuativeRel
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.RepresentationTheory.KPHilbertNormalization.LocalComparison
noncomputable section
set_option autoImplicit false

open Polynomial KummerTheory

private theorem kummer_splits (K : Type) [Field K] (n : ℕ+)
    (hn : (n : K) ≠ 0) (hm : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    IsSplittingField K (chosenSimpleKummerExtension K n hn b)
      (X ^ (n : ℕ) - C (b : K)) := by
  let E := chosenSimpleKummerExtension K n hn b
  let β : E := chosenSimpleKummerRootUnit K n hn b
  letI : FiniteDimensional K E := chosenSimpleKummerExtension_finiteDimensional K n hn b
  have hp : β ^ (n : ℕ) = algebraMap K E (b : K) :=
    congrArg Units.val (chosenSimpleKummerRootUnit_pow K n hn b)
  obtain ⟨ζ, hζ⟩ := hm
  constructor
  · simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot
      (((mem_primitiveRoots n.pos).1 hζ).map_of_injective (algebraMap K E).injective) hp
  · apply top_unique
    have ht : Algebra.adjoin K {β} = ⊤ :=
      (IntermediateField.adjoin_eq_top_iff).mp
        (chosenSimpleKummerExtension_adjoin_root_eq_top K n hn b)
    rw [← ht]
    apply Algebra.adjoin_mono
    intro x hx
    have hx' : x = β := Set.mem_singleton_iff.mp hx
    subst x
    apply Polynomial.mem_rootSet.mpr
    constructor
    · exact Polynomial.X_pow_sub_C_ne_zero n.pos _
    · simpa only [Polynomial.aeval_sub, map_pow, Polynomial.aeval_X,
        Polynomial.aeval_C, sub_eq_zero] using hp

private theorem kummer_equiv (K K' : Type) [Field K] [Field K']
    (e : K ≃+* K') (n : ℕ+) (hn : (n : K) ≠ 0) (hn' : (n : K') ≠ 0)
    (hm : (primitiveRoots (n : ℕ) K).Nonempty)
    (hm' : (primitiveRoots (n : ℕ) K').Nonempty) (b : Kˣ) :
    ∃ eL : chosenSimpleKummerExtension K n hn b ≃+*
        chosenSimpleKummerExtension K' n hn' (Units.mapEquiv e.toMulEquiv b),
      ∀ x : K, eL (algebraMap K _ x) = algebraMap K' _ (e x) := by
  let E := chosenSimpleKummerExtension K n hn b
  let b' : K'ˣ := Units.mapEquiv e.toMulEquiv b
  let E' := chosenSimpleKummerExtension K' n hn' b'
  letI : Algebra K E' := ((algebraMap K' E').comp e.toRingHom).toAlgebra
  letI : IsSplittingField K E (X ^ (n : ℕ) - C (b : K)) := kummer_splits K n hn hm b
  let β' : E' := chosenSimpleKummerRootUnit K' n hn' b'
  have hp' : β' ^ (n : ℕ) = algebraMap K E' (b : K) := by
    exact congrArg Units.val (chosenSimpleKummerRootUnit_pow K' n hn' b')
  have hs : ((X ^ (n : ℕ) - C (b : K)).map (algebraMap K E')).Splits := by
    obtain ⟨ζ, hζ⟩ := hm
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot
      (((mem_primitiveRoots n.pos).1 hζ).map_of_injective (algebraMap K E').injective) hp'
  let f : E →ₐ[K] E' := IsSplittingField.lift E (X ^ (n : ℕ) - C (b : K)) hs
  let β : E := chosenSimpleKummerRootUnit K n hn b
  have hpow : (f β) ^ (n : ℕ) = algebraMap K' E' (b' : K') := by
    rw [← map_pow]
    have hp : β ^ (n : ℕ) = algebraMap K E (b : K) :=
      congrArg Units.val (chosenSimpleKummerRootUnit_pow K n hn b)
    rw [hp, f.commutes]
    rfl
  have hgen : IntermediateField.adjoin K' {f β} = ⊤ :=
    LocalClassFieldTheory.Kummer.adjoin_root_eq_top_of_pow_eq K' n hn' hm' b' (f β) hpow
  let R : IntermediateField K' E' :=
    { __ := f.toRingHom.fieldRange
      algebraMap_mem' := fun x => by
        refine ⟨algebraMap K E (e.symm x), ?_⟩
        change f (algebraMap K E (e.symm x)) = algebraMap K' E' x
        rw [f.commutes]
        change algebraMap K' E' (e (e.symm x)) = algebraMap K' E' x
        rw [e.apply_symm_apply] }
  have htop : R = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hx' : x = f β := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨β, rfl⟩
  have hsurj : Function.Surjective f := by
    intro y
    have hy : y ∈ R := htop ▸ IntermediateField.mem_top
    exact hy
  exact ⟨RingEquiv.ofBijective f.toRingHom ⟨f.injective, hsurj⟩, fun x => f.commutes x⟩
private theorem hilbert_natural (K K' : Type) [Field K] [Field K']
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
    (e : K ≃+* K') (he : LocalClassFieldTheory.SemilinearValuationCompatible K K' e)
    (n : ℕ+) (hn : (n : K) ≠ 0) (hn' : (n : K') ≠ 0)
    (hm : (primitiveRoots (n : ℕ) K).Nonempty)
    (hm' : (primitiveRoots (n : ℕ) K').Nonempty) (a b : Kˣ) :
    ClassFieldTheory.rootsOfUnityEquivOfRingEquiv e n hm
        (ClassFieldTheory.localHilbertPairing K n hn hm
          (ClassFieldTheory.powerClass K n a) (ClassFieldTheory.powerClass K n b)) =
      ClassFieldTheory.localHilbertPairing K' n hn' hm'
          (ClassFieldTheory.powerClass K' n (Units.mapEquiv e.toMulEquiv a))
          (ClassFieldTheory.powerClass K' n (Units.mapEquiv e.toMulEquiv b)) := by
  let E := chosenSimpleKummerExtension K n hn b
  let a' : K'ˣ := Units.mapEquiv e.toMulEquiv a
  let b' : K'ˣ := Units.mapEquiv e.toMulEquiv b
  let E' := chosenSimpleKummerExtension K' n hn' b'
  letI : FiniteDimensional K E := chosenSimpleKummerExtension_finiteDimensional K n hn b
  letI : IsAbelianGalois K E := chosenSimpleKummerExtension_isAbelianGalois K n hn hm b
  letI : FiniteDimensional K' E' := chosenSimpleKummerExtension_finiteDimensional K' n hn' b'
  letI : IsAbelianGalois K' E' := chosenSimpleKummerExtension_isAbelianGalois K' n hn' hm' b'
  obtain ⟨eL, hc⟩ := kummer_equiv K K' e n hn hn' hm hm' b
  let β : Eˣ := chosenSimpleKummerRootUnit K n hn b
  let β' : E'ˣ := Units.mapEquiv eL.toMulEquiv β
  have hp : β' ^ (n : ℕ) = Units.map (algebraMap K' E').toMonoidHom b' := by
    apply Units.ext
    change (eL (β : E)) ^ (n : ℕ) = algebraMap K' E' (e (b : K))
    rw [← map_pow]
    have hp0 : (β : E) ^ (n : ℕ) = algebraMap K E (b : K) :=
      congrArg Units.val (chosenSimpleKummerRootUnit_pow K n hn b)
    rw [hp0, hc]
  have h1 := congrArg Units.val (ClassFieldTheory.localHilbertPairing_artin_rootQuotient K n hn hm b a)
  have h2 := congrArg Units.val
    (ClassFieldTheory.localHilbertPairing_artin_rootQuotient_of_same_pow K' n hn' hm' b' a' β' hp)
  let s := ClassFieldTheory.localHilbertPairing K n hn hm
    (ClassFieldTheory.powerClass K n a) (ClassFieldTheory.powerClass K n b)
  let t := ClassFieldTheory.localHilbertPairing K' n hn' hm'
    (ClassFieldTheory.powerClass K' n a') (ClassFieldTheory.powerClass K' n b')
  change algebraMap K E (s : Kˣ) =
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom K E a (β : E)) / (β : E) at h1
  simp only [rootQuotient, AlgEquiv.smul_units_def, Units.val_div_eq_div_val, Units.coe_map] at h2
  change algebraMap K' E' (t : K'ˣ) =
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom K' E' a' (β' : E')) / (β' : E') at h2
  apply Subtype.ext
  apply Units.ext
  change e (s : Kˣ) = (t : K'ˣ)
  apply (algebraMap K' E').injective
  rw [← hc, h1, map_div₀]
  rw [LocalClassFieldTheory.abelianLocalArtinMonoidHom_semilinear_action
    K K' E E' e eL hc he a (β : E)]
  exact h2.symm

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))
local instance : ValuativeRel (v.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F v
local instance : IsNonarchimedeanLocalField (v.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v

theorem finite_family_eq_local (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (hmuLocal : (primitiveRoots (n : ℕ) (v.adicCompletion F)).Nonempty)
    (a b : (v.adicCompletion F)ˣ) :
    ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F n hmu v
      (ClassFieldTheory.powerClass (v.adicCompletion F) n a)
      (ClassFieldTheory.powerClass (v.adicCompletion F) n b) =
    ClassFieldTheory.localHilbertPairing (v.adicCompletion F) n
      (Nat.cast_ne_zero.mpr n.ne_zero) hmuLocal
      (ClassFieldTheory.powerClass (v.adicCompletion F) n a)
      (ClassFieldTheory.powerClass (v.adicCompletion F) n b) := by
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  letI : ValuativeRel C :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  letI : CharZero C := charZero_of_injective_algebraMap (algebraMap F C).injective
  have hnC : ((n : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  have hmuC : (primitiveRoots (n : ℕ) C).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hmu
    exact ⟨algebraMap F C ζ,
      (mem_primitiveRoots n.pos).2
        (((mem_primitiveRoots n.pos).1 hζ).map_of_injective
          (algebraMap F C).injective)⟩
  let e : C ≃+* v.adicCompletion F :=
    (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let eu := Units.mapEquiv e.toMulEquiv
  change ClassFieldTheory.hilbertPairingOfRingEquiv e n hmuC
    (ClassFieldTheory.localHilbertPairing C n hnC hmuC)
    (ClassFieldTheory.powerClass (v.adicCompletion F) n a)
    (ClassFieldTheory.powerClass (v.adicCompletion F) n b) = _
  rw [ClassFieldTheory.hilbertPairingOfRingEquiv_apply,
    ClassFieldTheory.powerClassGroupEquivOfRingEquiv_symm_powerClass,
    ClassFieldTheory.powerClassGroupEquivOfRingEquiv_symm_powerClass]
  have h := hilbert_natural C (v.adicCompletion F) e
    (finitePlaceCompletion_semilinearValuationCompatible F v)
    n hnC (Nat.cast_ne_zero.mpr n.ne_zero) hmuC hmuLocal (eu.symm a) (eu.symm b)
  simpa only [eu, MulEquiv.apply_symm_apply] using h

end
end DedekindZetaZeroFree.RepresentationTheory.KPHilbertNormalization.LocalComparison

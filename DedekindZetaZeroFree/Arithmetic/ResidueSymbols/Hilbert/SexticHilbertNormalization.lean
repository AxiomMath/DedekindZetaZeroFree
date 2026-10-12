module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Hilbert.ProductFormula
public import DedekindZetaZeroFree.Arithmetic.Kummer.TwelfthRootsTotallyComplex
public import DedekindZetaZeroFree.Arithmetic.LocalFields.HilbertSymbolCompletionNaturality
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.ArithmeticTamePairing

@[expose] public section

open scoped NumberField Classical ValuativeRel
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree
namespace KPHilbert

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]

theorem primitive_six (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : IsPrimitiveRoot (ζ ^ 2) 6 :=
  hζ.pow (by decide) (by decide : 12 = 2 * 6)

theorem primitive_three (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : IsPrimitiveRoot (ζ ^ 4) 3 :=
  hζ.pow (by decide) (by decide : 12 = 4 * 3)

def rootsSix (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : (primitiveRoots 6 F).Nonempty :=
  ⟨ζ ^ 2, (mem_primitiveRoots (by decide : 0 < 6)).2 (primitive_six F ζ hζ)⟩

def rootsThree (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : (primitiveRoots 3 F).Nonempty :=
  ⟨ζ ^ 4, (mem_primitiveRoots (by decide : 0 < 3)).2 (primitive_three F ζ hζ)⟩

def finiteRootsSix (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (𝓞 F)) :
    rootsOfUnity 6 F ≃* rootsOfUnity 6 (v.adicCompletion F) :=
  rootsOfUnityEquivOfPrimitiveRoots (algebraMap F (v.adicCompletion F)).injective
    (rootsSix F ζ hζ)

def finiteRootsThree (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (𝓞 F)) :
    rootsOfUnity 3 F ≃* rootsOfUnity 3 (v.adicCompletion F) :=
  rootsOfUnityEquivOfPrimitiveRoots (algebraMap F (v.adicCompletion F)).injective
    (rootsThree F ζ hζ)

def finiteSixPairing (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (𝓞 F)) :
    ClassFieldTheory.PowerClassGroup (v.adicCompletion F) (6 : ℕ+) →*
      ClassFieldTheory.PowerClassGroup (v.adicCompletion F) (6 : ℕ+) →*
        rootsOfUnity 6 F :=
  NormalizedSymbolTransport.inverseTransport (finiteRootsSix F ζ hζ v)
    (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F (6 : ℕ+)
      (rootsSix F ζ hζ) v)

abbrev Place := InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)

abbrev Completion (v : Place F) : Type :=
  match v with
  | Sum.inl w => w.Completion
  | Sum.inr w => w.adicCompletion F

instance completionField (v : Place F) : Field (Completion F v) := by
  cases v <;> dsimp [Completion] <;> infer_instance

instance completionAlgebra (v : Place F) : Algebra F (Completion F v) := by
  cases v <;> dsimp [Completion] <;> infer_instance

instance completionTopology (v : Place F) : TopologicalSpace (Completion F v) := by
  cases v <;> dsimp [Completion] <;> infer_instance

def B6 (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : Place F) (a b : (Completion F v)ˣ) : rootsOfUnity 6 F :=
  match v with
  | Sum.inl _ => 1
  | Sum.inr w => finiteSixPairing F ζ hζ w
      (ClassFieldTheory.powerClass (w.adicCompletion F) (6 : ℕ+) a)
      (ClassFieldTheory.powerClass (w.adicCompletion F) (6 : ℕ+) b)

def squareToThree : rootsOfUnity 6 F →* rootsOfUnity 3 F where
  toFun z := ⟨(z : Fˣ) ^ 2, by
    change ((z : Fˣ) ^ 2) ^ 3 = 1
    rw [← pow_mul]
    exact z.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' := by intro x y; apply Subtype.ext; simp [mul_pow]

def B3 (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : Place F) (a b : (Completion F v)ˣ) : rootsOfUnity 3 F :=
  squareToThree F (B6 F ζ hζ v a b)

def finiteThreePairing (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (𝓞 F)) :
    ClassFieldTheory.PowerClassGroup (v.adicCompletion F) (3 : ℕ+) →*
      ClassFieldTheory.PowerClassGroup (v.adicCompletion F) (3 : ℕ+) →*
        rootsOfUnity 3 F :=
  NormalizedSymbolTransport.inverseTransport (finiteRootsThree F ζ hζ v)
    (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F (3 : ℕ+)
      (rootsThree F ζ hζ) v)

theorem infinite_isComplex (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (w : InfinitePlace F) :
    w.IsComplex := by
  letI := primitive12_totallyComplex F ζ hζ
  exact NumberField.IsTotallyComplex.isComplex w

theorem B6_infinite (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (w : InfinitePlace F)
    (a b : w.Completionˣ) : B6 F ζ hζ (Sum.inl w) a b = 1 := rfl

open ClassFieldTheory in
private theorem raw_three_six (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (𝓞 F))
    (a b : (v.adicCompletion F)ˣ) :
    ((finitePlaceAdicHilbertPairingFamily F 3 (rootsThree F ζ hζ) v
      (powerClass _ 3 a) (powerClass _ 3 b)) : (v.adicCompletion F)ˣ) =
    ((finitePlaceAdicHilbertPairingFamily F 6 (rootsSix F ζ hζ) v
      (powerClass _ 6 a) (powerClass _ 6 b)) : (v.adicCompletion F)ˣ) ^ 2 := by
  unfold finitePlaceAdicHilbertPairingFamily
  simp only [hilbertPairingOfRingEquiv_apply,
    powerClassGroupEquivOfRingEquiv_symm_powerClass]
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, rootsOfUnityEquivOfRingEquiv,
    val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe]
  rw [← map_pow]
  apply congrArg (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  simp only [localHilbertPairing_powerClass]
  exact congrArg Units.val (LocalClassFieldTheory.Kummer.localHilbertSymbol_exponentCompatibility
    (HeightOneSpectrum.adicAbv F v).Completion 3 6 _ _ _ _ (by decide) _ _)

theorem B3_canonical (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (v : HeightOneSpectrum (𝓞 F)) (a b : (v.adicCompletion F)ˣ) :
    B3 F ζ hζ (Sum.inr v) a b = finiteThreePairing F ζ hζ v
      (ClassFieldTheory.powerClass (v.adicCompletion F) 3 a)
      (ClassFieldTheory.powerClass (v.adicCompletion F) 3 b) := by
  apply rootsOfUnity.coe_injective
  apply (algebraMap F (v.adicCompletion F)).injective
  let r6 : rootsOfUnity 6 (v.adicCompletion F) := ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F 6 (rootsSix F ζ hζ) v
    (ClassFieldTheory.powerClass _ 6 a) (ClassFieldTheory.powerClass _ 6 b)
  let r3 : rootsOfUnity 3 (v.adicCompletion F) := ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F 3 (rootsThree F ζ hζ) v
    (ClassFieldTheory.powerClass _ 3 a) (ClassFieldTheory.powerClass _ 3 b)
  change algebraMap F (v.adicCompletion F)
      (((finiteRootsSix F ζ hζ v).symm (r6⁻¹) : Fˣ) ^ 2 : Fˣ) =
    algebraMap F (v.adicCompletion F) ((finiteRootsThree F ζ hζ v).symm (r3⁻¹) : Fˣ)
  rw [Units.val_pow_eq_pow_val, map_pow]
  rw [show algebraMap F (v.adicCompletion F)
      ((finiteRootsSix F ζ hζ v).symm (r6⁻¹) : Fˣ) = ((r6⁻¹ : rootsOfUnity 6 _) : (v.adicCompletion F)ˣ) from
        rootsOfUnityEquivOfPrimitiveRoots_symm_apply _ _ _,
    show algebraMap F (v.adicCompletion F)
      ((finiteRootsThree F ζ hζ v).symm (r3⁻¹) : Fˣ) = ((r3⁻¹ : rootsOfUnity 3 _) : (v.adicCompletion F)ˣ) from
        rootsOfUnityEquivOfPrimitiveRoots_symm_apply _ _ _]
  exact congrArg Units.val (by simpa only [map_inv, inv_pow] using
    (congrArg Inv.inv (raw_three_six F ζ hζ v a b)).symm)

open ClassFieldTheory in
private theorem raw_neg_self (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) :
    finitePlaceAdicHilbertPairingFamily F n hmu v
      (powerClass _ n a) (powerClass _ n (-a)) = 1 := by
  unfold finitePlaceAdicHilbertPairingFamily
  simp only [hilbertPairingOfRingEquiv_apply,
    powerClassGroupEquivOfRingEquiv_symm_powerClass, localHilbertPairing_powerClass]
  rw [show (Units.mapEquiv (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv.toMulEquiv).symm (-a) =
    -((Units.mapEquiv (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv.toMulEquiv).symm a) by
      apply Units.ext
      simp]
  unfold ClassFieldTheory.localHilbertSymbol
  rw [LocalClassFieldTheory.Kummer.localHilbertSymbol_neg_self]
  simp

open ClassFieldTheory in
private theorem transported_laws {K : Type} [Field K] {M : Type} [CommGroup M] (n : ℕ+) (B : HilbertPairing K n) (e : M ≃* rootsOfUnity (n : ℕ) K)
    (hB : B.IsLocalHilbertPairing)
    (hn : ∀ a : Kˣ, B (powerClass K n a) (powerClass K n (-a)) = 1)
    (hm : powerClass K n (-1) = 1) :
    let H := fun a b : Kˣ => DedekindZetaZeroFree.NormalizedSymbolTransport.inverseTransport e B
      (powerClass K n a) (powerClass K n b)
    (∀ a b c : Kˣ, H (a*b) c = H a c * H b c) ∧
    (∀ a b c : Kˣ, H a (b*c) = H a b * H a c) ∧
    (∀ a b : Kˣ, H a b = (H b a)⁻¹) ∧
    (∀ a b : Kˣ, (a : K) + b = 1 → H a b = 1) ∧
    (∀ a b : Kˣ, H (a ^ (n : ℕ)) b = 1 ∧ H a (b ^ (n : ℕ)) = 1) ∧
    ∀ a : Kˣ, H a a = 1 ∧ H a (-1) = 1 ∧ H a (-a) = 1 := by
  dsimp only
  let T := DedekindZetaZeroFree.NormalizedSymbolTransport.inverseTransport e B
  have hpow (a : Kˣ) : powerClass K n (a ^ (n : ℕ)) = 1 :=
    (powerClass_eq_one_iff _ _ _).2 ⟨a, rfl⟩
  have hneg (a : Kˣ) : T (powerClass K n a) (powerClass K n (-a)) = 1 := by
    simp only [T, DedekindZetaZeroFree.NormalizedSymbolTransport.inverseTransport_apply,
      hn, inv_one, map_one]
  have hminus (a : Kˣ) : T (powerClass K n a) (powerClass K n (-1)) = 1 := by
    rw [hm, map_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b c
    rw [map_mul, map_mul, MonoidHom.mul_apply]
  · intro a b c
    rw [map_mul, map_mul]
  · intro a b
    exact DedekindZetaZeroFree.NormalizedSymbolTransport.inverseTransport_skew e B hB.2.1 _ _
  · intro a b hab
    have hval : (b : K) = 1 - a := by linear_combination hab
    have hb : b = Units.mk0 (1 - (a : K)) (hval ▸ b.ne_zero) := by
      apply Units.ext
      exact hval
    rw [hb]
    simp only [DedekindZetaZeroFree.NormalizedSymbolTransport.inverseTransport_apply]
    rw [show B (powerClass K n a) (powerClass K n (Units.mk0 _ _)) = 1 from hB.1 a _]
    simp
  · intro a b
    constructor
    · rw [hpow, map_one, MonoidHom.one_apply]
    · rw [hpow, map_one]
  · intro a
    refine ⟨?_, hminus a, hneg a⟩
    have hh := hneg a
    rw [show -a = (-1 : Kˣ) * a by simp, map_mul, map_mul, hminus, one_mul] at hh
    exact hh

theorem B6_laws (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : Place F) :
    (∀ a b c : (Completion F v)ˣ,
      B6 F ζ hζ v (a * b) c = B6 F ζ hζ v a c * B6 F ζ hζ v b c) ∧
    (∀ a b c : (Completion F v)ˣ,
      B6 F ζ hζ v a (b * c) = B6 F ζ hζ v a b * B6 F ζ hζ v a c) ∧
    (∀ a b : (Completion F v)ˣ, B6 F ζ hζ v a b = (B6 F ζ hζ v b a)⁻¹) ∧
    (∀ a b : (Completion F v)ˣ, (a : Completion F v) + b = 1 →
      B6 F ζ hζ v a b = 1) ∧
    (∀ a b : (Completion F v)ˣ, B6 F ζ hζ v (a ^ 6) b = 1 ∧
      B6 F ζ hζ v a (b ^ 6) = 1) ∧
    ∀ a : (Completion F v)ˣ,
      B6 F ζ hζ v a a = 1 ∧ B6 F ζ hζ v a (-1) = 1 ∧
      B6 F ζ hζ v a (-a) = 1 := by
  cases v with
  | inl w => simp [B6]
  | inr w =>
    apply transported_laws 6
      (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F 6 (rootsSix F ζ hζ) w)
      (finiteRootsSix F ζ hζ w)
      (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F 6
        (rootsSix F ζ hζ) w) (raw_neg_self F 6 (rootsSix F ζ hζ) w)
    apply (ClassFieldTheory.powerClass_eq_one_iff _ _ _).2
    let z : (w.adicCompletion F)ˣ := Units.mk0
      (algebraMap F (w.adicCompletion F) ζ)
      ((algebraMap F (w.adicCompletion F)).injective.ne
        (hζ.ne_zero (by decide)))
    refine ⟨z, ?_⟩
    apply Units.ext
    change (algebraMap F (w.adicCompletion F) ζ) ^ 6 = -1
    rw [← map_pow,
      (hζ.pow (by decide) (by decide : 12 = 6 * 2)).eq_neg_one_of_two_right,
      map_neg, map_one]

theorem B3_laws (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : Place F) :
    (∀ a b c : (Completion F v)ˣ,
      B3 F ζ hζ v (a * b) c = B3 F ζ hζ v a c * B3 F ζ hζ v b c) ∧
    (∀ a b c : (Completion F v)ˣ,
      B3 F ζ hζ v a (b * c) = B3 F ζ hζ v a b * B3 F ζ hζ v a c) ∧
    (∀ a b : (Completion F v)ˣ, B3 F ζ hζ v a b = (B3 F ζ hζ v b a)⁻¹) ∧
    (∀ a b : (Completion F v)ˣ, (a : Completion F v) + b = 1 →
      B3 F ζ hζ v a b = 1) ∧
    (∀ a b : (Completion F v)ˣ, B3 F ζ hζ v (a ^ 3) b = 1 ∧
      B3 F ζ hζ v a (b ^ 3) = 1) ∧
    ∀ a : (Completion F v)ˣ,
      B3 F ζ hζ v a a = 1 ∧ B3 F ζ hζ v a (-1) = 1 ∧
      B3 F ζ hζ v a (-a) = 1 := by
  cases v with
  | inl w => simp [B3, B6]
  | inr w =>
    simp only [B3_canonical]
    apply transported_laws 3
      (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F 3 (rootsThree F ζ hζ) w)
      (finiteRootsThree F ζ hζ w)
      (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F 3
        (rootsThree F ζ hζ) w) (raw_neg_self F 3 (rootsThree F ζ hζ) w)
    apply (ClassFieldTheory.powerClass_eq_one_iff _ _ _).2
    refine ⟨-1, ?_⟩
    apply Units.ext
    norm_num [Units.val_pow_eq_pow_val]

open ClassFieldTheory in
private theorem continuous_powerClass_pair (K : Type) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    {M : Type} [TopologicalSpace M] (B : PowerClassGroup K n → PowerClassGroup K n → M) :
    Continuous (fun ab : Kˣ × Kˣ => B (powerClass K n ab.1) (powerClass K n ab.2)) := by
  obtain ⟨E, hE⟩ := LocalClassFieldTheory.exists_finiteGalois_normSubgroup_le_powMonoidHom_range K n hn
  letI : FiniteDimensional K (E : IntermediateField K (SeparableClosure K)) := E.finiteDimensional
  letI : IsGalois K (E : IntermediateField K (SeparableClosure K)) := E.isGalois
  have hopen : IsOpen ((powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range : Set Kˣ) :=
    Subgroup.isOpen_mono hE
      (LocalClassFieldTheory.localNormSubgroup_isOpen K (E : IntermediateField K (SeparableClosure K)))
  letI : TopologicalSpace (PowerClassGroup K n) :=
    inferInstanceAs (TopologicalSpace (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range))
  haveI : DiscreteTopology (PowerClassGroup K n) :=
    QuotientGroup.discreteTopology hopen
  have hc : Continuous (powerClass K n) := QuotientGroup.continuous_mk
  exact (continuous_of_discreteTopology : Continuous (fun xy : PowerClassGroup K n × PowerClassGroup K n => B xy.1 xy.2)).comp
    ((hc.comp continuous_fst).prodMk (hc.comp continuous_snd))

theorem B6_continuous (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : Place F) :
    letI : TopologicalSpace (rootsOfUnity 6 F) := ⊥
    Continuous (fun ab : (Completion F v)ˣ × (Completion F v)ˣ =>
      B6 F ζ hζ v ab.1 ab.2) := by
  letI : TopologicalSpace (rootsOfUnity 6 F) := ⊥
  cases v with
  | inl w => exact continuous_const
  | inr w =>
    letI : ValuativeRel (w.adicCompletion F) :=
      ClassFieldTheory.finitePlaceCompletionValuativeRel F w
    letI : IsNonarchimedeanLocalField (w.adicCompletion F) :=
      ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F w
    exact continuous_powerClass_pair (w.adicCompletion F) 6
      (Nat.cast_ne_zero.mpr (by decide))
      (fun a b => finiteSixPairing F ζ hζ w a b)

theorem B3_continuous (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : Place F) :
    letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
    Continuous (fun ab : (Completion F v)ˣ × (Completion F v)ˣ =>
      B3 F ζ hζ v ab.1 ab.2) := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : TopologicalSpace (rootsOfUnity 6 F) := ⊥
  haveI : DiscreteTopology (rootsOfUnity 6 F) := ⟨rfl⟩
  exact (continuous_of_discreteTopology : Continuous (squareToThree F)).comp
    (B6_continuous F ζ hζ v)

def diagonal (v : Place F) : Fˣ →* (Completion F v)ˣ :=
  Units.map (algebraMap F (Completion F v)).toMonoidHom

theorem B6_productFormula (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (a b : Fˣ) :
    Function.HasFiniteMulSupport (fun v : Place F =>
      B6 F ζ hζ v (diagonal F v a) (diagonal F v b)) ∧
    (∏ᶠ v : Place F, B6 F ζ hζ v (diagonal F v a) (diagonal F v b)) = 1 := by
  let f := fun v : Place F => B6 F ζ hζ v (diagonal F v a) (diagonal F v b)
  let g : HeightOneSpectrum (𝓞 F) → rootsOfUnity 6 F := fun v =>
    ClassFieldTheory.GlobalHilbertPairingFamily.finiteFactor F
      (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F 6 (rootsSix F ζ hζ))
      (rootsSix F ζ hζ) v a b
  have hg := (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_productFormula
    F 6 (rootsSix F ζ hζ)).2.1 a b
  have hfg (v : HeightOneSpectrum (𝓞 F)) : f (Sum.inr v) = (g v)⁻¹ := by
    change (finiteRootsSix F ζ hζ v).symm (_⁻¹) = _
    rw [map_inv]
    rfl
  have hsub : Function.mulSupport f ⊆ Sum.inr '' Function.mulSupport g := by
    intro v hv
    cases v with
    | inl w => exact (hv rfl).elim
    | inr w =>
      refine ⟨w, ?_, rfl⟩
      intro hw
      exact hv (by rw [hfg, hw, inv_one])
  have hf : Function.HasFiniteMulSupport f := (hg.image Sum.inr).subset hsub
  have hp : (∏ᶠ v, g v) = 1 := by
    have h := (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_productFormula
        F 6 (rootsSix F ζ hζ)).2.2 a b
    simp only [ClassFieldTheory.globalInfinitePlaceHilbertSymbol,
      show ((6 : ℕ+) : ℕ) ≠ 2 by decide, dite_false,
      Finset.prod_const_one, one_mul] at h
    convert h using 1 <;> rfl
  refine ⟨hf, ?_⟩
  change (∏ᶠ v, f v) = 1
  calc
    (∏ᶠ v, f v) = ∏ᶠ v ∈ Set.range (Sum.inr : HeightOneSpectrum (𝓞 F) → Place F), f v := by
      rw [← finprod_mem_mulSupport f,
        ← finprod_mem_inter_mulSupport f (Set.range Sum.inr)]
      rw [Set.inter_eq_right.mpr (hsub.trans (Set.image_subset_range _ _))]
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 F), f (Sum.inr v) :=
      finprod_mem_range Sum.inr_injective
    _ = ∏ᶠ v, (g v)⁻¹ := finprod_congr hfg
    _ = 1 := by rw [finprod_inv_distrib, hp, inv_one]

theorem B3_productFormula (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (a b : Fˣ) :
    Function.HasFiniteMulSupport (fun v : Place F =>
      B3 F ζ hζ v (diagonal F v a) (diagonal F v b)) ∧
    (∏ᶠ v : Place F, B3 F ζ hζ v (diagonal F v a) (diagonal F v b)) = 1 := by
  obtain ⟨hf, hp⟩ := B6_productFormula F ζ hζ a b
  have hfs : Function.HasFiniteMulSupport (fun v : Place F =>
      squareToThree F (B6 F ζ hζ v (diagonal F v a) (diagonal F v b))) :=
    hf.fun_comp (squareToThree F).map_one
  refine ⟨hfs, ?_⟩
  change (∏ᶠ v : Place F, squareToThree F
    (B6 F ζ hζ v (diagonal F v a) (diagonal F v b))) = 1
  rw [← MonoidHom.map_finprod (squareToThree F) hf, hp, map_one]

section FiniteNormalization

variable (v : HeightOneSpectrum (𝓞 F))
local instance : ValuativeRel (v.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F v
local instance : IsNonarchimedeanLocalField (v.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v

def localRootsSix (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    (primitiveRoots 6 (v.adicCompletion F)).Nonempty :=
  ⟨algebraMap F (v.adicCompletion F) (ζ ^ 2),
    (mem_primitiveRoots (by decide : 0 < 6)).2
      ((primitive_six F ζ hζ).map_of_injective
        (algebraMap F (v.adicCompletion F)).injective)⟩

theorem B6_localCanonical (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (a b : (v.adicCompletion F)ˣ) :
    finiteRootsSix F ζ hζ v (B6 F ζ hζ (Sum.inr v) a b) =
      ClassFieldTheory.localHilbertPairing (v.adicCompletion F) 6
        (by exact Nat.cast_ne_zero.mpr (by decide : (6 : ℕ) ≠ 0))
        (localRootsSix F v ζ hζ)
        (ClassFieldTheory.powerClass (v.adicCompletion F) 6 b)
        (ClassFieldTheory.powerClass (v.adicCompletion F) 6 a) := by
  change finiteRootsSix F ζ hζ v
    (NormalizedSymbolTransport.inverseTransport (finiteRootsSix F ζ hζ v)
      (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F 6
        (rootsSix F ζ hζ) v)
      (ClassFieldTheory.powerClass _ 6 a) (ClassFieldTheory.powerClass _ 6 b)) = _
  change (finiteRootsSix F ζ hζ v) ((finiteRootsSix F ζ hζ v).symm
    ((ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F 6
      (rootsSix F ζ hζ) v (ClassFieldTheory.powerClass _ 6 a)
        (ClassFieldTheory.powerClass _ 6 b))⁻¹)) = _
  rw [MulEquiv.apply_symm_apply]
  have hswap := (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_isLocallyHilbert
    F 6 (rootsSix F ζ hζ) v).2.1
    (ClassFieldTheory.powerClass _ 6 b) (ClassFieldTheory.powerClass _ 6 a)
  exact hswap.symm.trans
    (RepresentationTheory.KPHilbertNormalization.LocalComparison.finite_family_eq_local F v 6
      (rootsSix F ζ hζ) (localRootsSix F v ζ hζ) b a)

abbrev LocalIntegerUnits := (ValuativeRel.valuation (v.adicCompletion F)).integerˣ

def ordinaryValuation (a : (v.adicCompletion F)ˣ) : ℤ :=
  -LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
    (v.adicCompletion F) (Additive.ofMul a)

def integerUnitInclusion : LocalIntegerUnits F v →* (v.adicCompletion F)ˣ :=
  LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits (v.adicCompletion F)

def residueSixCharacter (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hgood : ValuativeRel.valuation (v.adicCompletion F) (6 : v.adicCompletion F) = 1)
    (u : LocalIntegerUnits F v) : rootsOfUnity 6 F :=
  (finiteRootsSix F ζ hζ v).symm
    (KummerTheory.nthRootsSubgroupEquivRootsOfUnity (v.adicCompletion F) 6
      (LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol
        (v.adicCompletion F) 6 hgood (localRootsSix F v ζ hζ) u))

theorem tame_place_iff :
    ValuativeRel.valuation (v.adicCompletion F) (6 : v.adicCompletion F) = 1 ↔
      (6 : 𝓞 F) ∉ v.asIdeal := by
  letI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [← (ValuativeRel.isEquiv (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))) (ValuativeRel.valuation (v.adicCompletion F))).eq_one_iff_eq_one]
  have h := v.valuedAdicCompletion_eq_valuation (K := F) (6 : 𝓞 F)
  have hp : v.valuation F (algebraMap (𝓞 F) F 6) = 1 ↔ (6 : 𝓞 F) ∉ v.asIdeal :=
    v.valuation_eq_one_iff_notMem (K := F)
  rw [← h] at hp
  simpa only [map_ofNat] using hp

theorem B6_tame_ordinaryValuation (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hgood : ValuativeRel.valuation (v.adicCompletion F) (6 : v.adicCompletion F) = 1)
    (x : (v.adicCompletion F)ˣ) (u u' : LocalIntegerUnits F v) :
    B6 F ζ hζ (Sum.inr v) x (integerUnitInclusion F v u) =
      residueSixCharacter F v ζ hζ hgood u ^ ordinaryValuation F v x ∧
    B6 F ζ hζ (Sum.inr v) (integerUnitInclusion F v u)
      (integerUnitInclusion F v u') = 1 := by
  obtain ⟨hx, hu⟩ := RepresentationTheory.KPHilbertNormalization.TamePairing.arithmetic_tame_pairing
    (v.adicCompletion F) 6 hgood (localRootsSix F v ζ hζ) x u u'
  constructor
  · apply (finiteRootsSix F ζ hζ v).injective
    rw [B6_localCanonical]
    change _ = (finiteRootsSix F ζ hζ v)
      ((finiteRootsSix F ζ hζ v).symm _ ^ ordinaryValuation F v x)
    rw [map_zpow, MulEquiv.apply_symm_apply]
    have hx' := hx.trans (map_zpow (KummerTheory.nthRootsSubgroupEquivRootsOfUnity
      (v.adicCompletion F) 6) _ _)
    exact hx'
  · apply (finiteRootsSix F ζ hζ v).injective
    rw [B6_localCanonical, map_one]
    exact hu

theorem B6_tame (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hgood : ValuativeRel.valuation (v.adicCompletion F) (6 : v.adicCompletion F) = 1)
    (π : (v.adicCompletion F)ˣ) (hπ : ordinaryValuation F v π = 1)
    (u u' : LocalIntegerUnits F v) :
    B6 F ζ hζ (Sum.inr v) π (integerUnitInclusion F v u) =
      residueSixCharacter F v ζ hζ hgood u ∧
    B6 F ζ hζ (Sum.inr v) (integerUnitInclusion F v u)
      (integerUnitInclusion F v u') = 1 := by
  simpa only [hπ, zpow_one] using
    B6_tame_ordinaryValuation F v ζ hζ hgood π u u'

end FiniteNormalization

theorem B6_S_product (A : SArithmeticData F) (x y : A.G) :
    (∏ v : {v // v ∈ A.Sf},
      B6 F A.zeta12 A.primitive_zeta12 (Sum.inr v.val) (x.2 v) (y.2 v)) =
        A.H_S x y := by
  rfl

end
end KPHilbert
end DedekindZetaZeroFree

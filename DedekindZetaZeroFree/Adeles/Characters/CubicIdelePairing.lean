module

public import DedekindZetaZeroFree.Adeles.Quotients.CubicClassCoordinateTopology
public import DedekindZetaZeroFree.Metaplectic.Torus.CubicAdelicCommutator
public import DedekindZetaZeroFree.Adeles.Quotients.CubicUnitValuationDecomposition
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.TameLocalNondegeneracy

@[expose] public section

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalCubicIdelePairing

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev Ideles := KPAdelicCoverRestrictedProduct.Ideles F

abbrev D := Ideles F ⧸ CubicCharacters.cubes (Ideles F)

abbrev LocalD (v : KPHilbert.Place F) :=
  KPLocalTorus.CubeClasses (KPHilbert.Completion F v)ˣ

def localClass (v : KPHilbert.Place F) : (KPHilbert.Completion F v)ˣ →* LocalD F v :=
  QuotientGroup.mk' (CubicCharacters.cubes (KPHilbert.Completion F v)ˣ)

def U (v : KPHilbert.Place F) : Subgroup (LocalD F v) :=
  match v with
  | Sum.inl _ => ⊤
  | Sum.inr q => (KPHilbert.integerUnitInclusion F q).range.map (localClass F (Sum.inr q))

abbrev RestrictedClasses := RestrictedProduct (LocalD F)
  (fun v => (U F v : Set _)) Filter.cofinite

def ideleEval (v : KPHilbert.Place F) : Ideles F →* (KPHilbert.Completion F v)ˣ :=
  Units.map (KPAdelicCoverRestrictedProduct.adeleEval F v)

theorem ideleClass_restricted (x : Ideles F) :
    ∀ᶠ v in Filter.cofinite, localClass F v (ideleEval F v x) ∈ U F v := by
  have hi : ∀ᶠ q : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∃ u : KPHilbert.LocalIntegerUnits F q,
        KPHilbert.integerUnitInclusion F q u = ideleEval F (Sum.inr q) x := by
    filter_upwards [(x.val.2).property, (x.inv.2).property] with q hq hqi
    letI : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
    letI : (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    have mem (a : q.adicCompletion F) (ha : a ∈ q.adicCompletionIntegers F) :
        a ∈ (ValuativeRel.valuation (q.adicCompletion F)).integer := by
      rw [Valuation.mem_integer_iff, ← Valuation.vle_one_iff]
      exact (Valuation.vle_one_iff
        (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)))).mpr ha
    let z := ideleEval F (Sum.inr q) x
    let u : KPHilbert.LocalIntegerUnits F q :=
      ⟨⟨(z : q.adicCompletion F), mem _ hq⟩,
       ⟨(z⁻¹ : (q.adicCompletion F)ˣ), mem _ hqi⟩,
       by apply Subtype.ext; exact z.val_inv,
       by apply Subtype.ext; exact z.inv_val⟩
    exact ⟨u, rfl⟩
  have hf : {q : HeightOneSpectrum (𝓞 F) | ¬ ∃ u : KPHilbert.LocalIntegerUnits F q,
      KPHilbert.integerUnitInclusion F q u = ideleEval F (Sum.inr q) x}.Finite :=
    Filter.mem_cofinite.mp hi
  filter_upwards [(hf.image (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F)).compl_mem_cofinite] with v hv
  cases v with
  | inl w => exact Subgroup.mem_top _
  | inr q =>
    have hq : ∃ u : KPHilbert.LocalIntegerUnits F q,
        KPHilbert.integerUnitInclusion F q u = ideleEval F (Sum.inr q) x := by
      by_contra h
      exact hv ⟨q, h, rfl⟩
    obtain ⟨u, hu⟩ := hq
    exact ⟨_, ⟨u, rfl⟩, congrArg (localClass F (Sum.inr q)) hu⟩

def restrictedClassMap : Ideles F →* RestrictedClasses F where
  toFun x := ⟨fun v => localClass F v (ideleEval F v x), ideleClass_restricted F x⟩
  map_one' := by ext v; simp
  map_mul' x y := by
    ext v
    change localClass F v (ideleEval F v (x * y)) =
      localClass F v (ideleEval F v x) * localClass F v (ideleEval F v y)
    simp

theorem restrictedClassMap_kills_cubes :
    CubicCharacters.cubes (Ideles F) ≤ (restrictedClassMap F).ker := by
  rintro x ⟨y, rfl⟩
  change restrictedClassMap F (y ^ 3) = 1
  ext v
  change localClass F v (ideleEval F v (y ^ 3)) = 1
  rw [map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨ideleEval F v y, rfl⟩

def classComparison : D F →* RestrictedClasses F :=
  QuotientGroup.lift _ (restrictedClassMap F) (restrictedClassMap_kills_cubes F)

private theorem idele_of_coordinates (a : ∀ v, (KPHilbert.Completion F v)ˣ)
    (ha : ∀ᶠ q : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ((a (Sum.inr q) : q.adicCompletion F) ∈ q.adicCompletionIntegers F) ∧
      (((a (Sum.inr q))⁻¹ : (q.adicCompletion F)ˣ) : q.adicCompletion F) ∈ q.adicCompletionIntegers F) :
    ∃ x : Ideles F, ∀ v, ideleEval F v x = a v := by
  let x : Ideles F :=
    { val := (fun w => (a (Sum.inl w) : w.Completion), ⟨fun q => (a (Sum.inr q) : q.adicCompletion F), ha.mono fun q h => h.1⟩)
      inv := (fun w => (((a (Sum.inl w))⁻¹ : w.Completionˣ) : w.Completion), ⟨fun q => (((a (Sum.inr q))⁻¹ : (q.adicCompletion F)ˣ) : q.adicCompletion F), ha.mono fun q h => h.2⟩)
      val_inv := by
        apply Prod.ext
        · funext w; exact (a (Sum.inl w)).val_inv
        · apply RestrictedProduct.ext
          intro q; exact (a (Sum.inr q)).val_inv
      inv_val := by
        apply Prod.ext
        · funext w; exact (a (Sum.inl w)).inv_val
        · apply RestrictedProduct.ext
          intro q; exact (a (Sum.inr q)).inv_val }
  exact ⟨x, fun v => by cases v <;> apply Units.ext <;> rfl⟩

private theorem restricted_cube_root (x : Ideles F) (hx : restrictedClassMap F x = 1) :
    x ∈ CubicCharacters.cubes (Ideles F) := by
  have hr (v : KPHilbert.Place F) : ∃ a : (KPHilbert.Completion F v)ˣ, a ^ 3 = ideleEval F v x := by
    have h := congrArg (fun y : RestrictedClasses F => y v) hx
    change localClass F v (ideleEval F v x) = 1 at h
    exact (QuotientGroup.eq_one_iff _).mp h
  choose a ha using hr
  have hint : ∀ᶠ q : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ((a (Sum.inr q) : q.adicCompletion F) ∈ q.adicCompletionIntegers F) ∧
      (((a (Sum.inr q))⁻¹ : (q.adicCompletion F)ˣ) : q.adicCompletion F) ∈ q.adicCompletionIntegers F := by
    filter_upwards [x.val.2.property, x.inv.2.property] with q hq hqi
    have hp : (a (Sum.inr q) : q.adicCompletion F) ^ 3 = (ideleEval F (Sum.inr q) x : q.adicCompletion F) := congrArg Units.val (ha (Sum.inr q))
    have hpi : (((a (Sum.inr q))⁻¹ : (q.adicCompletion F)ˣ) : q.adicCompletion F) ^ 3 = (((ideleEval F (Sum.inr q) x)⁻¹ : (q.adicCompletion F)ˣ) : q.adicCompletion F) := by simpa using congrArg (fun u : (q.adicCompletion F)ˣ => ((u⁻¹ : (q.adicCompletion F)ˣ) : q.adicCompletion F)) (ha (Sum.inr q))
    constructor
    · change (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ))) _ ≤ 1
      have hh : Valued.v ((a (Sum.inr q) : q.adicCompletion F) ^ 3) ≤ 1 := hp ▸ hq
      rw [map_pow] at hh
      exact (pow_le_one_iff (by decide : (3 : ℕ) ≠ 0)).mp hh
    · change (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ))) _ ≤ 1
      have hh : Valued.v ((((a (Sum.inr q))⁻¹ : (q.adicCompletion F)ˣ) : q.adicCompletion F) ^ 3) ≤ 1 := hpi ▸ hqi
      rw [map_pow] at hh
      exact (pow_le_one_iff (by decide : (3 : ℕ) ≠ 0)).mp hh
  obtain ⟨y, hy⟩ := idele_of_coordinates F a hint
  refine ⟨y, ?_⟩
  apply Units.ext
  apply Prod.ext
  · funext w
    exact congrArg Units.val ((map_pow (ideleEval F (Sum.inl w)) y 3).trans ((congrArg (fun z : w.Completionˣ => z ^ 3) (hy (Sum.inl w))).trans (ha (Sum.inl w))))
  · apply RestrictedProduct.ext
    intro q
    exact congrArg Units.val ((map_pow (ideleEval F (Sum.inr q)) y 3).trans ((congrArg (fun z : (q.adicCompletion F)ˣ => z ^ 3) (hy (Sum.inr q))).trans (ha (Sum.inr q))))

theorem classComparison_injective : Function.Injective (classComparison F) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro d hd
  induction d using QuotientGroup.induction_on with
  | H x =>
    apply (QuotientGroup.eq_one_iff _).mpr
    apply restricted_cube_root F x
    exact hd

theorem classComparison_surjective : Function.Surjective (classComparison F) := by
  intro d
  have hreps (v : KPHilbert.Place F) : ∃ a : (KPHilbert.Completion F v)ˣ,
      localClass F v a = d v ∧
      (d v ∈ U F v → ∀ q, v = Sum.inr q →
        ∃ u : KPHilbert.LocalIntegerUnits F q,
          HEq (KPHilbert.integerUnitInclusion F q u) a) := by
    cases v with
    | inl w =>
      obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective _ (d (Sum.inl w))
      refine ⟨a, ha, ?_⟩
      intro h q hq
      cases hq
    | inr q =>
      by_cases hd : d (Sum.inr q) ∈ U F (Sum.inr q)
      · obtain ⟨a, ⟨u, rfl⟩, hu⟩ := hd
        refine ⟨KPHilbert.integerUnitInclusion F q u, hu, ?_⟩
        intro h r hr
        cases hr
        exact ⟨u, HEq.rfl⟩
      · obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective _ (d (Sum.inr q))
        exact ⟨a, ha, fun h => (hd h).elim⟩
  choose a ha hu using hreps
  have hi : ∀ᶠ q : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (a (Sum.inr q) : q.adicCompletion F) ∈ q.adicCompletionIntegers F ∧
      (((a (Sum.inr q))⁻¹ : (q.adicCompletion F)ˣ) : q.adicCompletion F) ∈ q.adicCompletionIntegers F := by
    have hd : ∀ᶠ q : HeightOneSpectrum (𝓞 F) in Filter.cofinite, d (Sum.inr q) ∈ U F (Sum.inr q) :=
      Sum.inr_injective.tendsto_cofinite d.property
    filter_upwards [hd] with q hq
    obtain ⟨u, he⟩ := hu (Sum.inr q) hq q rfl
    have he' : KPHilbert.integerUnitInclusion F q u = a (Sum.inr q) := eq_of_heq he
    rw [← he']
    letI : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
    letI : (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
    have mem (b : q.adicCompletion F) (hb : b ∈ (ValuativeRel.valuation (q.adicCompletion F)).integer) :
        b ∈ q.adicCompletionIntegers F := by
      rw [Valuation.mem_integer_iff, ← Valuation.vle_one_iff] at hb
      exact (Valuation.vle_one_iff (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)))).mp hb
    exact ⟨mem _ u.val.property, mem _ u.inv.property⟩
  obtain ⟨x, hx⟩ := idele_of_coordinates F a hi
  refine ⟨QuotientGroup.mk' _ x, ?_⟩
  ext v
  change localClass F v (ideleEval F v x) = d v
  rw [hx, ha]

theorem restricted_cube_quotient :
    ∃ e : D F ≃ₜ* RestrictedClasses F,
      ∀ d : D F, e d = classComparison F d := by
  have hb : Function.Bijective (classComparison F) :=
    ⟨classComparison_injective F, classComparison_surjective F⟩
  let e : D F ≃* RestrictedClasses F := MulEquiv.ofBijective (classComparison F) hb
  have hc : Continuous (classComparison F) ∧ IsOpenMap (classComparison F) :=
    DedekindZetaZeroFree.RepresentationTheory.KPGlobalCubicIdelePairingRaw.class_comparison_continuous_open F
  let h : D F ≃ₜ RestrictedClasses F :=
    e.toEquiv.toHomeomorphOfContinuousOpen hc.1 hc.2
  let e' : D F ≃ₜ* RestrictedClasses F :=
    { toMulEquiv := e
      continuous_toFun := h.continuous_toFun
      continuous_invFun := h.continuous_invFun }
  exact ⟨e', fun _ => rfl⟩

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem local_complex_trivial (w : InfinitePlace F) : Subsingleton (LocalD F (Sum.inl w)) := by
  rw [QuotientGroup.subsingleton_iff, Subgroup.eq_top_iff']
  intro u
  have roots : ∀ x : w.Completion, ∃ y, y ^ 3 = x := by
    intro x
    rcases w.isReal_or_isComplex with hw | hw
    · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      have hbot : Filter.Tendsto (fun y : ℝ => y ^ 3) Filter.atBot Filter.atBot := by
        simpa only [Function.comp_def, pow_succ, pow_zero, mul_one, neg_mul, mul_neg, neg_neg] using
          (Filter.tendsto_neg_atTop_atBot (G := ℝ)).comp
          ((Filter.tendsto_pow_atTop (by decide : 3 ≠ 0)).comp
            (Filter.tendsto_neg_atBot_atTop (G := ℝ)))
      obtain ⟨y, hy⟩ := ((show Continuous (fun y : ℝ => y ^ 3) from continuous_id.pow 3).surjective
        (Filter.tendsto_pow_atTop (by decide : 3 ≠ 0)) hbot) (e x)
      refine ⟨e.symm y, ?_⟩
      apply e.injective
      simpa using hy
    · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (e x) (by decide : 0 < 3)
      refine ⟨e.symm y, ?_⟩
      apply e.injective
      simpa using hy
  obtain ⟨y, hy⟩ := roots u
  have hne : y ≠ 0 := by
    intro h
    apply Units.ne_zero u
    simpa [h] using hy.symm
  exact ⟨Units.mk0 y hne, Units.ext hy⟩

theorem exponent_three (d : D F) : d ^ 3 = 1 := by
  induction d using QuotientGroup.induction_on with
  | H x =>
    change (QuotientGroup.mk' _ x) ^ 3 = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨x, rfl⟩

theorem locally_compact : LocallyCompactSpace (D F) := by
  infer_instance

private theorem local_discrete (v : KPHilbert.Place F) : DiscreteTopology (LocalD F v) := by
  cases v with
  | inl w =>
    letI := local_complex_trivial F w
    infer_instance
  | inr q =>
    let K := q.adicCompletion F
    letI : ValuativeRel K := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
    letI : IsNonarchimedeanLocalField K := ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
    obtain ⟨E, hE⟩ := LocalClassFieldTheory.exists_finiteGalois_normSubgroup_le_powMonoidHom_range K 3 (Nat.cast_ne_zero.mpr (by decide))
    letI : FiniteDimensional K (E : IntermediateField K (SeparableClosure K)) := E.finiteDimensional
    letI : IsGalois K (E : IntermediateField K (SeparableClosure K)) := E.isGalois
    have hopen : IsOpen ((powMonoidHom 3 : Kˣ →* Kˣ).range : Set Kˣ) :=
      Subgroup.isOpen_mono hE (LocalClassFieldTheory.localNormSubgroup_isOpen K (E : IntermediateField K (SeparableClosure K)))
    exact QuotientGroup.discreteTopology hopen
private theorem classCoordinates_continuous :
    Continuous (fun d : D F => (classComparison F d : ∀ v, LocalD F v)) := by
  apply continuous_pi
  intro v
  apply (QuotientGroup.isQuotientMap_mk (CubicCharacters.cubes (Ideles F))).continuous_iff.mpr
  change Continuous (fun x : Ideles F => localClass F v (ideleEval F v x))
  apply QuotientGroup.continuous_mk.comp
  apply Units.continuous_map
  cases v with
  | inl w => exact (continuous_apply w).comp continuous_fst
  | inr q => exact (RestrictedProduct.continuous_eval q).comp continuous_snd

theorem hausdorff : T2Space (D F) := by
  letI (v : KPHilbert.Place F) := local_discrete F v
  apply T2Space.of_injective_continuous (f := fun d : D F => (classComparison F d : ∀ v, LocalD F v))
  · intro x y h
    apply classComparison_injective F
    ext v
    exact congrFun h v
  · exact classCoordinates_continuous F

theorem localSymbol_congr (v : KPHilbert.Place F)
    (a b a' b' : (KPHilbert.Completion F v)ˣ)
    (ha : QuotientGroup.leftRel (CubicCharacters.cubes (KPHilbert.Completion F v)ˣ) a a')
    (hb : QuotientGroup.leftRel (CubicCharacters.cubes (KPHilbert.Completion F v)ˣ) b b') :
    KPHilbert.B3 F ζ hζ v a b = KPHilbert.B3 F ζ hζ v a' b' := by
  obtain ⟨t, ht⟩ := QuotientGroup.leftRel_apply.mp ha
  obtain ⟨u, hu⟩ := QuotientGroup.leftRel_apply.mp hb
  have ht' : a' = a * t ^ 3 := by
    change t ^ 3 = a⁻¹ * a' at ht
    rw [ht, mul_inv_cancel_left]
  have hu' : b' = b * u ^ 3 := by
    change u ^ 3 = b⁻¹ * b' at hu
    rw [hu, mul_inv_cancel_left]
  rw [ht', hu', (KPHilbert.B3_laws F ζ hζ v).1,
    (KPHilbert.B3_laws F ζ hζ v).2.1]
  rw [(KPHilbert.B3_laws F ζ hζ v).2.2.2.2.1 t (b * u ^ 3) |>.1,
    (KPHilbert.B3_laws F ζ hζ v).2.2.2.2.1 a u |>.2]
  simp

def localPairing (v : KPHilbert.Place F) (a b : LocalD F v) : rootsOfUnity 3 F :=
  Quotient.liftOn₂ a b (KPHilbert.B3 F ζ hζ v) (localSymbol_congr F ζ hζ v)

@[simp] theorem localPairing_representatives (v : KPHilbert.Place F)
    (a b : (KPHilbert.Completion F v)ˣ) :
    localPairing F ζ hζ v (localClass F v a) (localClass F v b) =
      KPHilbert.B3 F ζ hζ v a b := rfl

theorem tame_unit_isotropic (q : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ KPAdelicCoverRestrictedProduct.Bad F q)
    (a b : LocalD F (Sum.inr q)) (ha : a ∈ U F (Sum.inr q))
    (hb : b ∈ U F (Sum.inr q)) :
    localPairing F ζ hζ (Sum.inr q) a b = 1 := by
  obtain ⟨a, ⟨u, rfl⟩, rfl⟩ := ha
  obtain ⟨b, ⟨w, rfl⟩, rfl⟩ := hb
  exact KPTameCompact.B3_units F q ζ hζ
    (fun h => hgood (Or.inr h)) u w

theorem pairing_finiteSupport (x y : RestrictedClasses F) :
    Function.HasFiniteMulSupport (fun v => localPairing F ζ hζ v (x v) (y v)) := by
  have hgood : ∀ᶠ v : KPHilbert.Place F in Filter.cofinite,
      ∀ q, v = Sum.inr q → ¬ KPAdelicCoverRestrictedProduct.Bad F q := by
    have hf := (KPAdelicCoverRestrictedProduct.bad_finite F).image
      (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F)
    filter_upwards [hf.compl_mem_cofinite] with v hv q hq
    intro hbad
    exact hv ⟨q, hbad, hq.symm⟩
  have heq : ∀ᶠ v in Filter.cofinite, localPairing F ζ hζ v (x v) (y v) = 1 := by
    filter_upwards [x.property, y.property, hgood] with v hx hy hv
    cases v with
    | inl w =>
      induction (x (Sum.inl w)) using QuotientGroup.induction_on with
      | H a =>
        induction (y (Sum.inl w)) using QuotientGroup.induction_on with
        | H b => simp [localPairing, KPHilbert.B3, KPHilbert.B6]
    | inr q => exact tame_unit_isotropic F ζ hζ q (hv q rfl) _ _ hx hy
  exact Filter.mem_cofinite.mp heq

def restrictedBeta (x y : RestrictedClasses F) : rootsOfUnity 3 F :=
  ∏ᶠ v, localPairing F ζ hζ v (x v) (y v)

def beta3 (x y : D F) : rootsOfUnity 3 F :=
  restrictedBeta F ζ hζ (classComparison F x) (classComparison F y)

theorem beta3_idele_formula (x y : Ideles F) :
    beta3 F ζ hζ (QuotientGroup.mk' _ x) (QuotientGroup.mk' _ y) =
      ∏ᶠ v, KPHilbert.B3 F ζ hζ v (ideleEval F v x) (ideleEval F v y) := by
  rfl

theorem beta3_continuous :
    letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
    Continuous (fun xy : D F × D F => beta3 F ζ hζ xy.1 xy.2) := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  letI (v : KPHilbert.Place F) := local_discrete F v
  obtain ⟨e, he⟩ := restricted_cube_quotient F
  have hc : Continuous (fun xy : RestrictedClasses F × RestrictedClasses F => restrictedBeta F ζ hζ xy.1 xy.2) := by
    apply (RestrictedProduct.continuous_dom_prod (fun v => isOpen_discrete _) (fun v => isOpen_discrete _)).mpr
    intro S hS
    have hf : Sᶜ.Finite := Filter.mem_cofinite.mp (Filter.le_principal_iff.mp hS)
    let T : Set (KPHilbert.Place F) := Sᶜ ∪ Sum.inr '' {q | KPAdelicCoverRestrictedProduct.Bad F q}
    have hT : T.Finite := hf.union ((KPAdelicCoverRestrictedProduct.bad_finite F).image Sum.inr)
    have heq (xy : RestrictedProduct (LocalD F) (fun v => (U F v : Set _)) (Filter.principal S) × RestrictedProduct (LocalD F) (fun v => (U F v : Set _)) (Filter.principal S)) :
        restrictedBeta F ζ hζ (RestrictedProduct.inclusion (LocalD F) (fun v => (U F v : Set _)) hS xy.1) (RestrictedProduct.inclusion (LocalD F) (fun v => (U F v : Set _)) hS xy.2) = ∏ v ∈ hT.toFinset, localPairing F ζ hζ v (xy.1 v) (xy.2 v) := by
      unfold restrictedBeta
      simp only [RestrictedProduct.inclusion_apply]
      apply finprod_eq_prod_of_mulSupport_subset
      intro v hv
      by_contra hn
      have hn' : v ∉ T := by simpa using hn
      have hvS : v ∈ S := by simpa [T] using (fun h => hn' (Or.inl h))
      cases v with
      | inl w =>
        letI := local_complex_trivial F w
        have h1 : xy.1 (Sum.inl w) = 1 := Subsingleton.elim _ _
        have h2 : xy.2 (Sum.inl w) = 1 := Subsingleton.elim _ _
        apply hv
        change localPairing F ζ hζ (Sum.inl w) (xy.1 (Sum.inl w)) (xy.2 (Sum.inl w)) = 1
        rw [h1, h2]
        rw [← map_one (localClass F (Sum.inl w))]
        rw [localPairing_representatives]
        exact map_one (KPHilbert.squareToThree F)
      | inr q =>
        apply hv
        apply tame_unit_isotropic F ζ hζ q
        · intro hbad
          exact hn' (Or.inr ⟨q, hbad, rfl⟩)
        · exact (Filter.mem_principal.mp xy.1.property) hvS
        · exact (Filter.mem_principal.mp xy.2.property) hvS
    change Continuous (fun xy : RestrictedProduct (LocalD F) (fun v => (U F v : Set _)) (Filter.principal S) × RestrictedProduct (LocalD F) (fun v => (U F v : Set _)) (Filter.principal S) => restrictedBeta F ζ hζ (RestrictedProduct.inclusion (LocalD F) (fun v => (U F v : Set _)) hS xy.1) (RestrictedProduct.inclusion (LocalD F) (fun v => (U F v : Set _)) hS xy.2))
    simp_rw [heq]
    apply continuous_finset_prod
    intro v hv
    exact (continuous_of_discreteTopology : Continuous (fun ab : LocalD F v × LocalD F v => localPairing F ζ hζ v ab.1 ab.2)).comp
      (((RestrictedProduct.continuous_eval v).comp continuous_fst).prodMk ((RestrictedProduct.continuous_eval v).comp continuous_snd))
  have hc' := hc.comp ((e.continuous.comp continuous_fst).prodMk (e.continuous.comp continuous_snd))
  change Continuous (fun xy : D F × D F => restrictedBeta F ζ hζ (e xy.1) (e xy.2)) at hc'
  simpa only [he, beta3] using hc'

private theorem localPairing_mul_left (v : KPHilbert.Place F) (x y z : LocalD F v) :
    localPairing F ζ hζ v (x * y) z =
      localPairing F ζ hζ v x z * localPairing F ζ hζ v y z := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    induction y using QuotientGroup.induction_on with
    | H y =>
      induction z using QuotientGroup.induction_on with
      | H z => exact (KPHilbert.B3_laws F ζ hζ v).1 x y z

private theorem localPairing_mul_right (v : KPHilbert.Place F) (x y z : LocalD F v) :
    localPairing F ζ hζ v x (y * z) =
      localPairing F ζ hζ v x y * localPairing F ζ hζ v x z := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    induction y using QuotientGroup.induction_on with
    | H y =>
      induction z using QuotientGroup.induction_on with
      | H z => exact (KPHilbert.B3_laws F ζ hζ v).2.1 x y z

private theorem localPairing_self (v : KPHilbert.Place F) (x : LocalD F v) :
    localPairing F ζ hζ v x x = 1 := by
  induction x using QuotientGroup.induction_on with
  | H x => exact ((KPHilbert.B3_laws F ζ hζ v).2.2.2.2.2 x).1

theorem beta3_bilinear :
    (∀ x y z : D F, beta3 F ζ hζ (x * y) z = beta3 F ζ hζ x z * beta3 F ζ hζ y z) ∧
    (∀ x y z : D F, beta3 F ζ hζ x (y * z) = beta3 F ζ hζ x y * beta3 F ζ hζ x z) ∧
    (∀ x : D F, beta3 F ζ hζ x x = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y z
    unfold beta3 restrictedBeta
    rw [map_mul]
    simp only [RestrictedProduct.mul_apply, localPairing_mul_left]
    exact finprod_mul_distrib
      (pairing_finiteSupport F ζ hζ _ _) (pairing_finiteSupport F ζ hζ _ _)
  · intro x y z
    unfold beta3 restrictedBeta
    rw [map_mul]
    simp only [RestrictedProduct.mul_apply, localPairing_mul_right]
    exact finprod_mul_distrib
      (pairing_finiteSupport F ζ hζ _ _) (pairing_finiteSupport F ζ hζ _ _)
  · intro x
    simp [beta3, restrictedBeta, localPairing_self]

private theorem localPairing_radical (v : KPHilbert.Place F) (a : LocalD F v)
    (ha : ∀ b, localPairing F ζ hζ v a b = 1) : a = 1 := by
  cases v with
  | inl w => letI := local_complex_trivial F w; exact Subsingleton.elim _ _
  | inr q =>
    induction a using QuotientGroup.induction_on with
    | H a =>
      change ClassFieldTheory.powerClass (q.adicCompletion F) 3 a = 1
      apply NormalizedSymbolTransport.inverseTransport_left_nondegenerate
        (KPHilbert.finiteRootsThree F ζ hζ q)
        (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F 3 (KPHilbert.rootsThree F ζ hζ) q)
        (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F 3
          (KPHilbert.rootsThree F ζ hζ) q).2.2.1.1
      intro b
      induction b using QuotientGroup.induction_on with
      | H b => exact (KPHilbert.B3_canonical F ζ hζ q a b).symm.trans (ha (localClass F (Sum.inr q) b))
private theorem localPairing_one_right (v : KPHilbert.Place F) (a : LocalD F v) :
    localPairing F ζ hζ v a 1 = 1 := by
  induction a using QuotientGroup.induction_on with
  | H a =>
    change KPHilbert.B3 F ζ hζ v a 1 = 1
    have h := (KPHilbert.B3_laws F ζ hζ v).2.1 a 1 1
    have h' : KPHilbert.B3 F ζ hζ v a 1 * KPHilbert.B3 F ζ hζ v a 1 = KPHilbert.B3 F ζ hζ v a 1 := by simpa using h.symm
    exact mul_eq_left.mp h'

private theorem ideleEval_supported (q : HeightOneSpectrum (𝓞 F)) (a : (q.adicCompletion F)ˣ) (v : KPHilbert.Place F) :
    ideleEval F v (IdeleGroup.ofAdicCompletion (𝓞 F) F q a) = Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) (Sum.inr q) a v := by
  apply Units.ext
  cases v with
  | inl w =>
    change (1 : w.Completion) = _
    simp
  | inr r =>
    change RestrictedProduct.mulSingle (fun w => w.adicCompletionIntegers F) q (a : q.adicCompletion F) r = _
    by_cases h : r = q
    · subst r
      simp [RestrictedProduct.mulSingle_eq_same]
    · simp [RestrictedProduct.mulSingle_eq_of_ne, h]

theorem beta3_radical_zero (x : D F) :
    (∀ y : D F, beta3 F ζ hζ x y = 1) ↔ x = 1 := by
  constructor
  · intro hx
    apply classComparison_injective F
    rw [map_one]
    ext v
    apply localPairing_radical F ζ hζ v
    cases v with
    | inl w =>
      intro b
      letI := local_complex_trivial F w
      rw [show b = 1 from Subsingleton.elim _ _]
      exact localPairing_one_right F ζ hζ _ _
    | inr q =>
      intro b
      induction b using QuotientGroup.induction_on with
      | H b =>
        let y := IdeleGroup.ofAdicCompletion (𝓞 F) F q b
        have hy := hx (QuotientGroup.mk' _ y)
        change restrictedBeta F ζ hζ (classComparison F x) (restrictedClassMap F y) = 1 at hy
        unfold restrictedBeta at hy
        rw [finprod_eq_single _ (Sum.inr q)] at hy
        · change localPairing F ζ hζ (Sum.inr q) (classComparison F x (Sum.inr q))
            (localClass F (Sum.inr q) (ideleEval F (Sum.inr q) y)) = 1 at hy
          rw [ideleEval_supported, Pi.mulSingle_eq_same] at hy
          exact hy
        · intro w hw
          change localPairing F ζ hζ w (classComparison F x w) (localClass F w (ideleEval F w y)) = 1
          rw [ideleEval_supported, Pi.mulSingle_eq_of_ne hw, map_one]
          exact localPairing_one_right F ζ hζ _ _
  · rintro rfl y
    have h := (beta3_bilinear F ζ hζ).1 1 1 y
    have h' : beta3 F ζ hζ 1 y * beta3 F ζ hζ 1 y = beta3 F ζ hζ 1 y := by simpa using h.symm
    exact mul_eq_left.mp h'

def diagonalMatrix (y : Ideles F) : KPAdelicCoverRestrictedProduct.AdelicGL2 F where
  val := !![(y : KPAdelicCoverRestrictedProduct.Adeles F), 0; 0, 1]
  inv := !![((y⁻¹ : Ideles F) : KPAdelicCoverRestrictedProduct.Adeles F), 0; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

def diagonalHom : Ideles F →* KPAdelicCoverRestrictedProduct.AdelicGL2 F where
  toFun := diagonalMatrix F
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalMatrix]
  map_mul' x y := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonalMatrix, Matrix.mul_apply, Fin.sum_univ_two]

def diagonalPGL : Ideles F →* KPAdelicCoverRestrictedProduct.AdelicPGL2 F :=
  (QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).comp (diagonalHom F)

def torusPullback : Subgroup
    (KPAdelicCoverRestrictedProduct.CubicPGL2Adelic F ζ hζ × Ideles F) :=
  MonoidHom.eqLocus
    ((KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).comp (MonoidHom.fst _ _))
    ((diagonalPGL F).comp (MonoidHom.snd _ _))

abbrev E := torusPullback F ζ hζ

def torusProjection : E F ζ hζ →* Ideles F :=
  (MonoidHom.snd _ _).comp (torusPullback F ζ hζ).subtype

theorem torusProjection_surjective : Function.Surjective (torusProjection F ζ hζ) := by
  intro y
  obtain ⟨x, hx⟩ := KPAdelicCoverRestrictedProduct.pglProjection_surjective F ζ hζ (diagonalPGL F y)
  exact ⟨⟨(x, y), hx⟩, rfl⟩

theorem torusCentral_mem (z : rootsOfUnity 3 F) :
    (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ z, 1) ∈
      torusPullback F ζ hζ := by
  change KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
    (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ z) = diagonalPGL F 1
  rw [map_one]
  have hz := KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel F ζ hζ
  change KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ z ∈
    (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).ker
  rw [← hz]
  exact ⟨z, rfl⟩

def torusCentralInjection : rootsOfUnity 3 F →* E F ζ hζ where
  toFun z := ⟨(KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ z, 1),
    torusCentral_mem F ζ hζ z⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

abbrev Z := Subgroup.center (E F ζ hζ)

theorem actual_torus_commutator (x y : E F ζ hζ) :
    x * y * x⁻¹ * y⁻¹ = torusCentralInjection F ζ hζ
      (beta3 F ζ hζ
        (QuotientGroup.mk' _ (torusProjection F ζ hζ x))
        (QuotientGroup.mk' _ (torusProjection F ζ hζ y)) ^ 4) := by
  exact DedekindZetaZeroFree.RepresentationTheory.KPGlobalCubicIdelePairingRaw.cover_torus_commutator F ζ hζ x y

def iotaThree : rootsOfUnity 3 F →* ℂˣ :=
  (KPLocalCover.coefficientEmbedding F ζ hζ).comp (KPLocalCover.threeToSix F)

private theorem roots_three_pow_four (z : rootsOfUnity 3 F) : z ^ 4 = z := by
  have hz : z ^ 3 = 1 := Subtype.ext z.property
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hz, pow_one, one_mul]

private theorem torusCentral_injective : Function.Injective (torusCentralInjection F ζ hζ) := by
  intro x y h
  exact KPAdelicCoverRestrictedProduct.pglCentralInjection_injective F ζ hζ
    (congrArg (fun e : E F ζ hζ => e.val.1) h)

private theorem iotaThree_injective : Function.Injective (iotaThree F ζ hζ) := by
  intro x y h
  have h' := KPLocalCover.coefficientEmbedding_injective F ζ hζ h
  exact Subtype.ext (congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ)) h')

theorem commutator_annihilators (x y : E F ζ hζ) :
    Commute x y ↔ beta3 F ζ hζ
      (QuotientGroup.mk' _ (torusProjection F ζ hζ x))
      (QuotientGroup.mk' _ (torusProjection F ζ hζ y)) = 1 := by
  rw [← commutatorElement_eq_one_iff_commute, commutatorElement_def,
    actual_torus_commutator, roots_three_pow_four]
  exact (torusCentral_injective F ζ hζ).eq_iff' (map_one _)

theorem coefficient_annihilators (x y : D F) :
    iotaThree F ζ hζ (beta3 F ζ hζ x y ^ 4) = 1 ↔ beta3 F ζ hζ x y = 1 := by
  rw [roots_three_pow_four]
  exact (iotaThree_injective F ζ hζ).eq_iff' (map_one _)

theorem torus_center : Z F ζ hζ =
    (CubicCharacters.cubes (Ideles F)).comap (torusProjection F ζ hζ) := by
  ext x
  change x ∈ Subgroup.center (E F ζ hζ) ↔
    torusProjection F ζ hζ x ∈ CubicCharacters.cubes (Ideles F)
  rw [← QuotientGroup.eq_one_iff (N := CubicCharacters.cubes (Ideles F))
    (torusProjection F ζ hζ x)]
  rw [← beta3_radical_zero F ζ hζ]
  constructor
  · intro hx d
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CubicCharacters.cubes (Ideles F)) d
    obtain ⟨y, rfl⟩ := torusProjection_surjective F ζ hζ y
    apply (commutator_annihilators F ζ hζ x y).mp
    exact (show Commute y x from (Subgroup.mem_center_iff.mp hx y)).symm
  · intro hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact ((commutator_annihilators F ζ hζ x y).mpr (hx _)).symm.eq

def AdmissibleS (S : Finset (KPHilbert.Place F)) : Prop :=
  (∀ w : InfinitePlace F, Sum.inl w ∈ S) ∧
  (∀ q : HeightOneSpectrum (𝓞 F), KPAdelicCoverRestrictedProduct.Bad F q → Sum.inr q ∈ S)

abbrev FiniteSClasses (S : Finset (KPHilbert.Place F)) :=
  (v : {v : KPHilbert.Place F // v ∈ S}) → LocalD F v.val

abbrev ExteriorValuations (S : Finset (KPHilbert.Place F)) :=
  Multiplicative ({v : KPHilbert.Place F // v ∉ S} →₀ ZMod 3)

@[instance_reducible] def exteriorValuationsTopology (S : Finset (KPHilbert.Place F)) :
    TopologicalSpace (ExteriorValuations F S) := ⊥

attribute [local instance] exteriorValuationsTopology

abbrev LocalValuationClasses (v : KPHilbert.Place F) := LocalD F v ⧸ U F v

theorem unitValuation_congr (q : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ KPAdelicCoverRestrictedProduct.Bad F q)
    (u : U F (Sum.inr q)) (a b : LocalD F (Sum.inr q))
    (hab : QuotientGroup.leftRel (U F (Sum.inr q)) a b) :
    localPairing F ζ hζ (Sum.inr q) u.val a =
      localPairing F ζ hζ (Sum.inr q) u.val b := by
  have hmul : a⁻¹ * b ∈ U F (Sum.inr q) := QuotientGroup.leftRel_apply.mp hab
  have hiso := tame_unit_isotropic F ζ hζ q hgood u.val _ u.property hmul
  have heq := localPairing_mul_right F ζ hζ (Sum.inr q) u.val a (a⁻¹ * b)
  simpa [hiso] using heq.symm

def unitValuationPairing (q : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ KPAdelicCoverRestrictedProduct.Bad F q)
    (u : U F (Sum.inr q)) (a : LocalValuationClasses F (Sum.inr q)) : rootsOfUnity 3 F :=
  Quotient.liftOn a (fun b => localPairing F ζ hζ (Sum.inr q) u.val b)
    (unitValuation_congr F ζ hζ q hgood u)

theorem tame_unit_valuation_perfect (q : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ KPAdelicCoverRestrictedProduct.Bad F q) :
    (∀ χ : LocalValuationClasses F (Sum.inr q) →* rootsOfUnity 3 F,
      ∃! u : U F (Sum.inr q), ∀ a,
        unitValuationPairing F ζ hζ q hgood u a = χ a) ∧
    (∀ χ : U F (Sum.inr q) →* rootsOfUnity 3 F,
      ∃! a : LocalValuationClasses F (Sum.inr q), ∀ u,
        unitValuationPairing F ζ hζ q hgood u a = χ u) := by
  exact DedekindZetaZeroFree.RepresentationTheory.KPGlobalCubicIdelePairingRaw.tame_arithmetic_unit_valuation_duality F ζ hζ q hgood

end
end DedekindZetaZeroFree.KPGlobalCubicIdelePairing

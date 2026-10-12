module

public import DedekindZetaZeroFree.Metaplectic.Weil.OddLocalQuadraticPhase
public import DedekindZetaZeroFree.Metaplectic.Weil.PhaseSigns
public import DedekindZetaZeroFree.Arithmetic.LocalFields.SexticHilbertPairing
public import DedekindZetaZeroFree.LFunctions.Tate.Local.AnnularFourierMellin
public import DedekindZetaZeroFree.Arithmetic.LocalFields.HilbertSymbolCompletionNaturality

@[expose] public section

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
open scoped NumberField Classical WithZero
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.OddEvaluation
noncomputable section
variable {F : Type} [Field F] [NumberField F]
attribute [local instance] residueFintype
private theorem raw_presentation (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π)
    (x : (v.adicCompletion F)ˣ) :
    ∃ (n : ℤ) (u : (v.adicCompletionIntegers F)ˣ),
      x = localUnit v u * uniformizer v π hπ ^ n := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ x.ne_zero
  refine ⟨n,u, Units.ext ?_⟩
  simpa [Algebra.smul_def, Units.smul_def] using hu
private theorem conductor_exists (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) :
    ∃ c : ℤ, conductor v π hπ c := by
  have hn : ∃ x : v.adicCompletion F, ResidueTrace.localTraceCharacter v x ≠ 1 := by
    letI := (ResidueTrace.baseEmbedding v).toAlgebra
    letI := ResidueTrace.localTrace_finite v
    obtain ⟨x, hx⟩ := Algebra.trace_surjective ℚ_[ResidueTrace.rationalPrimeBelow v]
      (v.adicCompletion F)
      (((ResidueTrace.rationalPrimeBelow v).1 : ℚ)⁻¹ : ℚ_[ResidueTrace.rationalPrimeBelow v])
    refine ⟨x, ?_⟩
    change rationalPadicCharacter (ResidueTrace.rationalPrimeBelow v)
      (Algebra.trace ℚ_[ResidueTrace.rationalPrimeBelow v] (v.adicCompletion F) x) ≠ 1
    rw [hx]
    exact rationalPadicCharacter_inv_prime_ne_one _
  obtain ⟨a, ha, hc⟩ := TateFiniteShell.exists_conductorZero_rescaling F v
    (ResidueTrace.localTraceCharacter v) (ResidueTrace.continuous_localTraceCharacter v) hn
  obtain ⟨c, u, hu⟩ := raw_presentation v π hπ (Units.mk0 a ha)
  have hva : a = (localUnit v u : v.adicCompletion F) *
      ((uniformizer v π hπ ^ c : (v.adicCompletion F)ˣ) : v.adicCompletion F) :=
    congrArg Units.val hu
  have htriv : ∀ x : v.adicCompletionIntegers F,
      ResidueTrace.localTraceCharacter v
        (((uniformizer v π hπ ^ c : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) = 1 := by
    intro x
    have hh := (hc 1).mpr (by change Valued.v (1 : v.adicCompletion F) ≤ 1; simp)
    have hmem : (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) * x : v.adicCompletionIntegers F) : v.adicCompletion F) ∈
        finiteCompletionBall F v 0 := by
      change Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) * x : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1
      exact (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) * x : v.adicCompletionIntegers F)).property
    have he := hh _ hmem
    change ResidueTrace.localTraceCharacter v (a * _) = 1 at he
    rw [hva] at he
    convert he using 2
    change ↑(uniformizer v π hπ ^ c) * ↑x =
      (↑↑u : v.adicCompletion F) * ↑(uniformizer v π hπ ^ c) * (((↑↑u⁻¹ : v.adicCompletion F) * ↑x) * 1)
    have huinv : (↑↑u : v.adicCompletion F) * (↑↑u⁻¹ : v.adicCompletion F) = 1 :=
      congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) (by simp : (u : v.adicCompletionIntegers F) * ↑u⁻¹ = 1)
    linear_combination -(↑(uniformizer v π hπ ^ c) * ↑x) * (huinv)
  refine ⟨c,htriv,?_⟩
  have hpi : (π : v.adicCompletion F) ≠ 0 := by intro h; exact hπ.ne_zero (Subtype.ext h)
  have hlt : Valued.v (π : v.adicCompletion F) < 1 :=
    (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).valuation_irreducible_lt_one hπ
  have hinv : (π : v.adicCompletion F)⁻¹ ∉ finiteCompletionBall F v 0 := by
    change ¬ Valued.v (π : v.adicCompletion F)⁻¹ ≤ 1
    rw [map_inv₀, inv_le_one₀ (by exact lt_of_le_of_ne zero_le (Ne.symm ((Valuation.ne_zero_iff _).mpr hpi)))]
    exact not_le.mpr hlt
  have hh := mt (hc (π : v.adicCompletion F)⁻¹).mp hinv
  push Not at hh
  obtain ⟨x, hx, he⟩ := hh
  let y : v.adicCompletionIntegers F := ⟨x, hx⟩
  refine ⟨u * y, ?_⟩
  simpa [TateFiniteShell.rescaledCharacter, AddChar.mulShift_apply, hva, zpow_sub,
    mul_assoc, mul_left_comm, mul_comm, y, uniformizer] using he

local instance (v : HeightOneSpectrum (𝓞 F)) : ValuativeRel (v.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F v
local instance (v : HeightOneSpectrum (𝓞 F)) : IsNonarchimedeanLocalField (v.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v
 theorem ints_eq (v : HeightOneSpectrum (𝓞 F)) :
    (ValuativeRel.valuation (v.adicCompletion F)).integer = (v.adicCompletionIntegers F).toSubring := by
  letI : (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).Compatible := Valuation.Compatible.ofValuation _
  ext x
  change ValuativeRel.valuation (v.adicCompletion F) x ≤ 1 ↔ Valued.v x ≤ 1
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion F)) (Valued.v)).le_one_iff_le_one
 def intEquiv (v : HeightOneSpectrum (𝓞 F)) :
    (ValuativeRel.valuation (v.adicCompletion F)).integer ≃+* v.adicCompletionIntegers F :=
  RingEquiv.subringCongr (ints_eq v)
private theorem tame_two (v : HeightOneSpectrum (𝓞 F)) (hodd : ringChar (Residue v) ≠ 2) :
    ValuativeRel.valuation (v.adicCompletion F) (2 : v.adicCompletion F) = 1 := by
  have hu : IsUnit (2 : v.adicCompletionIntegers F) := by
    apply isUnit_of_map_unit (IsLocalRing.residue (v.adicCompletionIntegers F))
    rw [map_ofNat]
    exact isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime (Residue v) Nat.prime_two hodd)
  have hu' : IsUnit (2 : (ValuativeRel.valuation (v.adicCompletion F)).integer) := by
    simpa only [map_ofNat] using hu.map (intEquiv v).symm.toRingHom
  exact (Valuation.integer.integers (ValuativeRel.valuation (v.adicCompletion F))).isUnit_iff_valuation_eq_one.mp hu'
private theorem tame_symbol_one_iff (v : HeightOneSpectrum (𝓞 F))
    (hodd : ringChar (Residue v) ≠ 2)
    (hm : (primitiveRoots 2 (v.adicCompletion F)).Nonempty)
    (u : (v.adicCompletionIntegers F)ˣ) :
    LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol (v.adicCompletion F) 2
      (tame_two v hodd) hm (Units.map (intEquiv v).symm.toRingHom.toMonoidHom u) = 1 ↔
      IsSquare (IsLocalRing.residue _ (u : v.adicCompletionIntegers F)) := by
  let u' := Units.map (intEquiv v).symm.toRingHom.toMonoidHom u
  letI : Fintype (IsLocalRing.ResidueField (ValuativeRel.valuation (v.adicCompletion F)).integer) := Fintype.ofFinite _
  rw [← (LocalClassFieldTheory.Kummer.localNthRootsReductionEquiv (v.adicCompletion F) 2 (tame_two v hodd) hm).map_eq_one_iff,
    LocalClassFieldTheory.Kummer.localNthRootsReductionEquiv_localTamePowerResidueSymbol (v.adicCompletion F) 2 (tame_two v hodd) hm,
    ]
  erw [AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol_eq_one_iff]
  have he : ∀ (a : IsLocalRing.ResidueField (ValuativeRel.valuation (v.adicCompletion F)).integer),
      IsSquare a ↔ IsSquare ((IsLocalRing.ResidueField.mapEquiv (intEquiv v)) a) := by
    intro a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨(IsLocalRing.ResidueField.mapEquiv (intEquiv v)) b, by simp⟩
    · rintro ⟨b, hb⟩
      refine ⟨(IsLocalRing.ResidueField.mapEquiv (intEquiv v)).symm b, ?_⟩
      apply (IsLocalRing.ResidueField.mapEquiv (intEquiv v)).injective
      simpa using hb
  letI : IsLocalHom (intEquiv v).toRingHom := IsLocalHom.of_surjective _ (intEquiv v).surjective
  have hred : (IsLocalRing.ResidueField.mapEquiv (intEquiv v))
      (↑(LocalFieldTheory.residueUnitsConcreteEquiv (v.adicCompletion F) (LocalFieldTheory.integerUnitsToResidueUnits (v.adicCompletion F) u')) :
        IsLocalRing.ResidueField (ValuativeRel.valuation (v.adicCompletion F)).integer) =
      IsLocalRing.residue _ (u : v.adicCompletionIntegers F) := by
    change IsLocalRing.ResidueField.map (intEquiv v).toRingHom
      (IsLocalRing.residue _ ((intEquiv v).symm (u : v.adicCompletionIntegers F))) = _
    rw [IsLocalRing.ResidueField.map_residue]
    simp
  rw [← hred, ← he]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨(b : _), by simpa [pow_two, u'] using congrArg Units.val hb.symm⟩
  · rintro ⟨b, hb⟩
    have hb0 : b ≠ 0 := by
      intro hz
      simp [hz] at hb
      exact (LocalFieldTheory.integerUnitsToResidueUnits (v.adicCompletion F) u').ne_zero hb
    refine ⟨Units.mk0 b hb0, Units.ext ?_⟩
    simpa [pow_two, u'] using hb.symm

 def signHom (K : Type*) [Field K] : rootsOfUnity 2 K →* ℂ where
  toFun z := if z = 1 then 1 else -1
  map_one' := by simp
  map_mul' z w := by
    by_cases hz : z = 1
    · simp [hz]
    by_cases hw : w = 1
    · simp [hw]
    have root_neg (t : rootsOfUnity 2 K) (ht : t ≠ 1) : ((t : Kˣ) : K) = -1 := by
      have hp : (((t : Kˣ) : K)) ^ 2 = 1 := congrArg Units.val t.property
      rcases sq_eq_one_iff.mp hp with hp | hp
      · exact False.elim (ht (Subtype.ext (Units.ext hp)))
      · exact hp
    have hzw : z*w=1 := Subtype.ext (Units.ext (by
      change (((z : Kˣ) : K) * ((w : Kˣ) : K)) = 1
      rw [root_neg z hz, root_neg w hw]; simp))
    simp [hz,hw,hzw]
private theorem sign_equiv {K L : Type*} [Field K] [Field L]
    (e : rootsOfUnity 2 K ≃* rootsOfUnity 2 L) (z : rootsOfUnity 2 K) :
    signHom L (e z) = signHom K z := by
  simp only [signHom, MonoidHom.coe_mk, OneHom.coe_mk, e.map_eq_one_iff]
private theorem sign_tame (v : HeightOneSpectrum (𝓞 F)) (hodd : ringChar (Residue v) ≠ 2)
    (hm : (primitiveRoots 2 (v.adicCompletion F)).Nonempty)
    (u : (v.adicCompletionIntegers F)ˣ) :
    signHom (v.adicCompletion F)
      (KummerTheory.nthRootsSubgroupEquivRootsOfUnity (v.adicCompletion F) 2
        (LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol (v.adicCompletion F) 2
          (tame_two v hodd) hm (Units.map (intEquiv v).symm.toRingHom.toMonoidHom u))) =
    quadratic v (IsLocalRing.residue _ (u : v.adicCompletionIntegers F)) := by
  letI := residueFintype v
  have hn : IsLocalRing.residue _ (u : v.adicCompletionIntegers F) ≠ 0 :=
    (u.isUnit.map (IsLocalRing.residue _)).ne_zero
  have hs := tame_symbol_one_iff v hodd hm u
  have hq := quadraticChar_dichotomy hn
  have hqi := quadraticChar_one_iff_isSquare hn
  simp only [signHom, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.map_eq_one_iff]
  split_ifs with h
  · have h := (KummerTheory.nthRootsSubgroupEquivRootsOfUnity (v.adicCompletion F) 2).map_eq_one_iff.mp h
    have h := hs.mp h
    simp [quadratic, hqi.mpr h]
  · have hnq : quadraticChar (Residue v) (IsLocalRing.residue _ (u : v.adicCompletionIntegers F)) = -1 :=
      hq.resolve_left (fun hq => h ((KummerTheory.nthRootsSubgroupEquivRootsOfUnity (v.adicCompletion F) 2).map_eq_one_iff.mpr (hs.mpr (hqi.mp hq))))
    simp [quadratic, hnq]
private theorem sign_actual_unit (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hodd : ringChar (Residue v) ≠ 2)
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π)
    (u : (v.adicCompletionIntegers F)ˣ) :
    signHom F (A.actualLocalSymbol v 2 (Or.inl rfl) (localUnit v u) (uniformizer v π hπ)) =
      quadratic v (IsLocalRing.residue _ (u : v.adicCompletionIntegers F)) := by
  let K := v.adicCompletion F
  letI := residueFintype v
  have hm : (primitiveRoots 2 K).Nonempty :=
    ⟨_, (mem_primitiveRoots (by decide)).mpr (A.finite_primitive_root v 2 (Or.inl rfl))⟩
  have hh := A.actualLocalHilbert_local_value v 2 (Or.inl rfl)
    (ClassFieldTheory.powerClass K 2 (localUnit v u))
    (ClassFieldTheory.powerClass K 2 (uniformizer v π hπ))
  change A.finiteRootsEquiv v 2 (Or.inl rfl) (A.actualLocalSymbol v 2 (Or.inl rfl) _ _) = _ at hh
  change _ = (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F 2
    (A.actualHilbert_roots 2 (Or.inl rfl)) v _ _)⁻¹ at hh
  rw [RepresentationTheory.KPHilbertNormalization.LocalComparison.finite_family_eq_local F v 2 _ hm,
    ] at hh
  erw [ClassFieldTheory.localHilbertPairing_powerClass] at hh
  let u' := Units.map (intEquiv v).symm.toRingHom.toMonoidHom u
  have hu : LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits K u' = localUnit v u := Units.ext rfl
  have hval : LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul (uniformizer v π hπ)) = -1 := by
    have hi : Irreducible ((intEquiv v).symm π) := (MulEquiv.irreducible_iff (intEquiv v).symm.toMulEquiv).mpr hπ
    exact LocalFieldTheory.v_integerRingIrreducibleFieldUnit K
      ((intEquiv v).symm π) hi (uniformizer v π hπ) rfl
  rw [← hu] at hh
  unfold ClassFieldTheory.localHilbertSymbol at hh
  erw [LocalClassFieldTheory.Kummer.localHilbertSymbol_tame_formula K 2 (tame_two v hodd) hm u', hval] at hh
  simp only [neg_neg, zpow_one] at hh
  have hh' := congrArg (signHom K) hh
  erw [sign_equiv, map_inv] at hh'
  have ht := sign_tame v hodd hm u
  change _ = (signHom (v.adicCompletion F) _)⁻¹ at hh'
  erw [ht] at hh'
  have hq : quadratic v (IsLocalRing.residue _ (u : v.adicCompletionIntegers F)) ^ 2 = 1 := by
    exact_mod_cast quadraticChar_sq_one ((u.isUnit.map (IsLocalRing.residue _)).ne_zero)
  rw [inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hq)] at hh'
  simpa only [hu] using hh'

private theorem actual_integral_integral (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hodd : ringChar (Residue v) ≠ 2)
    (u w : (v.adicCompletionIntegers F)ˣ) :
    A.actualLocalSymbol v 2 (Or.inl rfl) (localUnit v u) (localUnit v w) = 1 := by
  let K := v.adicCompletion F
  have hm : (primitiveRoots 2 K).Nonempty :=
    ⟨_, (mem_primitiveRoots (by decide)).mpr (A.finite_primitive_root v 2 (Or.inl rfl))⟩
  apply (A.finiteRootsEquiv v 2 (Or.inl rfl)).injective
  erw [map_one]
  have hh := A.actualLocalHilbert_local_value v 2 (Or.inl rfl)
    (ClassFieldTheory.powerClass K 2 (localUnit v u))
    (ClassFieldTheory.powerClass K 2 (localUnit v w))
  change A.finiteRootsEquiv v 2 (Or.inl rfl) (A.actualLocalSymbol v 2 (Or.inl rfl) _ _) = _ at hh
  change _ = (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F 2
    (A.actualHilbert_roots 2 (Or.inl rfl)) v _ _)⁻¹ at hh
  rw [RepresentationTheory.KPHilbertNormalization.LocalComparison.finite_family_eq_local F v 2 _ hm] at hh
  erw [ClassFieldTheory.localHilbertPairing_powerClass] at hh
  let u' := Units.map (intEquiv v).symm.toRingHom.toMonoidHom u
  let w' := Units.map (intEquiv v).symm.toRingHom.toMonoidHom w
  have hu : LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits K u' = localUnit v u := Units.ext rfl
  have hw : LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits K w' = localUnit v w := Units.ext rfl
  rw [← hu, ← hw] at hh
  unfold ClassFieldTheory.localHilbertSymbol at hh
  erw [LocalClassFieldTheory.Kummer.localHilbertSymbol_integerUnit_integerUnit_eq_one K 2 (tame_two v hodd) hm u' w', map_one, inv_one] at hh
  exact hh
private theorem actual_alternating (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) :
    A.actualLocalSymbol v 2 (Or.inl rfl) a a = 1 := by
  let K := v.adicCompletion F
  have hm : (primitiveRoots 2 K).Nonempty :=
    ⟨_, (mem_primitiveRoots (by decide)).mpr (A.finite_primitive_root v 2 (Or.inl rfl))⟩
  obtain ⟨r, hr⟩ := A.finite_neg_one_isPower v 2 (Or.inl rfl)
  have hr0 : r ≠ 0 := by intro hz; simp [hz] at hr
  let ru : Kˣ := Units.mk0 r hr0
  have hru : ru ^ (2 : ℕ) = -1 := Units.ext (by simpa [ru] using hr)
  have hneg : ClassFieldTheory.powerClass K 2 (-1) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨ru, hru⟩
  have hclass : ClassFieldTheory.powerClass K 2 (-a) = ClassFieldTheory.powerClass K 2 a := by
    rw [show -a = (-1)*a by simp]
    change QuotientGroup.mk' _ ((-1)*a) = _
    rw [map_mul]
    change ClassFieldTheory.powerClass K 2 (-1) * _ = _
    rw [hneg]
    exact one_mul _
  apply (A.finiteRootsEquiv v 2 (Or.inl rfl)).injective
  erw [map_one]
  have hh := A.actualLocalHilbert_local_value v 2 (Or.inl rfl)
    (ClassFieldTheory.powerClass K 2 a) (ClassFieldTheory.powerClass K 2 a)
  change A.finiteRootsEquiv v 2 (Or.inl rfl) (A.actualLocalSymbol v 2 (Or.inl rfl) _ _) = _ at hh
  change _ = (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F 2
    (A.actualHilbert_roots 2 (Or.inl rfl)) v _ _)⁻¹ at hh
  rw [RepresentationTheory.KPHilbertNormalization.LocalComparison.finite_family_eq_local F v 2 _ hm] at hh
  nth_rw 2 [← hclass] at hh
  erw [ClassFieldTheory.localHilbertPairing_powerClass] at hh
  unfold ClassFieldTheory.localHilbertSymbol at hh
  erw [LocalClassFieldTheory.Kummer.localHilbertSymbol_neg_self, map_one, inv_one] at hh
  exact hh
 def signedPair (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ →* ℂ :=
  (MonoidHom.compHom (signHom F)).comp
    ((A.actualLocalHilbert v 2 (Or.inl rfl)).comp (ClassFieldTheory.powerClass _ 2)) |>.flip |>.comp
      (ClassFieldTheory.powerClass _ 2) |>.flip

private theorem signedPair_apply (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (a b : (v.adicCompletion F)ˣ) :
    signedPair A v a b = signHom F (A.actualLocalSymbol v 2 (Or.inl rfl) a b) := rfl
private theorem sign_sq (K : Type*) [Field K] (z : rootsOfUnity 2 K) : signHom K z ^ 2 = 1 := by
  simp only [signHom, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs <;> norm_num
private theorem even_zpow (x : ℂ) (hx : x^2=1) (n : ℤ) :
    x ^ n = if Even n then 1 else x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  by_cases hn : Even n
  · obtain ⟨k, hk⟩ := hn
    rw [if_pos (by exact ⟨k,hk⟩), hk, ← two_mul, zpow_mul, zpow_ofNat, hx, one_zpow]
  · rw [if_neg hn]
    obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hn
    rw [hk, zpow_add₀ hx0, zpow_mul, zpow_ofNat, hx, one_zpow, zpow_one, one_mul]
private theorem signed_formula (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (hodd : ringChar (Residue v) ≠ 2)
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π)
    (u w : (v.adicCompletionIntegers F)ˣ) (n m : ℤ) :
    signHom F (A.actualLocalSymbol v 2 (Or.inl rfl)
      (localUnit v u * uniformizer v π hπ ^ n)
      (localUnit v w * uniformizer v π hπ ^ m)) =
      (if Even m then 1 else quadratic v (IsLocalRing.residue _ (u : v.adicCompletionIntegers F))) *
      (if Even n then 1 else quadratic v (IsLocalRing.residue _ (w : v.adicCompletionIntegers F))) := by
  let B := signedPair A v
  change B _ _ = _
  simp only [map_mul, MonoidHom.mul_apply, map_zpow, MonoidHom.zpow_apply]
  have huu : B (localUnit v u) (localUnit v w) = 1 := by
    rw [signedPair_apply,actual_integral_integral A v hodd]
    exact map_one _
  have hpp : B (uniformizer v π hπ) (uniformizer v π hπ) = 1 := by
    rw [signedPair_apply,actual_alternating]
    exact map_one _
  have hup : B (localUnit v u) (uniformizer v π hπ) = quadratic v (IsLocalRing.residue _ (u : v.adicCompletionIntegers F)) :=
    sign_actual_unit A v hodd π hπ u
  have hpw : B (uniformizer v π hπ) (localUnit v w) = quadratic v (IsLocalRing.residue _ (w : v.adicCompletionIntegers F)) := by
    rw [signedPair_apply]
    have hh := A.actualLocalHilbert_skew v 2 (Or.inl rfl)
      (ClassFieldTheory.powerClass _ 2 (uniformizer v π hπ)) (ClassFieldTheory.powerClass _ 2 (localUnit v w))
    change A.actualLocalSymbol v 2 (Or.inl rfl) _ _ = (A.actualLocalSymbol v 2 (Or.inl rfl) _ _)⁻¹ at hh
    rw [hh]
    erw [map_inv,sign_actual_unit A v hodd π hπ w]
    have hh := sign_sq F (A.actualLocalSymbol v 2 (Or.inl rfl) (localUnit v w) (uniformizer v π hπ))
    rw [sign_actual_unit A v hodd π hπ w] at hh
    exact inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hh)
  have hz (y : (v.adicCompletion F)ˣ) : B (uniformizer v π hπ ^ n) y = B (uniformizer v π hπ) y ^ n :=
    by
      change B.flip y (uniformizer v π hπ ^ n) = (B.flip y (uniformizer v π hπ)) ^ n
      exact map_zpow (B.flip y) _ _
  rw [hz,hz]
  rw [huu,hpp,hup,hpw,one_zpow,one_mul,mul_one]
  have hqu := sign_sq F (A.actualLocalSymbol v 2 (Or.inl rfl) (localUnit v u) (uniformizer v π hπ))
  have hqw := sign_sq F (A.actualLocalSymbol v 2 (Or.inl rfl) (localUnit v w) (uniformizer v π hπ))
  rw [sign_actual_unit A v hodd π hπ u] at hqu
  rw [sign_actual_unit A v hodd π hπ w] at hqw
  rw [even_zpow _ hqu,even_zpow _ hqw]
  exact mul_comm _ _

private theorem parity_identity (r s e : ℂ) (hr : r^2=1) (hs : s^2=1) (he : e^2=1)
    (n m c : ℤ) :
    ((if Even (n-c) then 1 else r*e) / (if Even (-c) then 1 else e)) *
    ((if Even (m-c) then 1 else s*e) / (if Even (-c) then 1 else e)) =
    ((if Even m then 1 else r) * (if Even n then 1 else s)) *
    ((if Even (n+m-c) then 1 else (r*s)*e) / (if Even (-c) then 1 else e)) := by
  have he0 : e ≠ 0 := by intro h; simp [h] at he
  have hh : ∀ i : ℤ, Even i ↔ i % 2 = 0 := fun _ => Int.even_iff
  simp only [hh]
  split_ifs <;> try omega
  all_goals field_simp
  all_goals simp_all [pow_two]
  all_goals linear_combination (r*s)*he + e*(r*s)*hr + e*r*hs
attribute [local instance] residueFintype

theorem hilbert_defect_of_parity_evaluation (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hodd : ringChar (Residue v) ≠ 2)
    (hg : ∀ (π : v.adicCompletionIntegers F) (hπ : Irreducible π)
      (c : ℤ), conductor v π hπ c →
      ∀ (u : (v.adicCompletionIntegers F)ˣ) (n : ℤ),
        A.finiteGamma v (localUnit v u * uniformizer v π hπ ^ n) =
          if Even (n-c) then 1 else
            quadratic v (IsLocalRing.residue _ (u : v.adicCompletionIntegers F)) *
              epsilon v π hπ c)
    (he : ∀ (π : v.adicCompletionIntegers F) (hπ : Irreducible π)
      (c : ℤ), conductor v π hπ c → epsilon v π hπ c ^ 2 = 1)
    (a b : (v.adicCompletion F)ˣ) :
    A.finiteWeilPhase v a * A.finiteWeilPhase v b =
      (if A.actualLocalSymbol v 2 (Or.inl rfl) a b = 1 then (1 : ℂ) else -1) *
        A.finiteWeilPhase v (a*b) := by
  letI := residueFintype v
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  obtain ⟨c,hc⟩ := conductor_exists v π hπ
  obtain ⟨n,u,ha⟩ := raw_presentation v π hπ a
  obtain ⟨m,w,hb⟩ := raw_presentation v π hπ b
  rw [ha,hb]
  have hab : (localUnit v u * uniformizer v π hπ ^ n) *
      (localUnit v w * uniformizer v π hπ ^ m) =
      localUnit v (u*w) * uniformizer v π hπ ^ (n+m) := by
    rw [map_mul,zpow_add]
    ac_rfl
  change _ = signHom F (A.actualLocalSymbol v 2 (Or.inl rfl) _ _) * _
  rw [signed_formula A v hodd π hπ u w n m,hab]
  have hone : (1 : (v.adicCompletion F)ˣ) = localUnit v 1 * uniformizer v π hπ ^ (0:ℤ) := by simp
  unfold SArithmeticData.finiteWeilPhase
  rw [hg π hπ c hc u n,hg π hπ c hc w m,hg π hπ c hc (u*w) (n+m),hone,
      hg π hπ c hc 1 0]
  simp only [Int.zero_sub, Units.val_one, map_one, quadratic, map_mul, Units.val_mul,
    Int.cast_mul, Int.cast_one, one_mul]
  have hu : (quadraticChar (Residue v) (IsLocalRing.residue _ (u : v.adicCompletionIntegers F)) : ℂ) ^ 2 = 1 := by
    exact_mod_cast quadraticChar_sq_one ((u.isUnit.map (IsLocalRing.residue _)).ne_zero)
  have hw : (quadraticChar (Residue v) (IsLocalRing.residue _ (w : v.adicCompletionIntegers F)) : ℂ) ^ 2 = 1 := by
    exact_mod_cast quadraticChar_sq_one ((w.isUnit.map (IsLocalRing.residue _)).ne_zero)
  exact parity_identity _ _ _ hu hw (he π hπ c hc) n m c

end
end DedekindZetaZeroFree.OddEvaluation

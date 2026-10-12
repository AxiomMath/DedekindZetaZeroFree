module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Hilbert.HilbertSymbolSpecification
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Hilbert.SexticHilbertNormalization
public import DedekindZetaZeroFree.Adeles.Approximation.SIntegerFiniteStrongApproximation

@[expose] public section

open scoped NumberField Classical ValuativeRel
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PalomarHilbert

noncomputable section
set_option autoImplicit false

section LocalAlgebra

variable {A C U : Type*} [CommGroup A] [CommGroup C]

theorem multiplicative_one (f : A → C)
    (hf : ∀ a b : A, f (a * b) = f a * f b) : f 1 = 1 := by
  have h : f 1 * 1 = f 1 * f 1 := by
    simpa only [mul_one, one_mul] using hf 1 1
  exact (mul_left_cancel h).symm

def leftHom (H : A → A → C)
    (hl : ∀ a b c : A, H (a * b) c = H a c * H b c) (b : A) : A →* C where
  toFun a := H a b
  map_one' := multiplicative_one (fun a => H a b) (fun a a' => hl a a' b)
  map_mul' a a' := hl a a' b

def rightHom (H : A → A → C)
    (hr : ∀ a b c : A, H a (b * c) = H a b * H a c) (a : A) : A →* C where
  toFun b := H a b
  map_one' := multiplicative_one (H a) (hr a)
  map_mul' b b' := hr a b b'

theorem skew_of_alternating (H : A → A → C)
    (hl : ∀ a b c : A, H (a * b) c = H a c * H b c)
    (hr : ∀ a b c : A, H a (b * c) = H a b * H a c)
    (ha : ∀ a : A, H a a = 1) (a b : A) : H a b = (H b a)⁻¹ := by
  have h : H a b * H b a = 1 := by
    simpa only [hl, hr, ha a, ha b, one_mul, mul_one] using ha (a * b)
  exact eq_inv_iff_mul_eq_one.mpr h

theorem pairing_decomposition (H : A → A → C)
    (hl : ∀ a b c : A, H (a * b) c = H a c * H b c)
    (hr : ∀ a b c : A, H a (b * c) = H a b * H a c)
    (ha : ∀ a : A, H a a = 1)
    (π u v : A) (n m : ℤ) (huv : H u v = 1) :
    H (π ^ n * u) (π ^ m * v) = H π v ^ n * (H π u ^ m)⁻¹ := by
  have hleftpow (a b : A) (k : ℤ) : H (a ^ k) b = H a b ^ k :=
    (leftHom H hl b).map_zpow a k
  have hrightpow (a b : A) (k : ℤ) : H a (b ^ k) = H a b ^ k :=
    (rightHom H hr a).map_zpow b k
  have hswap : H u π = (H π u)⁻¹ := skew_of_alternating H hl hr ha u π
  simp only [hl, hr, hleftpow, hrightpow, ha π, huv, hswap,
    one_zpow, one_mul, mul_one, inv_zpow]

theorem eq_of_uniformizer_decomposition (H J : A → A → C)
    (hHleft : ∀ a b c : A, H (a * b) c = H a c * H b c)
    (hHright : ∀ a b c : A, H a (b * c) = H a b * H a c)
    (hHalt : ∀ a : A, H a a = 1)
    (hJleft : ∀ a b c : A, J (a * b) c = J a c * J b c)
    (hJright : ∀ a b c : A, J a (b * c) = J a b * J a c)
    (hJalt : ∀ a : A, J a a = 1)
    (π : A) (ι : U → A)
    (hdecomp : ∀ a : A, ∃ n : ℤ, ∃ u : U, a = π ^ n * ι u)
    (hHunit : ∀ u v : U, H (ι u) (ι v) = 1)
    (hJunit : ∀ u v : U, J (ι u) (ι v) = 1)
    (hnorm : ∀ u : U, H π (ι u) = J π (ι u)) : H = J := by
  funext a b
  obtain ⟨n, u, rfl⟩ := hdecomp a
  obtain ⟨m, v, rfl⟩ := hdecomp b
  rw [pairing_decomposition H hHleft hHright hHalt π (ι u) (ι v) n m
      (hHunit u v),
    pairing_decomposition J hJleft hJright hJalt π (ι u) (ι v) n m
      (hJunit u v),
    hnorm u, hnorm v]

end LocalAlgebra

section ActualFamily

variable (F : Type) [Field F] [NumberField F]

local instance (v : FinitePlace F) : ValuativeRel (v.adicCompletion F) :=
  completionRelation F v

local instance (v : FinitePlace F) : IsNonarchimedeanLocalField (v.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v

def actualFamily (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : Family F :=
  fun v a b => KPHilbert.B6 F ζ hζ (Sum.inr v) a b

theorem actualFamily_continuous (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (v : FinitePlace F) :
    letI : TopologicalSpace (rootsOfUnity 6 F) := ⊥
    Continuous (fun ab : (v.adicCompletion F)ˣ × (v.adicCompletion F)ˣ =>
      actualFamily F ζ hζ v ab.1 ab.2) := by
  exact KPHilbert.B6_continuous F ζ hζ (Sum.inr v)

theorem actualFamily_laws (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    (∀ (v : FinitePlace F) (a b c : (v.adicCompletion F)ˣ),
      actualFamily F ζ hζ v (a * b) c =
        actualFamily F ζ hζ v a c * actualFamily F ζ hζ v b c) ∧
    (∀ (v : FinitePlace F) (a b c : (v.adicCompletion F)ˣ),
      actualFamily F ζ hζ v a (b * c) =
        actualFamily F ζ hζ v a b * actualFamily F ζ hζ v a c) ∧
    ∀ (v : FinitePlace F) (a : (v.adicCompletion F)ˣ),
      actualFamily F ζ hζ v a a = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro v a b c
    exact (KPHilbert.B6_laws F ζ hζ (Sum.inr v)).1 a b c
  · intro v a b c
    exact (KPHilbert.B6_laws F ζ hζ (Sum.inr v)).2.1 a b c
  · intro v a
    exact ((KPHilbert.B6_laws F ζ hζ (Sum.inr v)).2.2.2.2.2 a).1

theorem actualFamily_productFormula (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (a b : Fˣ) :
    Function.HasFiniteMulSupport (fun v =>
      actualFamily F ζ hζ v (diagonal F v a) (diagonal F v b)) ∧
    (∏ᶠ v, actualFamily F ζ hζ v (diagonal F v a) (diagonal F v b)) = 1 := by
  let f : KPHilbert.Place F → rootsOfUnity 6 F := fun p =>
    KPHilbert.B6 F ζ hζ p (KPHilbert.diagonal F p a) (KPHilbert.diagonal F p b)
  obtain ⟨hf, hp⟩ := KPHilbert.B6_productFormula F ζ hζ a b
  have hfinite : Function.HasFiniteMulSupport (fun v : FinitePlace F =>
      actualFamily F ζ hζ v (diagonal F v a) (diagonal F v b)) := by
    change ((Sum.inr : FinitePlace F → KPHilbert.Place F) ⁻¹'
      Function.mulSupport f).Finite
    exact hf.preimage Sum.inr_injective.injOn
  have hsub : Function.mulSupport f ⊆
      Set.range (Sum.inr : FinitePlace F → KPHilbert.Place F) := by
    intro p hmem
    cases p with
    | inl w => exact (hmem rfl).elim
    | inr v => exact ⟨v, rfl⟩
  refine ⟨hfinite, ?_⟩
  change (∏ᶠ v : FinitePlace F, f (Sum.inr v)) = 1
  calc
    (∏ᶠ v : FinitePlace F, f (Sum.inr v)) =
        ∏ᶠ p ∈ Set.range (Sum.inr : FinitePlace F → KPHilbert.Place F), f p :=
      (finprod_mem_range Sum.inr_injective).symm
    _ = ∏ᶠ p, f p := by
      rw [← finprod_mem_mulSupport f,
        ← finprod_mem_inter_mulSupport f (Set.range Sum.inr)]
      rw [Set.inter_eq_right.mpr hsub]
    _ = 1 := hp

theorem actualFamily_tame_units (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (v : FinitePlace F) (hgood : (6 : 𝓞 F) ∉ v.asIdeal)
    (u u' : (LocalIntegers F v)ˣ) :
    actualFamily F ζ hζ v (integerUnitInclusion F v u)
      (integerUnitInclusion F v u') = 1 := by
  have hgood' := (KPHilbert.tame_place_iff F v).2 hgood
  change KPHilbert.B6 F ζ hζ (Sum.inr v)
    (KPHilbert.integerUnitInclusion F v u) (KPHilbert.integerUnitInclusion F v u') = 1
  exact (KPHilbert.B6_tame_ordinaryValuation F v ζ hζ hgood' 1 u u').2

section FiniteComparison

open ValuativeRel LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open KummerTheory LocalClassFieldTheory.Kummer

private theorem iso_unique
    (e : WithZero (Multiplicative ℤ) ≃*o WithZero (Multiplicative ℤ)) :
    e = OrderMonoidIso.refl _ := by
  have hf : OrderMonoidIso.withZero.symm e = OrderMonoidIso.refl (Multiplicative ℤ) :=
    Subsingleton.elim _ _
  have := congrArg OrderMonoidIso.withZero hf
  have hh : e = OrderMonoidIso.withZero (OrderMonoidIso.refl (Multiplicative ℤ)) := by
    simpa using this
  exact hh.trans (by ext x; cases x <;> rfl)

private theorem val_eq (v : FinitePlace F) (x : v.adicCompletion F) :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (v.adicCompletion F)
      (valuation (v.adicCompletion F) x) = Valued.v x := by
  let ν : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let : ν.Compatible := Valuation.Compatible.ofValuation _
  let e := (ValuativeRel.ValueGroupWithZero.orderMonoidIso ν).trans
    (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt ν)
  have he : e = IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt
      (v.adicCompletion F) := by
    have hh := iso_unique (e.symm.trans
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (v.adicCompletion F)))
    ext a
    have h := congrArg (fun f => f (e a)) hh
    simpa using h.symm
  rw [← he]
  change Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt ν
    (ValuativeRel.ValueGroupWithZero.orderMonoidIso ν
      (valuation (v.adicCompletion F) x)) = _
  rw [ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀]
  exact Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
    (v.valuedAdicCompletion_surjective F) x

theorem ordinaryValuation_eq_one (v : FinitePlace F)
    (π : (v.adicCompletion F)ˣ) (hπ : OrdinaryUniformizer F v π) :
    KPHilbert.ordinaryValuation F v π = 1 := by
  unfold KPHilbert.ordinaryValuation
  rw [valuationMap_apply, v_apply, WithZero.toAdd_unzero_eq_log]
  change -WithZero.log
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (v.adicCompletion F)
      (valuation (v.adicCompletion F) (π : v.adicCompletion F))) = 1
  rw [val_eq F v, hπ]
  rfl

private def sixthRootLocal (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (v : FinitePlace F) (t : rootsOfUnity 6 F) :
    nthRootsSubgroup (v.adicCompletion F) 6 :=
  (nthRootsSubgroupEquivRootsOfUnity (v.adicCompletion F) 6).symm
    (KPHilbert.finiteRootsSix F ζ hζ v t)

private theorem sixthRootLocal_value (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (v : FinitePlace F) (t : rootsOfUnity 6 F) :
    ((sixthRootLocal F ζ hζ v t : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) ((t : Fˣ) : F) := by
  exact congrArg (fun z : rootsOfUnity 6 (v.adicCompletion F) =>
    ((z : (v.adicCompletion F)ˣ) : v.adicCompletion F))
    ((nthRootsSubgroupEquivRootsOfUnity (v.adicCompletion F) 6).apply_symm_apply
      (KPHilbert.finiteRootsSix F ζ hζ v t))

def sixthRootsReduction (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (v : FinitePlace F) : rootsOfUnity 6 F →* rootsOfUnity 6 (Residue F v) :=
  (localNthRootsReduction (v.adicCompletion F) (6 : ℕ+)).comp
    (((nthRootsSubgroupEquivRootsOfUnity (v.adicCompletion F) 6).symm.toMonoidHom).comp
      (KPHilbert.finiteRootsSix F ζ hζ v).toMonoidHom)

theorem sixthRootsReduction_injective (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (v : FinitePlace F) (hgood : (6 : 𝓞 F) ∉ v.asIdeal) :
    Function.Injective (sixthRootsReduction F ζ hζ v) := by
  intro a b hab
  apply (KPHilbert.finiteRootsSix F ζ hζ v).injective
  apply (nthRootsSubgroupEquivRootsOfUnity (v.adicCompletion F) 6).symm.injective
  exact localNthRootsReduction_injective (v.adicCompletion F) (6 : ℕ+)
    ((KPHilbert.tame_place_iff F v).2 hgood) hab

theorem sixthRootsReduction_representative (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (v : FinitePlace F) (t : rootsOfUnity 6 F) (r : LocalIntegers F v)
    (hr : (r : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) ((t : Fˣ) : F)) :
    ((sixthRootsReduction F ζ hζ v t : (Residue F v)ˣ) : Residue F v) =
      IsLocalRing.residue (LocalIntegers F v) r := by
  let K := v.adicCompletion F
  let z := sixthRootLocal F ζ hζ v t
  let rU := nthRootIntegerUnit K (6 : ℕ+) z
  have hrU : (rU : LocalIntegers F v) = r := by
    apply Subtype.ext
    exact ((congrArg Units.val
      (integerUnitsToFieldUnits_nthRootIntegerUnit K (6 : ℕ+) z)).trans
      (sixthRootLocal_value F ζ hζ v t)).trans hr.symm
  change
    ((LocalFieldTheory.residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K rU) :
      (Residue F v)ˣ) : Residue F v) = _
  rw [integerUnitsToResidueUnits_apply]
  exact congrArg (IsLocalRing.residue (LocalIntegers F v)) hrU

theorem actualFamily_tame_residue (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (v : FinitePlace F) (hgood : (6 : 𝓞 F) ∉ v.asIdeal)
    (π : (v.adicCompletion F)ˣ) (hπ : OrdinaryUniformizer F v π)
    (u : (LocalIntegers F v)ˣ) :
    ∃ r : LocalIntegers F v,
      (r : v.adicCompletion F) = algebraMap F (v.adicCompletion F)
        ((actualFamily F ζ hζ v π (integerUnitInclusion F v u) : Fˣ) : F) ∧
      IsLocalRing.residue (LocalIntegers F v) r =
        IsLocalRing.residue (LocalIntegers F v) (u : LocalIntegers F v) ^
          ((Nat.card (Residue F v) - 1) / 6) := by
  let K := v.adicCompletion F
  have hgood' := (KPHilbert.tame_place_iff F v).2 hgood
  have hπ' := ordinaryValuation_eq_one F v π hπ
  let z := sixthRootLocal F ζ hζ v
    (actualFamily F ζ hζ v π (integerUnitInclusion F v u))
  have hz : z = localTamePowerResidueSymbol K (6 : ℕ+) hgood'
      (KPHilbert.localRootsSix F v ζ hζ) u := by
    dsimp only [z, sixthRootLocal]
    change (nthRootsSubgroupEquivRootsOfUnity K 6).symm
      (KPHilbert.finiteRootsSix F ζ hζ v
        (KPHilbert.B6 F ζ hζ (Sum.inr v) π
          (KPHilbert.integerUnitInclusion F v u))) = _
    rw [(KPHilbert.B6_tame F v ζ hζ hgood' π hπ' u u).1]
    unfold K
    simp only [KPHilbert.residueSixCharacter, MulEquiv.apply_symm_apply]
    rfl
  let rU := nthRootIntegerUnit K (6 : ℕ+) z
  refine ⟨(rU : LocalIntegers F v), ?_, ?_⟩
  · exact (congrArg Units.val
      (integerUnitsToFieldUnits_nthRootIntegerUnit K (6 : ℕ+) z)).trans
      (sixthRootLocal_value F ζ hζ v
        (actualFamily F ζ hζ v π (integerUnitInclusion F v u)))
  · let : Fintype (Residue F v) := Fintype.ofFinite _
    have hred := localNthRootsReductionEquiv_localTamePowerResidueSymbol K (6 : ℕ+)
      hgood' (KPHilbert.localRootsSix F v ζ hζ) u
    rw [← hz] at hred
    have h := congrArg (fun w : rootsOfUnity 6 (Residue F v) =>
      ((w : (Residue F v)ˣ) : Residue F v)) hred
    change
      ((LocalFieldTheory.residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K rU) :
        (Residue F v)ˣ) : Residue F v) = _ at h
    rw [integerUnitsToResidueUnits_apply] at h
    change IsLocalRing.residue (LocalIntegers F v) (rU : LocalIntegers F v) =
      ((LocalFieldTheory.residueUnitsConcreteEquiv K
        (integerUnitsToResidueUnits K u ^
          ((Fintype.card (Residue F v) - 1) / 6)) : (Residue F v)ˣ) :
        Residue F v) at h
    rw [map_pow, Units.val_pow_eq_pow_val, integerUnitsToResidueUnits_apply] at h
    simpa only [Nat.card_eq_fintype_card] using h

theorem actualFamily_isSexticHilbertFamily (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    IsSexticHilbertFamily F (actualFamily F ζ hζ) := by
  obtain ⟨hl, hr, ha⟩ := actualFamily_laws F ζ hζ
  refine ⟨actualFamily_continuous F ζ hζ, hl, hr, ha,
    actualFamily_productFormula F ζ hζ, ?_⟩
  intro v hgood
  exact ⟨actualFamily_tame_units F ζ hζ v hgood,
    actualFamily_tame_residue F ζ hζ v hgood⟩

theorem tame_uniformizer_eq (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    {H J : Family F} (hH : IsSexticHilbertFamily F H) (hJ : IsSexticHilbertFamily F J)
    (v : FinitePlace F) (hgood : (6 : 𝓞 F) ∉ v.asIdeal)
    (π : (v.adicCompletion F)ˣ) (hπ : OrdinaryUniformizer F v π)
    (u : (LocalIntegers F v)ˣ) :
    H v π (integerUnitInclusion F v u) = J v π (integerUnitInclusion F v u) := by
  obtain ⟨r, hr, hresr⟩ := (hH.tame v hgood).2 π hπ u
  obtain ⟨s, hs, hress⟩ := (hJ.tame v hgood).2 π hπ u
  apply sixthRootsReduction_injective F ζ hζ v hgood
  apply Subtype.ext
  apply Units.ext
  rw [sixthRootsReduction_representative F ζ hζ v _ r hr,
    sixthRootsReduction_representative F ζ hζ v _ s hs]
  exact hresr.trans hress.symm

private theorem ordinaryUniformizer_exists (v : FinitePlace F) :
    ∃ π : (v.adicCompletion F)ˣ, OrdinaryUniformizer F v π := by
  obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective F
    ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  have hx0 : x ≠ 0 := by
    intro h
    simp [h] at hx
  exact ⟨Units.mk0 x hx0, hx⟩

theorem ordinaryUniformizer_decomposition (v : FinitePlace F)
    (π : (v.adicCompletion F)ˣ) (hπ : OrdinaryUniformizer F v π) :
    ∀ a : (v.adicCompletion F)ˣ, ∃ n : ℤ, ∃ u : (LocalIntegers F v)ˣ,
      a = π ^ n * integerUnitInclusion F v u := by
  let K := v.adicCompletion F
  have hv : -valuationMap K (Additive.ofMul π) = 1 :=
    ordinaryValuation_eq_one F v π hπ
  have hinv : valuationMap K (Additive.ofMul π⁻¹) = 1 := by
    change valuationMap K (-Additive.ofMul π) = 1
    rw [map_neg]
    exact hv
  intro a
  obtain ⟨u, hu⟩ := exists_integerUnit_mul_uniformizer_zpow K π⁻¹ hinv a
  refine ⟨-valuationMap K (Additive.ofMul a), u, ?_⟩
  change a = π ^ (-valuationMap K (Additive.ofMul a)) * integerUnitsToFieldUnits K u
  simpa only [inv_zpow, zpow_neg, mul_comm] using hu.symm

theorem tame_place_eq (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    {H J : Family F} (hH : IsSexticHilbertFamily F H) (hJ : IsSexticHilbertFamily F J)
    (v : FinitePlace F) (hgood : (6 : 𝓞 F) ∉ v.asIdeal) : H v = J v := by
  obtain ⟨π, hπ⟩ := ordinaryUniformizer_exists F v
  exact eq_of_uniformizer_decomposition (H v) (J v)
    (hH.mul_left v) (hH.mul_right v) (hH.alternating v)
    (hJ.mul_left v) (hJ.mul_right v) (hJ.alternating v)
    π (integerUnitInclusion F v)
    (ordinaryUniformizer_decomposition F v π hπ)
    (hH.tame v hgood).1 (hJ.tame v hgood).1
    (tame_uniformizer_eq F ζ hζ hH hJ v hgood π hπ)

end FiniteComparison

end ActualFamily

section GlobalUniqueness

open Topology

variable (F : Type) [Field F] [NumberField F]

abbrev UnitSpace (S : Finset (FinitePlace F)) :=
  (v : S) → (v.val.adicCompletion F)ˣ

def unitDiagonal (S : Finset (FinitePlace F)) (a : Fˣ) : UnitSpace F S :=
  fun v => diagonal F v.val a

private def fieldDiagonal (S : Finset (FinitePlace F)) (a : F) :
    PoissonSFiniteDensity.Space F S :=
  fun v => algebraMap F (v.val.adicCompletion F) a

private theorem fieldDiagonal_denseRange (S : Finset (FinitePlace F)) :
    DenseRange (fieldDiagonal F S) := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨_, hz, ⟨m, rfl⟩⟩ :=
    (dense_iff_inter_open.mp
      (PoissonSFiniteDensity.diagonal_denseRange F S)) U hU hUne
  refine ⟨_, hz, ⟨(m : F), ?_⟩⟩
  funext v
  rfl

theorem unitDiagonal_denseRange (S : Finset (FinitePlace F)) :
    DenseRange (unitDiagonal F S) := by
  classical
  by_cases hS : S.Nonempty
  · apply dense_iff_inter_open.mpr
    intro U hU hUne
    obtain ⟨b, hb⟩ := hUne
    obtain ⟨u, hu, huU⟩ := isOpen_pi_iff'.mp hU b hb
    let W : Set (PoissonSFiniteDensity.Space F S) :=
      Set.pi Set.univ (fun v : S => Units.val '' u v)
    have hW : IsOpen W := by
      apply isOpen_pi_iff'.mpr
      intro z hz
      refine ⟨(fun v : S => Units.val '' u v), ?_, ?_⟩
      · intro v
        exact ⟨(IsOpenUnits.isOpenEmbedding_unitsVal
          (M := v.val.adicCompletion F)).isOpenMap (u v) (hu v).1,
          hz v (Set.mem_univ v)⟩
      · exact Set.Subset.rfl
    have hWne : W.Nonempty := by
      refine ⟨(fun v => (b v : v.val.adicCompletion F)), ?_⟩
      intro v _
      exact ⟨b v, (hu v).2, rfl⟩
    obtain ⟨_, hxW, ⟨x, rfl⟩⟩ :=
      (dense_iff_inter_open.mp (fieldDiagonal_denseRange F S)) W hW hWne
    obtain ⟨v₀, hv₀⟩ := hS
    have hx : x ≠ 0 := by
      intro hx
      obtain ⟨q, _, hq⟩ := hxW ⟨v₀, hv₀⟩ (Set.mem_univ _)
      simp [fieldDiagonal, hx] at hq
    let a : Fˣ := Units.mk0 x hx
    refine ⟨unitDiagonal F S a, ?_, ⟨a, rfl⟩⟩
    apply huU
    intro v _
    obtain ⟨q, hqu, hq⟩ := hxW v (Set.mem_univ v)
    have he : unitDiagonal F S a v = q := by
      apply Units.val_injective
      change algebraMap F (v.val.adicCompletion F) x =
        (q : v.val.adicCompletion F)
      exact hq.symm
    rw [he]
    exact hqu
  · let : IsEmpty S := ⟨fun v => hS ⟨v.val, v.property⟩⟩
    apply dense_iff_inter_open.mpr
    intro U _ hUne
    obtain ⟨b, hb⟩ := hUne
    refine ⟨unitDiagonal F S 1, ?_, ⟨1, rfl⟩⟩
    have he : unitDiagonal F S 1 = b := Subsingleton.elim _ _
    simpa only [he] using hb

local instance : TopologicalSpace (rootsOfUnity 6 F) := ⊥
local instance : DiscreteTopology (rootsOfUnity 6 F) := ⟨rfl⟩

private theorem pairing_one_left (H : Family F) (hH : IsSexticHilbertFamily F H)
    (v : FinitePlace F) (b : (v.adicCompletion F)ˣ) : H v 1 b = 1 := by
  have he : H v 1 b * 1 = H v 1 b * H v 1 b := by
    simpa only [one_mul, mul_one] using hH.mul_left v 1 1 b
  exact (mul_left_cancel he).symm

private def ratioFamily (H J : Family F) : Family F :=
  fun v a b => H v a b / J v a b

private theorem ratio_prod_diagonal_eq_one
    (S : Finset (FinitePlace F)) (H J : Family F)
    (hH : IsSexticHilbertFamily F H) (hJ : IsSexticHilbertFamily F J)
    (hout : ∀ v : FinitePlace F, v ∉ S → H v = J v) (a b : Fˣ) :
    (∏ v ∈ S, ratioFamily F H J v (diagonal F v a) (diagonal F v b)) = 1 := by
  have hf := hH.productFormula a b
  have hg := hJ.productFormula a b
  have hs : Function.mulSupport
      (fun v => ratioFamily F H J v (diagonal F v a) (diagonal F v b)) ⊆
      (S : Set (FinitePlace F)) := by
    intro v hv
    by_contra hnot
    apply hv
    dsimp only [ratioFamily]
    rw [hout v hnot, div_self']
  have hr :
      (∏ᶠ v, ratioFamily F H J v (diagonal F v a) (diagonal F v b)) = 1 := by
    simpa only [ratioFamily, hf.2, hg.2, div_self'] using
      (finprod_div_distrib hf.1 hg.1)
  rw [← finprod_eq_prod_of_mulSupport_subset _ hs]
  exact hr

private def finiteRatio (S : Finset (FinitePlace F)) (H J : Family F)
    (ab : UnitSpace F S × UnitSpace F S) : rootsOfUnity 6 F :=
  ∏ v ∈ S.attach, ratioFamily F H J v.val (ab.1 v) (ab.2 v)

private theorem finiteRatio_continuous
    (S : Finset (FinitePlace F)) (H J : Family F)
    (hH : IsSexticHilbertFamily F H) (hJ : IsSexticHilbertFamily F J) :
    Continuous (finiteRatio F S H J) := by
  unfold finiteRatio ratioFamily
  apply continuous_finsetProd
  intro v _
  have hc : Continuous
      (fun ab : UnitSpace F S × UnitSpace F S => (ab.1 v, ab.2 v)) :=
    ((continuous_apply v).comp continuous_fst).prodMk
      ((continuous_apply v).comp continuous_snd)
  simp_rw [div_eq_mul_inv]
  exact ((hH.continuous v.val).comp hc).mul
    (((hJ.continuous v.val).comp hc).inv)

private theorem finiteRatio_eq_one
    (S : Finset (FinitePlace F)) (H J : Family F)
    (hH : IsSexticHilbertFamily F H) (hJ : IsSexticHilbertFamily F J)
    (hout : ∀ v : FinitePlace F, v ∉ S → H v = J v) :
    ∀ ab : UnitSpace F S × UnitSpace F S, finiteRatio F S H J ab = 1 := by
  have hd := (unitDiagonal_denseRange F S).prodMap (unitDiagonal_denseRange F S)
  have he : finiteRatio F S H J = (fun _ => 1) :=
    hd.equalizer (finiteRatio_continuous F S H J hH hJ) continuous_const (by
      funext ab
      change (∏ v ∈ S.attach, ratioFamily F H J v.val
        (diagonal F v.val ab.1) (diagonal F v.val ab.2)) = 1
      rw [Finset.prod_attach S (fun v : FinitePlace F =>
        ratioFamily F H J v (diagonal F v ab.1) (diagonal F v ab.2))]
      exact ratio_prod_diagonal_eq_one F S H J hH hJ hout ab.1 ab.2)
  intro ab
  exact congr_fun he ab

private theorem finiteRatio_at_update
    (S : Finset (FinitePlace F)) (H J : Family F)
    (hH : IsSexticHilbertFamily F H) (hJ : IsSexticHilbertFamily F J)
    (v : FinitePlace F) (hv : v ∈ S) (a b : (v.adicCompletion F)ˣ) :
    finiteRatio F S H J
      (Function.update (fun _ : S => 1) ⟨v, hv⟩ a,
       Function.update (fun _ : S => 1) ⟨v, hv⟩ b) =
      ratioFamily F H J v a b := by
  classical
  let w : S := ⟨v, hv⟩
  let x : UnitSpace F S := Function.update (fun _ => 1) w a
  let y : UnitSpace F S := Function.update (fun _ => 1) w b
  change finiteRatio F S H J (x, y) = ratioFamily F H J v a b
  calc
    finiteRatio F S H J (x, y) =
        ratioFamily F H J w.val (x w) (y w) := by
      unfold finiteRatio
      apply Finset.prod_eq_single
      · intro i _ hi
        change ratioFamily F H J i.val (x i) (y i) = 1
        have hxi : x i = 1 := by simp [x, hi]
        have hyi : y i = 1 := by simp [y, hi]
        rw [hxi, hyi]
        simp only [ratioFamily, pairing_one_left F H hH,
          pairing_one_left F J hJ, div_self']
      · intro hnot
        exact (hnot (by simp)).elim
    _ = ratioFamily F H J v a b := by simp [x, y, w]

theorem family_eq_of_eq_outside_finset
    (S : Finset (FinitePlace F)) (H J : Family F)
    (hH : IsSexticHilbertFamily F H) (hJ : IsSexticHilbertFamily F J)
    (hout : ∀ v : FinitePlace F, v ∉ S → H v = J v) : H = J := by
  classical
  funext v a b
  by_cases hv : v ∈ S
  · have hone := finiteRatio_eq_one F S H J hH hJ hout
      (Function.update (fun _ : S => 1) ⟨v, hv⟩ a,
       Function.update (fun _ : S => 1) ⟨v, hv⟩ b)
    have hisolate := finiteRatio_at_update F S H J hH hJ v hv a b
    exact div_eq_one.mp
      (show H v a b / J v a b = 1 from hisolate.symm.trans hone)
  · exact congr_fun (congr_fun (hout v hv) a) b

theorem finite_badPlaces :
    {v : FinitePlace F | (6 : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have hspan : Ideal.span ({(6 : 𝓞 F)} : Set (𝓞 F)) ≠ 0 := by
    intro h
    have h6 : (6 : 𝓞 F) = 0 := Ideal.span_singleton_eq_bot.mp h
    norm_num at h6
  simpa only [Ideal.dvd_span_singleton] using (Ideal.finite_factors hspan)

theorem sexticHilbertFamily_unique (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    {H J : Family F} (hH : IsSexticHilbertFamily F H)
    (hJ : IsSexticHilbertFamily F J) : H = J := by
  classical
  let S := (finite_badPlaces F).toFinset
  apply family_eq_of_eq_outside_finset F S H J hH hJ
  intro v hv
  apply tame_place_eq F ζ hζ hH hJ v
  simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hv

theorem eq_actualFamily (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    {H : Family F} (hH : IsSexticHilbertFamily F H) :
    H = actualFamily F ζ hζ := by
  exact sexticHilbertFamily_unique F ζ hζ hH
    (actualFamily_isSexticHilbertFamily F ζ hζ)

end GlobalUniqueness

end
end DedekindZetaZeroFree.PalomarHilbert

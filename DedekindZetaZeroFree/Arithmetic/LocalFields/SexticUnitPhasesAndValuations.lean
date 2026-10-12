module

public import DedekindZetaZeroFree.Theta.Whittaker.NormalizedResidualFunctionals

@[expose] public section

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical ValuativeRel
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.UnitCovarianceCompletion
open LocalFiniteSums LocalFiniteSumCompatibility
variable {F : Type} [Field F] [NumberField F] {A : SArithmeticData F} {σ : F →+* ℂ}
local instance (p : ExteriorPrime A) : ValuativeRel (LocalField p) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F p.val
local instance (p : ExteriorPrime A) : IsNonarchimedeanLocalField (LocalField p) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F p.val

theorem chi_eq_residueSixCharacter_of_residue (p : ExteriorPrime A) (x : A.R)
    (u : KPHilbert.LocalIntegerUnits F p.val)
    (hu : IsLocalRing.residue _ u.val =
      cftResidueEquiv p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) x)) :
    chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) x) =
      σ (((KPHilbert.residueSixCharacter F p.val A.zeta12
        A.primitive_zeta12 (exterior_tame p) u : rootsOfUnity 6 F) : Fˣ) : F) := by
  let e := cftResidueEquiv p
  let r := Units.map (IsLocalRing.residue (ValuativeRel.valuation (LocalField p)).integer).toMonoidHom u
  let q := Units.map e.symm.toMonoidHom r
  have hq : (q : A.R ⧸ A.extendIdeal (primeIdeal p)) = Ideal.Quotient.mk _ x := by
    apply e.injective
    change e (e.symm r.val) = e (Ideal.Quotient.mk _ x)
    rw [e.apply_symm_apply]
    exact hu
  obtain ⟨j, hj, he, hr⟩ := A.sexticResidueFamily_normalized.2.1 (primeIdeal p) p.val rfl q
  let a : rootsOfUnity 6 F := ⟨A.sexticResidueFamily (primeIdeal p) q,
    A.sexticResidueFamily_normalized.1 (primeIdeal p) q⟩
  let z := (KummerTheory.nthRootsSubgroupEquivRootsOfUnity (LocalField p) 6).symm
    (KPHilbert.finiteRootsSix F A.zeta12 A.primitive_zeta12 p.val a)
  let w := integerRingEquiv p (integerMap p
    (algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ (2 * j))))
  have hw : (w : LocalField p) = (z.val : LocalField p) := by
    change algebraMap F (LocalField p) (((algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ (2 * j))) : A.R) : F) =
      algebraMap F (LocalField p) (A.sexticResidueFamily (primeIdeal p) q : F)
    rw [he]
    congr 1
  have hcard : Nat.card (A.R ⧸ A.extendIdeal (primeIdeal p)) =
      Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation (LocalField p)).integer) := Nat.card_congr e.toEquiv
  have hred := congrArg e hr
  rw [map_pow e] at hred
  have heq : e q.val = r.val := e.apply_symm_apply r.val
  rw [heq] at hred
  rw [cftResidueEquiv_mk, hcard] at hred
  let : Fintype (IsLocalRing.ResidueField (ValuativeRel.valuation (LocalField p)).integer) := Fintype.ofFinite _
  have hz : z = LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol (LocalField p) 6
      (exterior_tame p) (KPHilbert.localRootsSix F p.val A.zeta12 A.primitive_zeta12) u := by
    apply (LocalClassFieldTheory.Kummer.localNthRootsReductionEquiv (LocalField p) 6
      (exterior_tame p) (KPHilbert.localRootsSix F p.val A.zeta12 A.primitive_zeta12)).injective
    rw [LocalClassFieldTheory.Kummer.localNthRootsReductionEquiv_localTamePowerResidueSymbol
      (LocalField p) 6 (exterior_tame p) (KPHilbert.localRootsSix F p.val A.zeta12 A.primitive_zeta12) u]
    apply Subtype.ext
    apply Units.ext
    rw [rootReduction p (exterior_tame p) (KPHilbert.localRootsSix F p.val A.zeta12 A.primitive_zeta12) z w hw]
    apply hred.trans
    change r.val ^ ((Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation (LocalField p)).integer) - 1) / 6) = r.val ^ ((Fintype.card (IsLocalRing.ResidueField (ValuativeRel.valuation (LocalField p)).integer) - 1) / 6)
    rw [Nat.card_eq_fintype_card]
  have ha : a = KPHilbert.residueSixCharacter F p.val A.zeta12 A.primitive_zeta12 (exterior_tame p) u := by
    apply (KPHilbert.finiteRootsSix F A.zeta12 A.primitive_zeta12 p.val).injective
    change (KummerTheory.nthRootsSubgroupEquivRootsOfUnity (LocalField p) 6) z = _
    rw [hz]
    exact ((KPHilbert.finiteRootsSix F A.zeta12 A.primitive_zeta12 p.val).apply_symm_apply _).symm
  rw [← hq]
  simp only [chi, SArithmeticData.sexticResiduePowerChar, SArithmeticData.sexticExponent]
  norm_num only [Int.toNat_one, pow_one]
  change MulChar.ofUnitHom ((Units.map σ.toMonoidHom).comp (A.sexticResidueFamily (primeIdeal p))) q.val = _
  rw [MulChar.ofUnitHom_coe]
  exact congrArg σ (congrArg (fun b : rootsOfUnity 6 F => (b.val : F)) ha)

theorem residue_eq_of_norm_sub_lt_one (p : ExteriorPrime A)
    (u : KPHilbert.LocalIntegerUnits F p.val) (t : 𝓞 F)
    (ht : ‖((u.val : (ValuativeRel.valuation (LocalField p)).integer) : LocalField p) -
      algebraMap (𝓞 F) (LocalField p) t‖ < 1) :
    IsLocalRing.residue _ u.val =
      cftResidueEquiv p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p))
        (algebraMap (𝓞 F) A.R t)) := by
  rw [cftResidueEquiv_mk]
  apply sub_eq_zero.mp
  rw [← map_sub, IsLocalRing.residue_eq_zero_iff]
  change ¬ IsUnit _
  apply Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr
  let : (Valued.v : Valuation (LocalField p) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [← (ValuativeRel.isEquiv
    (Valued.v : Valuation (LocalField p) (WithZero (Multiplicative ℤ)))
    (ValuativeRel.valuation (LocalField p))).lt_one_iff_lt_one]
  apply Valued.toNormedField.norm_lt_one_iff.mp
  exact ht

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

abbrev localPrime (p : ThetaBranch.ExteriorPrime A) : LocalFiniteSums.ExteriorPrime A :=
  ⟨p.val, (ThetaBranch.primeIdeal A p).property.2⟩

theorem unit_phase_of_norm_sub_lt_one (R : PrincipalMellin.ActualRecipe S η)
    (hR : MomentSources.RootAligned R) (p : ThetaBranch.ExteriorPrime R.A)
    (u : KPHilbert.LocalIntegerUnits F p.val) (t : 𝓞 F)
    (ht : ‖((u.val : (ValuativeRel.valuation (p.val.adicCompletion F)).integer) : p.val.adicCompletion F) -
      algebraMap (𝓞 F) (p.val.adicCompletion F) t‖ < 1) :
    (KPLocalCover.coefficientEmbedding F R.A.zeta12 R.A.primitive_zeta12
      (KPHilbert.residueSixCharacter F p.val R.A.zeta12 R.A.primitive_zeta12
        (exterior_tame (localPrime p)) u) : ℂ) =
      ThetaBranch.residueCharacter R.A R.σ p (Ideal.Quotient.mk p.val.asIdeal t) := by
  rw [NormalizedProbe.principal_prime_residueCharacter_transport]
  erw [ArithGaussCRT.exteriorQuotientEquiv_mk R.A (ThetaBranch.primeIdeal R.A p) t]
  have h := chi_eq_residueSixCharacter_of_residue (σ := R.σ) (localPrime p)
    (algebraMap (𝓞 F) R.A.R t) u (residue_eq_of_norm_sub_lt_one (localPrime p) u t ht)
  have hr := hR (KPHilbert.residueSixCharacter F p.val R.A.zeta12 R.A.primitive_zeta12 (exterior_tame (localPrime p)) u)
  have he : KPLocalCover.coefficientEmbedding F S.zeta12 S.primitive_zeta12 =
      KPLocalCover.coefficientEmbedding F R.A.zeta12 R.A.primitive_zeta12 := by
    congr 1
    exact R.sameRoot.symm
  rw [he] at hr
  exact (h.trans hr).symm

section Valuation
open ValuativeRel LocalFieldTheory.IsNonarchimedeanLocalField
variable (q : HeightOneSpectrum (𝓞 F))
local instance : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
local instance : IsNonarchimedeanLocalField (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
private theorem iso_unique (e : WithZero (Multiplicative ℤ) ≃*o WithZero (Multiplicative ℤ)) : e = OrderMonoidIso.refl _ := by
  have hf : OrderMonoidIso.withZero.symm e = OrderMonoidIso.refl (Multiplicative ℤ) := Subsingleton.elim _ _
  have := congrArg OrderMonoidIso.withZero hf
  have hh : e = OrderMonoidIso.withZero (OrderMonoidIso.refl (Multiplicative ℤ)) := by simpa using this
  exact hh.trans (by ext x; cases x <;> rfl)
private theorem val_eq (x : q.adicCompletion F) :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (q.adicCompletion F) (valuation (q.adicCompletion F) x) = Valued.v x := by
  let ν : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let : ν.Compatible := Valuation.Compatible.ofValuation _
  let e := (ValuativeRel.ValueGroupWithZero.orderMonoidIso ν).trans
    (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt ν)
  have he : e = IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (q.adicCompletion F) := by
    have hh := iso_unique (e.symm.trans (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (q.adicCompletion F)))
    ext a
    have h := congrArg (fun f => f (e a)) hh
    simpa using h.symm
  rw [← he]
  change Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt ν
    (ValuativeRel.ValueGroupWithZero.orderMonoidIso ν (valuation (q.adicCompletion F) x)) = _
  rw [ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀]
  exact Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
    (q.valuedAdicCompletion_surjective F) x
theorem ordinaryValuation_eq_order (x : Fˣ) :
    KPHilbert.ordinaryValuation F q (Units.map (algebraMap F (q.adicCompletion F)).toMonoidHom x) = ThetaBranch.order q x := by
  unfold KPHilbert.ordinaryValuation
  rw [valuationMap_apply, v_apply, WithZero.toAdd_unzero_eq_log]
  change -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (q.adicCompletion F)
    (valuation (q.adicCompletion F) (algebraMap F (q.adicCompletion F) (x : F)))) = _
  rw [val_eq]
  exact congrArg (fun a : WithZero (Multiplicative ℤ) => -WithZero.log a)
    (q.valuedAdicCompletion_eq_valuation' (K := F) (x : F))

end Valuation

theorem exterior_completion_generator_ordinary_valuation (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) :
    KPHilbert.ordinaryValuation F p.val (ThetaExpansion.exteriorCompletionGenerator R p) = 1 := by
  rw [ordinaryValuation_eq_order, ThetaBranch.generator_order]
  simp [ThetaBranch.primeIdeal, idealPrimeExponent,
    UniqueFactorizationMonoid.normalizedFactors_irreducible p.val.irreducible]

theorem exists_integerUnit_of_valuation_one (p : ThetaBranch.ExteriorPrime A)
    (u : (p.val.adicCompletion F)ˣ)
    (hu : ValuativeRel.valuation (p.val.adicCompletion F) (u : p.val.adicCompletion F) = 1) :
    ∃ ui : KPHilbert.LocalIntegerUnits F p.val,
      KPHilbert.integerUnitInclusion F p.val ui = u := by
  let a : (ValuativeRel.valuation (p.val.adicCompletion F)).integer := ⟨u, le_of_eq hu⟩
  have ha : IsUnit a :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (ValuativeRel.valuation (p.val.adicCompletion F)))).mpr hu
  refine ⟨ha.unit, ?_⟩
  apply Units.ext
  change ((ha.unit.val : (ValuativeRel.valuation (p.val.adicCompletion F)).integer) :
    p.val.adicCompletion F) = (u : p.val.adicCompletion F)
  rw [ha.unit_spec]

end DedekindZetaZeroFree.ExteriorWhittakerValues.UnitCovarianceCompletion

end

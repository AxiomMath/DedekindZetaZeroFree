module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.SignedTraceUniformizer
public import DedekindZetaZeroFree.Arithmetic.LocalFields.SexticUnitPhasesAndValuations
public import DedekindZetaZeroFree.Theta.Whittaker.UnitDiagonalCovariance
public import DedekindZetaZeroFree.CharacterSums.Gauss.WeightedUnitShellIntegrals

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical ValuativeRel
open NumberField IsDedekindDomain ValuativeRel
namespace DedekindZetaZeroFree.ExteriorWhittakerValues.ShellArithmetic
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem allowedGenerator_integer_irreducible (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) :
    ∃ π : (valuation (p.val.adicCompletion F)).integer, Irreducible π ∧
      (π : p.val.adicCompletion F) = (ThetaExpansion.exteriorCompletionGenerator R p : p.val.adicCompletion F) := by
  let x := R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p)
  have ho : ThetaBranch.order p.val x = 1 := by
    rw [← UnitCovarianceCompletion.ordinaryValuation_eq_order]
    exact UnitCovarianceCompletion.exterior_completion_generator_ordinary_valuation R p
  have hv : p.val.valuation F (x : F) = WithZero.exp (-1 : ℤ) := by
    have hn := (Valuation.ne_zero_iff (p.val.valuation F)).mpr x.ne_zero
    have hl : WithZero.log (p.val.valuation F (x : F)) = -1 := by
      unfold ThetaBranch.order at ho
      omega
    rw [← WithZero.exp_log hn, hl]
  have hc : Valued.v (ThetaExpansion.exteriorCompletionGenerator R p : p.val.adicCompletion F) =
      WithZero.exp (-1 : ℤ) :=
    (p.val.valuedAdicCompletion_eq_valuation' (K := F) (x : F)).trans hv
  have hm : (ThetaExpansion.exteriorCompletionGenerator R p : p.val.adicCompletion F) ∈
      p.val.adicCompletionIntegers F := by
    change Valued.v (ThetaExpansion.exteriorCompletionGenerator R p : p.val.adicCompletion F) ≤ (1 : WithZero (Multiplicative ℤ))
    rw [hc, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  let π : p.val.adicCompletionIntegers F := ⟨_, hm⟩
  have hu : (Valued.v : Valuation (p.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer
      (π : p.val.adicCompletion F) := by
    rw [Valuation.IsUniformizer.iff,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (p.val.valuedAdicCompletion_surjective F)]
    exact hc
  have hi : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hu.is_generator
  let J := LocalFiniteSumCompatibility.integerRingEquiv (UnitCovarianceCompletion.localPrime p)
  exact ⟨J π, (MulEquiv.irreducible_iff (f := J)).mpr hi, rfl⟩

def tracePsi (p : KPFinitePlace F) : AddChar (p.adicCompletion F) ℂ where
  toFun x := (ResidueTrace.localTraceCharacter p x : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by rw [AddChar.map_add_eq_mul, Circle.coe_mul]

theorem tracePsi_continuous (p : KPFinitePlace F) : Continuous (tracePsi p) :=
  continuous_subtype_val.comp (ResidueTrace.continuous_localTraceCharacter p)

theorem tracePsi_unitary (p : KPFinitePlace F) (x : p.adicCompletion F) :
    ‖tracePsi p x‖ = 1 := Circle.norm_coe _

theorem tracePsi_conductorZero (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A)
    (π : (valuation (p.val.adicCompletion F)).integer) (hπ : Irreducible π) :
    KPExteriorUnitShellIntegrals.ConductorZero (tracePsi p.val) π := by
  let J := LocalFiniteSumCompatibility.integerRingEquiv (UnitCovarianceCompletion.localPrime p)
  constructor
  · intro u
    have ht := (R.traceBad p.val p.property (1 : p.val.adicCompletion F)).mpr (by simp)
    have h := ht (J.symm u)
    change (ResidueTrace.localTraceCharacter p.val (u : p.val.adicCompletion F) : ℂ) = 1
    have hu : ((J.symm u : p.val.adicCompletionIntegers F) : p.val.adicCompletion F) =
        (u : p.val.adicCompletion F) := by
      exact congrArg (fun a : (valuation (p.val.adicCompletion F)).integer =>
        (a : p.val.adicCompletion F)) (J.apply_symm_apply u)
    simpa only [one_mul, hu, Circle.coe_one] using congrArg (fun z : Circle => (z : ℂ)) h
  · have hπ0 : (π : p.val.adicCompletion F) ≠ 0 := by
      intro h
      exact hπ.ne_zero (Subtype.ext h)
    have hnot : (π : p.val.adicCompletion F)⁻¹ ∉ p.val.adicCompletionIntegers F := by
      intro hh
      let z := J ⟨(π : p.val.adicCompletion F)⁻¹, hh⟩
      apply hπ.not_isUnit
      apply isUnit_iff_exists_inv.mpr
      refine ⟨z, ?_⟩
      apply Subtype.ext
      exact mul_inv_cancel₀ hπ0
    have hex : ∃ o : p.val.adicCompletionIntegers F,
        ResidueTrace.localTraceCharacter p.val
          ((π : p.val.adicCompletion F)⁻¹ * (o : p.val.adicCompletion F)) ≠ 1 :=
      not_forall.mp (fun h => hnot ((R.traceBad p.val p.property _).mp h))
    obtain ⟨o, ho⟩ := hex
    refine ⟨J o, ?_⟩
    intro h
    apply ho
    apply Subtype.ext
    exact h

def residueChi (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) :
    MulChar (IsLocalRing.ResidueField (valuation (p.val.adicCompletion F)).integer) ℂ :=
  MulChar.ofUnitHom
    ((LocalFiniteSums.chi (σ := R.σ) (UnitCovarianceCompletion.localPrime p)).toUnitHom.comp
      (Units.map (LocalFiniteSumCompatibility.cftResidueEquiv
        (UnitCovarianceCompletion.localPrime p)).symm.toMonoidHom))

theorem residueChi_unitCharacter (R : PrincipalMellin.ActualRecipe S η)
    (hR : MomentSources.RootAligned R) (p : ThetaBranch.ExteriorPrime R.A)
    (u : KPHilbert.LocalIntegerUnits F p.val) :
    KPExteriorUnitShellIntegrals.unitCharacter (residueChi R p) u =
      KPExteriorUnitShellIntegrals.arithmeticUnitCharacter F R.A.zeta12
        R.A.primitive_zeta12 p.val (exterior_good_six p) u := by
  let E := LocalFiniteSumCompatibility.cftResidueEquiv (UnitCovarianceCompletion.localPrime p)
  let r := Units.map (IsLocalRing.residue (valuation (p.val.adicCompletion F)).integer).toMonoidHom u
  let q := Units.map E.symm.toMonoidHom r
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (q : R.A.R ⧸ R.A.extendIdeal
    (LocalFiniteSums.primeIdeal (UnitCovarianceCompletion.localPrime p)))
  have he : IsLocalRing.residue _ u.val = E (Ideal.Quotient.mk _ x) := by
    rw [hx]
    exact (E.apply_symm_apply r.val).symm
  have hh := UnitCovarianceCompletion.chi_eq_residueSixCharacter_of_residue
    (σ := R.σ) (UnitCovarianceCompletion.localPrime p) x u he
  have hr := hR (KPHilbert.residueSixCharacter F p.val R.A.zeta12 R.A.primitive_zeta12
    (exterior_good_six p) u)
  have hroot : KPLocalCover.coefficientEmbedding F S.zeta12 S.primitive_zeta12 =
      KPLocalCover.coefficientEmbedding F R.A.zeta12 R.A.primitive_zeta12 := by
    congr 1
    exact R.sameRoot.symm
  rw [hroot] at hr
  unfold KPExteriorUnitShellIntegrals.unitCharacter residueChi
  change MulChar.ofUnitHom _ r.val = _
  rw [MulChar.ofUnitHom_coe]
  change LocalFiniteSums.chi (σ := R.σ) (UnitCovarianceCompletion.localPrime p) q.val = _
  rw [← hx]
  exact hh.trans hr

theorem exterior_tame_char (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) :
    ringChar (KPTameCompact.O F p.val ⧸ KPTameCompact.p F p.val) ≠ 3 :=
  fun h => exterior_not_bad p (Or.inr h)

theorem negativeGenerator_integer_irreducible (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) :
    ∃ π : (valuation (p.val.adicCompletion F)).integer, Irreducible π ∧
      (π : p.val.adicCompletion F) = -(ThetaExpansion.exteriorCompletionGenerator R p : p.val.adicCompletion F) := by
  obtain ⟨π, hi, hp⟩ := allowedGenerator_integer_irreducible R p
  have hneg : Associated π (-π) := ⟨-1, by simp⟩
  exact ⟨-π, hneg.irreducible_iff.mp hi, congrArg Neg.neg hp⟩

def residueEquiv (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) :
    DHCubic.Residue F p.val ≃+*
      IsLocalRing.ResidueField (valuation (p.val.adicCompletion F)).integer :=
  (ArithGaussCRT.exteriorQuotientEquiv R.A (ThetaBranch.primeIdeal R.A p)).trans
    (LocalFiniteSumCompatibility.cftResidueEquiv (UnitCovarianceCompletion.localPrime p))

theorem residueEquiv_mk (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) (t : 𝓞 F) :
    residueEquiv R p (Ideal.Quotient.mk p.val.asIdeal t) =
      IsLocalRing.residue _ (LocalFiniteSumCompatibility.integerRingEquiv
        (UnitCovarianceCompletion.localPrime p)
          (LocalFiniteSumCompatibility.integerMap (UnitCovarianceCompletion.localPrime p)
            (algebraMap (𝓞 F) R.A.R t))) := by
  exact LocalFiniteSumCompatibility.cftResidueEquiv_mk _ _

def residuePsi (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) :
    AddChar (IsLocalRing.ResidueField (valuation (p.val.adicCompletion F)).integer) ℂ :=
  (MomentSources.Characters.psi R p).compAddMonoidHom (residueEquiv R p).symm.toAddMonoidHom

theorem residuePsi_trace (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A)
    (π : (valuation (p.val.adicCompletion F)).integer) (hπ : Irreducible π)
    (hp : (π : p.val.adicCompletion F) = -(ThetaExpansion.exteriorCompletionGenerator R p : p.val.adicCompletion F))
    (u : (valuation (p.val.adicCompletion F)).integer) :
    residuePsi R p (IsLocalRing.residue _ u) =
      tracePsi p.val ((π : p.val.adicCompletion F)⁻¹ * (u : p.val.adicCompletion F)) := by
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective
    ((residueEquiv R p).symm (IsLocalRing.residue _ u))
  let a := LocalFiniteSumCompatibility.integerRingEquiv
    (UnitCovarianceCompletion.localPrime p)
      (LocalFiniteSumCompatibility.integerMap (UnitCovarianceCompletion.localPrime p)
        (algebraMap (𝓞 F) R.A.R t))
  have ha : (a : p.val.adicCompletion F) = algebraMap (𝓞 F) (p.val.adicCompletion F) t := by
    exact IsScalarTower.algebraMap_apply (𝓞 F) F (p.val.adicCompletion F) t |>.symm
  have hr : IsLocalRing.residue _ a = IsLocalRing.residue _ u := by
    rw [← residueEquiv_mk R p t, ht, RingEquiv.apply_symm_apply]
  have hphase := KPExteriorUnitShellIntegrals.residuePhase_lift_independent
    π hπ (tracePsi p.val) (tracePsi_continuous p.val) (tracePsi_unitary p.val)
    (tracePsi_conductorZero R p π hπ) a u hr
  change MomentSources.Characters.psi R p ((residueEquiv R p).symm (IsLocalRing.residue _ u)) = _
  rw [← ht, TraceHaarTransport.divided_negative_trace R p t, ← hphase]
  apply congrArg (fun x : p.val.adicCompletion F => (ResidueTrace.localTraceCharacter p.val x : ℂ))
  rw [hp, ha, map_neg, map_div₀, ← IsScalarTower.algebraMap_apply (𝓞 F) F]
  change -(algebraMap (𝓞 F) (p.val.adicCompletion F) t /
    (ThetaExpansion.exteriorCompletionGenerator R p : p.val.adicCompletion F)) =
      (-(ThetaExpansion.exteriorCompletionGenerator R p : p.val.adicCompletion F))⁻¹ *
        algebraMap (𝓞 F) (p.val.adicCompletion F) t
  simp [div_eq_mul_inv, mul_comm]

theorem residueChi_transport (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) (x : DHCubic.Residue F p.val) :
    residueChi R p (residueEquiv R p x) = ThetaBranch.residueCharacter R.A R.σ p x := by
  rw [NormalizedProbe.principal_prime_residueCharacter_transport]
  by_cases hx : x = 0
  · subst x
    rw [map_zero (residueEquiv R p), map_zero (ArithGaussCRT.exteriorQuotientEquiv R.A (ThetaBranch.primeIdeal R.A p))]
    exact (residueChi R p).map_zero.trans (LocalFiniteSums.chi (σ := R.σ) (UnitCovarianceCompletion.localPrime p)).map_zero.symm
  · let E := ArithGaussCRT.exteriorQuotientEquiv R.A (ThetaBranch.primeIdeal R.A p)
    let u := Units.map E.toMonoidHom (Units.mk0 x hx)
    let e := LocalFiniteSumCompatibility.cftResidueEquiv (UnitCovarianceCompletion.localPrime p)
    let r := Units.map e.toMonoidHom u
    change residueChi R p r.val = LocalFiniteSums.chi (σ := R.σ)
      (UnitCovarianceCompletion.localPrime p) u.val
    unfold residueChi
    rw [MulChar.ofUnitHom_coe]
    change LocalFiniteSums.chi (σ := R.σ) (UnitCovarianceCompletion.localPrime p)
      (e.symm (e u.val)) = _
    rw [e.symm_apply_apply]

@[simp] theorem residuePsi_transport (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) (x : DHCubic.Residue F p.val) :
    residuePsi R p (residueEquiv R p x) = MomentSources.Characters.psi R p x := by
  change MomentSources.Characters.psi R p ((residueEquiv R p).symm (residueEquiv R p x)) = _
  rw [RingEquiv.symm_apply_apply]

theorem gauss_two_transport (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A)
    [Fintype (IsLocalRing.ResidueField (valuation (p.val.adicCompletion F)).integer)] :
    gaussSum (residueChi R p ^ 2) (residuePsi R p) =
      gaussSum (ThetaBranch.residueCharacter R.A R.σ p ^ 2) (MomentSources.Characters.psi R p) := by
  unfold gaussSum
  symm
  apply Fintype.sum_equiv (residueEquiv R p).toEquiv
  intro x
  simp only [MulChar.pow_apply' _ (by norm_num : (2 : ℕ) ≠ 0)]
  change _ = residueChi R p (residueEquiv R p x) ^ 2 * residuePsi R p (residueEquiv R p x)
  rw [residueChi_transport, residuePsi_transport]

end DedekindZetaZeroFree.ExteriorWhittakerValues.ShellArithmetic

end

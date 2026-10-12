module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.PlacesAndCompletions
public import DedekindZetaZeroFree.Theta.Whittaker.ComplexRootDerivativeVectors
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.Cubic.ForwardExceptionalImage

@[expose] public section

section

noncomputable section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPInterface.ActualFiniteOutputSteps
open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPLocalStoneVonNeumann KPLocalJacquetImage
open KPRankOneShellRepair
variable {F : Type} [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : HeightOneSpectrum (RingOfIntegers F))
variable (S : CanonicalFiniteInducingData F ζ hζ v) (P : Polarization S.heisenberg)
variable (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure]
variable (hμ : μ ((valuation (LocalField F v)).integer : Set (LocalField F v)) = 1)

private theorem residue_card : residueCardinality (LocalField F v) = v.asIdeal.absNorm := by
  let e : v.adicCompletionIntegers F ≃+* (valuation (LocalField F v)).integer := by
    letI : (Valued.v : Valuation (LocalField F v) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    have he := (Valuation.isEquiv_iff_valuationSubring _ _).mp
      (ValuativeRel.isEquiv (Valued.v : Valuation (LocalField F v)
        (WithZero (Multiplicative ℤ))) (valuation (LocalField F v)))
    exact RingEquiv.restrict (RingEquiv.refl _) _ _ (fun x => by
      change x ∈ (Valued.v : Valuation (LocalField F v) (WithZero (Multiplicative ℤ))).valuationSubring ↔
        x ∈ (valuation (LocalField F v)).valuationSubring
      rw [he])
  let er := (GlobalClassFieldTheory.ClassFieldAxiom.ringOfIntegersQuotientEquivAdicResidueField v).trans
    (IsLocalRing.ResidueField.mapEquiv e)
  unfold residueCardinality
  rw [← Nat.card_congr er.toEquiv, Ideal.absNorm_apply]
  rfl

private theorem normalized_valuation (x : LocalField F v) :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v)
      (valuation (LocalField F v) x) = Valued.v x := by
  let ν : Valuation (LocalField F v) (WithZero (Multiplicative ℤ)) := Valued.v
  letI : ν.Compatible := Valuation.Compatible.ofValuation _
  let e := (ValuativeRel.ValueGroupWithZero.orderMonoidIso ν).trans
    (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt ν)
  have hsame : e = IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v) := by
    let f := e.symm.trans (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F v))
    have hf : f = OrderMonoidIso.refl _ := by
      have h := Subsingleton.elim (OrderMonoidIso.withZero.symm f)
        (OrderMonoidIso.refl (Multiplicative ℤ))
      have hh := congrArg OrderMonoidIso.withZero h
      exact (show f = OrderMonoidIso.withZero (OrderMonoidIso.refl (Multiplicative ℤ)) by simpa using hh).trans
        (by ext x; cases x <;> rfl)
    ext a
    have h := congrArg (fun k => k (e a)) hf
    simpa [f] using h.symm
  rw [← hsame]
  change Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt ν
    (ValuativeRel.ValueGroupWithZero.orderMonoidIso ν (valuation (LocalField F v) x)) = _
  rw [ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀]
  exact Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
    (v.valuedAdicCompletion_surjective F) x

set_option maxHeartbeats 8000000 in
private theorem actual_relation (π : (LocalField F v)ˣ)
    (hπ : Valued.v π.val = WithZero.exp (-1 : ℤ))
    (φ : actualCanonicalImageModule F ζ hζ v S P μ hμ) :
    actualCanonicalImageRepresentation F ζ hζ v S P μ hμ
      (KPPGLLocalCover.A F ζ hζ (Sum.inr v) (π ^ 3)) φ -
      (v.asIdeal.absNorm : ℂ)⁻¹ • φ ∈
        jacquetRelations S.borel (actualCanonicalImageRepresentation F ζ hζ v S P μ hμ) := by
  obtain ⟨e⟩ := actual_forward_image_jacquet_factor F ζ hζ v S P μ hμ
  let ρ := actualCanonicalImageRepresentation F ζ hζ v S P μ hμ
  let q := Representation.Coinvariants.mk (ρ.comp (root S.borel))
  apply (Representation.Coinvariants.mk_eq_zero _).mp
  have hweight := (KPJacquetExceptionalFactorSeparation.exceptional_cube_weights S.borel P π
    (by rw [normalized_valuation]; exact hπ)).2
  have h := congrArg (fun f => f (q φ)) (e.toIntertwiningMap.isIntertwining' (S.borel.cubeLift π))
  change e (q (ρ (S.borel.torus (S.borel.cubeLift π)) φ)) =
    KPJacquetExceptionalFactorSeparation.factorMinus S.borel P (S.borel.cubeLift π) (e (q φ)) at h
  have hv := hweight (e (q φ))
  have hc := residue_card (F := F) v
  simp only [hc, zpow_neg_one] at hv
  have ht : (S.borel.torus (S.borel.cubeLift π) : ActualCover F ζ hζ v) =
      KPPGLLocalCover.A F ζ hζ (Sum.inr v) (π ^ 3) :=
    (S.torus_full _).trans (S.cube_actual π)
  have hq : q (ρ (KPPGLLocalCover.A F ζ hζ (Sum.inr v) (π ^ 3)) φ) =
      (v.asIdeal.absNorm : ℂ)⁻¹ • q φ := by
    apply e.injective
    simpa only [map_smul, Representation.Equiv.toLinearEquiv_apply,
      Representation.Equiv.coe_toIntertwiningMap, ht] using h.trans hv
  have hz : q (ρ (KPPGLLocalCover.A F ζ hζ (Sum.inr v) (π ^ 3)) φ -
      (v.asIdeal.absNorm : ℂ)⁻¹ • φ) = 0 := by
    simp only [map_sub, map_smul, hq, sub_self]
  exact hz

private theorem actual_differences_eq :
    KPFiniteLocal.ordinaryDifferences (actualCanonicalImageRepresentation F ζ hζ v S P μ hμ)
      (show AddChar (LocalField F v) (ActualCover F ζ hζ v) from
        { toFun := KPPGLLocalCover.N F ζ hζ (Sum.inr v)
          map_zero_eq_one' := by simp [KPPGLLocalCover.N, KPStandardLocalRootLifts.N_zero]
          map_add_eq_mul' := KPPGLLocalCover.N_add F ζ hζ (Sum.inr v) }) =
      jacquetRelations S.borel (actualCanonicalImageRepresentation F ζ hζ v S P μ hμ) := by
  unfold KPFiniteLocal.ordinaryDifferences jacquetRelations Representation.Coinvariants.ker
  congr 1
  ext z
  have hroot (x : Multiplicative (LocalField F v)) :
      root S.borel x = KPPGLLocalCover.N F ζ hζ (Sum.inr v) x.toAdd :=
    (S.openCell P).upper_eq x.toAdd
  constructor
  · rintro ⟨x, φ, rfl⟩
    refine ⟨(Multiplicative.ofAdd x, φ), ?_⟩
    simp only [MonoidHom.comp_apply, hroot]
    rfl
  · rintro ⟨⟨x, φ⟩, rfl⟩
    refine ⟨x.toAdd, φ, ?_⟩
    simp only [MonoidHom.comp_apply, hroot]
    rfl

 def actualN : AddChar (LocalField F v) (ActualCover F ζ hζ v) where
  toFun := KPPGLLocalCover.N F ζ hζ (Sum.inr v)
  map_zero_eq_one' := by simp [KPPGLLocalCover.N, KPStandardLocalRootLifts.N_zero]
  map_add_eq_mul' := KPPGLLocalCover.N_add F ζ hζ (Sum.inr v)

set_option maxHeartbeats 8000000 in

theorem actual_small_norm_decay_canonical
    (ψ : ContinuousAddChar (LocalField F v))
    (ell : CanonicalSmoothModule (actualCanonicalImageModule F ζ hζ v S P μ hμ) →L[ℂ] ℂ)
    (hell : ell ∈ localWhittakerSpace (Multiplicative (LocalField F v))
      (CanonicalSmoothModule (actualCanonicalImageModule F ζ hζ v S P μ hμ))
      ((canonicalSmoothRepresentation (actualCanonicalImageRepresentation F ζ hζ v S P μ hμ)).comp
        (root S.borel)) ψ.toAddChar.toMonoidHom)
    (φ : CanonicalSmoothModule (actualCanonicalImageModule F ζ hζ v S P μ hμ))
    (δ : ℝ) (hδ : 0 < δ) (hδthird : δ < (1 / 3 : ℝ)) :
    ∃ B : ℝ, 0 < B ∧ ∀ y : (LocalField F v)ˣ, 0 < ‖y.val‖ → ‖y.val‖ ≤ 1 →
      ‖ell (canonicalSmoothRepresentation (actualCanonicalImageRepresentation F ζ hζ v S P μ hμ)
        (KPPGLLocalCover.A F ζ hζ (Sum.inr v) y) φ)‖ ≤ B * Real.rpow ‖y.val‖ δ := by
  let ρ := canonicalSmoothRepresentation (actualCanonicalImageRepresentation F ζ hζ v S P μ hμ)
  let n := actualN ζ hζ v
  let a := KPPGLLocalCover.A F ζ hζ (Sum.inr v)
  obtain ⟨p, hp⟩ := v.valuation_exists_uniformizer F
  have hpne : p ≠ 0 := by
    intro he
    rw [he, map_zero] at hp
    exact WithZero.coe_ne_zero hp.symm
  let π : (LocalField F v)ˣ := Units.mk0 (algebraMap F (LocalField F v) p)
    ((algebraMap F (LocalField F v)).injective.ne hpne)
  have hπ : Valued.v π.val = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap F (v.adicCompletion F) p) = _
    exact (v.valuedAdicCompletion_eq_valuation' p).trans hp
  have hπnorm : ‖π.val‖ = (v.asIdeal.absNorm : ℝ)⁻¹ := by
    rw [FinitePlace.norm_def,
      WithZeroMulInt.toNNReal_neg_apply _ (by simpa only [ne_eq, Valuation.zero_iff] using π.ne_zero),
      NNReal.coe_zpow, hπ, WithZero.log_exp]
    simp
  have hJ : ∀ η : CanonicalSmoothModule (actualCanonicalImageModule F ζ hζ v S P μ hμ),
      ((ρ (a (π ^ 3)) - (v.asIdeal.absNorm : ℂ)⁻¹ • LinearMap.id) *
        (ρ (a (π ^ 3)) - ((v.asIdeal.absNorm : ℂ) ^ 2)⁻¹ • LinearMap.id) : Module.End ℂ _) η ∈
      KPFiniteLocal.ordinaryDifferences ρ n := by
    intro η
    have he := actual_differences_eq ζ hζ v S P μ hμ
    change KPFiniteLocal.ordinaryDifferences ρ n = _ at he
    rw [he]
    exact actual_relation ζ hζ v S P μ hμ π hπ _
  let χ : AddChar (LocalField F v) Circle :=
    { toFun x := ⟨ψ.toAddChar x, mem_sphere_zero_iff_norm.mpr (ψ.unitary x)⟩
      map_zero_eq_one' := by apply Subtype.ext; exact ψ.toAddChar.map_zero_eq_one
      map_add_eq_mul' := by intro x y; apply Subtype.ext; exact ψ.toAddChar.map_add_eq_mul x y }
  have hn : Continuous n := by
    exact (KPPGLLocalCover.finite_lifts_continuous F ζ hζ v
      (KPAdelicCoverRestrictedProduct.depth F ζ hζ v)
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ v)).1
  have ha : Continuous a := by
    exact (KPPGLLocalCover.finite_lifts_continuous F ζ hζ v
      (KPAdelicCoverRestrictedProduct.depth F ζ hζ v)
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ v)).2.2
  have hconj : ∀ (y : (LocalField F v)ˣ) (x : LocalField F v),
      a y * n x = n (y.val * x) * a y := by
    intro y x
    have hh := (KPCorrectedBruhatLifts.quotient_upper_diagonal F ζ hζ (Sum.inr v) (y.val * x) y).symm
    rw [mul_div_cancel_left₀ x y.ne_zero] at hh
    exact hh
  have hcube : ∀ y : (LocalField F v)ˣ, a (y * π ^ 3) = a y * a (π ^ 3) := by
    intro y
    have hs : KPHilbert.B3 F ζ hζ (Sum.inr v) y (π ^ 3) = 1 := by
      exact ((KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.2.2.1 y π).2
    have hh := KPPGLLocalCover.A_mul F ζ hζ (Sum.inr v) y (π ^ 3)
    simp only [hs, one_pow, map_one, one_mul] at hh
    exact hh.symm
  exact KPFiniteLocal.generic_fixed_vector_small_norm v ρ
    (smoothRepresentation_orbit_isLocallyConstant _
      (actualCanonicalImage_smooth F ζ hζ v S P μ hμ)) n hn a ha hconj π hπnorm hcube hJ χ
    (ψ.continuous_toFun.subtype_mk _) ell.toLinearMap
    (fun x η => by
      have h := hell (Multiplicative.ofAdd x) η
      have hr := (S.openCell P).upper_eq x
      change ell (ρ (S.borel.upperRoot (Multiplicative.ofAdd x)) η) = _ at h
      rw [hr] at h
      exact h) φ δ hδ hδthird

end ActualFiniteOutputSteps
end KPInterface
end DedekindZetaZeroFree
end
end

end

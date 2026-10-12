module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalCompactHolomorphicModel

@[expose] public section

namespace DedekindZetaZeroFree.KPJacquetExceptionalFactorSeparation

open scoped Valued MonoidAlgebra
open ValuativeRel KPLocalStoneVonNeumann KPLocalPrincipalSeries

noncomputable section

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

abbrev factorPlus (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T) :
    Representation ℂ H (InducedModule P) :=
  (inducingAction A P .plus 0).comp A.torus

abbrev factorMinus (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T) :
    Representation ℂ H (InducedModule P) :=
  (inducingAction A P .minus 0).comp A.torus

theorem residue_cardinality_gt_one : 1 < residueCardinality K := by
  exact Finite.one_lt_card

 def scalarSubrepresentationOrderIso
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ σ : Representation ℂ H V) (c : H → ℂ)
    (hc : ∀ h, c h ≠ 0) (he : ∀ h v, σ h v = c h • ρ h v) :
    Subrepresentation σ ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun h v hv => by
    have hm := S.toSubmodule.smul_mem (c h)⁻¹ (S.apply_mem_toSubmodule h hv)
    simpa [he, smul_smul, hc] using hm⟩
  invFun S := ⟨S.toSubmodule, fun h v hv => by
    rw [he]
    exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule h hv)⟩
  left_inv S := by ext; rfl
  right_inv S := by ext; rfl
  map_rel_iff' := by rfl

private theorem factor_action (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (ε : Sign) (h : H) (v : InducedModule P) :
    ((inducingAction A P ε 0).comp A.torus) h v =
      deltaHalf A (A.torus h) •
        (match ε with | .plus => tau P h v | .minus => weylConjugate P A.weyl h v) := by
  cases ε
  · change inducingScalar A 0 (A.torus h) • tau P (A.retract (A.torus h)) v = _
    simp [inducingScalar, normPower, A.retract_torus]
  · change inducingScalar A 0 (A.torus h) •
      weylConjugate P A.weyl (A.retract (A.torus h)) v = _
    simp [inducingScalar, normPower, A.retract_torus]

theorem exceptional_factors_simple
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T) :
    Nontrivial (InducedModule P) ∧
      (factorPlus A P).IsIrreducible ∧ (factorMinus A P).IsIrreducible := by
  have hirr := tau_irreducible T P
  letI : (tau P).IsIrreducible := hirr
  have hn : Nontrivial (InducedModule P) := by
    haveI : IsSimpleModule ℂ[H] (tau P).asModule := inferInstance
    exact IsSimpleModule.nontrivial ℂ[H] (tau P).asModule
  have hc : ∀ h : H, deltaHalf A (A.torus h) ≠ 0 := by
    intro h
    exact Complex.exp_ne_zero _
  have hw := (weyl_conjugate_properties T P A.weyl A.weylCenter
    A.weylCenter_coe).2.2.1
  exact ⟨hn,
    (scalarSubrepresentationOrderIso (tau P) (factorPlus A P)
      (fun h => deltaHalf A (A.torus h)) hc (factor_action A P .plus)).isSimpleOrder_iff.mpr hirr,
    (scalarSubrepresentationOrderIso (weylConjugate P A.weyl) (factorMinus A P)
      (fun h => deltaHalf A (A.torus h)) hc (factor_action A P .minus)).isSimpleOrder_iff.mpr hw⟩

theorem exceptional_cube_weights
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T) (π : Kˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (π : K)) = WithZero.exp (-1 : ℤ)) :
    (∀ v : InducedModule P, factorPlus A P (A.cubeLift π : H) v =
      ((residueCardinality K : ℂ) ^ (-2 : ℤ)) • v) ∧
    (∀ v : InducedModule P, factorMinus A P (A.cubeLift π : H) v =
      ((residueCardinality K : ℂ) ^ (-1 : ℤ)) • v) := by
  obtain ⟨hp, hd, hm⟩ := uniformizer_weights A π hπ
  have hq : 0 < (residueCardinality K : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (residue_cardinality_gt_one (K := K)))
  have hw := (weyl_conjugate_properties T P A.weyl A.weylCenter
    A.weylCenter_coe).2.2.2.1
  constructor
  · intro v
    rw [factor_action A P .plus]
    change deltaHalf A (A.torus (A.cubeLift π : H)) • tau P (A.cubeLift π : H) v = _
    rw [tau_hasCentralCharacter T P]
    change deltaHalf A (A.torus (A.cubeLift π : H)) • ((T.ω (A.cubeLift π) : ℂ) • v) = _
    rw [hp, hd, smul_smul]
    congr 1
    rw [← Complex.ofReal_mul, ← Real.rpow_add hq]
    norm_num
  · intro v
    rw [factor_action A P .minus]
    change deltaHalf A (A.torus (A.cubeLift π : H)) •
      weylConjugate P A.weyl (A.cubeLift π : H) v = _
    rw [hw]
    change deltaHalf A (A.torus (A.cubeLift π : H)) •
      ((T.ω (A.weylCenter (A.cubeLift π)) : ℂ) • v) = _
    rw [hm, hd, smul_smul]
    congr 1
    rw [← Complex.ofReal_mul, ← Real.rpow_add hq]
    norm_num
    simp [Real.rpow_neg_one]

end

end DedekindZetaZeroFree.KPJacquetExceptionalFactorSeparation

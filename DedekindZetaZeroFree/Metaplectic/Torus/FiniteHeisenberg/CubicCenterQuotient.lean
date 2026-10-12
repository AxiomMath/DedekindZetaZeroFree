module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteTensorRealizations

@[expose] public section

open scoped NumberField Classical

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.TorusFiniteCenterQuotient

noncomputable section

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open KPGlobalTorusFiniteStages

variable (C : CompatibleModelData F ζ hζ) (L : Level F ζ hζ C)

theorem diagonal_formula (t : KPGlobalTorusFunctionData.ordinaryTorus F) :
    KPGlobalCubicIdelePairing.diagonalPGL F (KPGlobalTorusFunctionData.torusRatio F t) = t.val := by
  let A := Classical.choose t.property
  have hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A = t.val ∧
      A 1 0 = 0 ∧ A 0 1 = 0 := Classical.choose_spec t.property
  let u := (KPGlobalTorusFunctionData.diagonal_entries_units F A hA.2.1 hA.2.2).1.unit
  let w := (KPGlobalTorusFunctionData.diagonal_entries_units F A hA.2.1 hA.2.2).2.unit
  have hu : (u : KPAdelicCoverRestrictedProduct.Adeles F) = A 0 0 := IsUnit.unit_spec _
  have hw : (w : KPAdelicCoverRestrictedProduct.Adeles F) = A 1 1 := IsUnit.unit_spec _
  have heq : A = KPGlobalCubicIdelePairing.diagonalHom F (u * w⁻¹) *
      Matrix.GeneralLinearGroup.scalar (Fin 2) w := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix,
        Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar, hu, hA.2.1, hA.2.2]
    exact hw.symm
  change QuotientGroup.mk' _ (KPGlobalCubicIdelePairing.diagonalHom F (u * w⁻¹)) = t.val
  rw [← hA.1, heq]
  have hs : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) w) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨w, rfl⟩
  rw [(QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).map_mul, hs, mul_one]

def torusPullbackBridge : KPGlobalTorusFunctionData.E F ζ hζ →* KPGlobalCubicIdelePairing.E F ζ hζ where
  toFun e := ⟨(e.val, KPGlobalTorusFunctionData.p F ζ hζ e),
    (diagonal_formula F ⟨_, e.property⟩).symm⟩
  map_one' := by apply Subtype.ext; exact Prod.ext rfl (map_one _)
  map_mul' x y := by apply Subtype.ext; exact Prod.ext rfl (map_mul _ _ _)

private theorem torusPullbackBridge_injective :
    Function.Injective (torusPullbackBridge F ζ hζ) := by
  intro x y h
  exact Subtype.ext (congrArg (fun t : KPGlobalCubicIdelePairing.E F ζ hζ => t.val.1) h)

private theorem commute_iff_beta (x y : KPGlobalTorusFunctionData.E F ζ hζ) :
    Commute x y ↔ KPGlobalCubicIdelePairing.beta3 F ζ hζ
      (KPGlobalProductPolarizationCharacter.pD F ζ hζ x) (KPGlobalProductPolarizationCharacter.pD F ζ hζ y) = 1 := by
  have h := KPGlobalCubicIdelePairing.commutator_annihilators F ζ hζ
    (torusPullbackBridge F ζ hζ x) (torusPullbackBridge F ζ hζ y)
  constructor
  · intro hc
    exact h.mp (hc.map (torusPullbackBridge F ζ hζ))
  · intro hb
    apply torusPullbackBridge_injective F ζ hζ
    simpa only [map_mul] using (h.mpr hb).eq

def phaseInclusion : phaseGroup F ζ hζ C L →* stageDomain F ζ hζ C L :=
  Subgroup.inclusion (phase_inside_domain F ζ hζ C L)

def phaseInDomain : Subgroup (stageDomain F ζ hζ C L) :=
  (phaseGroup F ζ hζ C L).comap (stageDomain F ζ hζ C L).subtype

def phaseKernel : Subgroup (stageDomain F ζ hζ C L) :=
  (phaseCharacter F ζ hζ C L).ker.map (phaseInclusion F ζ hζ C L)

theorem phaseKernel_le_phaseInDomain :
    phaseKernel F ζ hζ C L ≤ phaseInDomain F ζ hζ C L := by
  rintro x ⟨k, hk, rfl⟩
  exact k.property

def domainProjection : stageDomain F ζ hζ C L →* symplecticQuotient F ζ hζ C L :=
  (QuotientGroup.mk' _).comp ((pD F ζ hζ).restrict (fun _ hx => hx))

theorem domainProjection_kernel :
    (domainProjection F ζ hζ C L).ker = phaseInDomain F ζ hζ C L := by
  ext x
  change QuotientGroup.mk (⟨pD F ζ hζ x.val, x.property⟩ : annihilator F ζ hζ L.K) = 1 ↔
    pD F ζ hζ x.val ∈ L.K
  exact QuotientGroup.eq_one_iff _

theorem phaseInclusion_central (k : phaseGroup F ζ hζ C L) (x : stageDomain F ζ hζ C L) :
    Commute (phaseInclusion F ζ hζ C L k) x := by
  apply Subtype.ext
  exact ((commute_iff_beta F ζ hζ x.val k.val).mpr (x.property _ k.property)).symm.eq

theorem phaseInDomain_central : phaseInDomain F ζ hζ C L ≤ Subgroup.center (stageDomain F ζ hζ C L) := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  exact (phaseInclusion_central F ζ hζ C L ⟨x.val, hx⟩ y).symm.eq

theorem phaseKernel_central : phaseKernel F ζ hζ C L ≤ Subgroup.center (stageDomain F ζ hζ C L) :=
  (phaseKernel_le_phaseInDomain F ζ hζ C L).trans (phaseInDomain_central F ζ hζ C L)

instance phaseKernel_normal : (phaseKernel F ζ hζ C L).Normal :=
  Subgroup.normal_of_le_center (phaseKernel_central F ζ hζ C L)

abbrev H := stageDomain F ζ hζ C L ⧸ phaseKernel F ζ hζ C L

def center : Subgroup (H F ζ hζ C L) :=
  (phaseInDomain F ζ hζ C L).map (QuotientGroup.mk' _)

def projection : H F ζ hζ C L →* symplecticQuotient F ζ hζ C L :=
  QuotientGroup.lift _ (domainProjection F ζ hζ C L) (by
    rw [domainProjection_kernel]
    exact phaseKernel_le_phaseInDomain F ζ hζ C L)

theorem projection_kernel : (projection F ζ hζ C L).ker = center F ζ hζ C L := by
  ext h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective h
  constructor
  · intro hx
    apply Subgroup.mem_map.mpr
    refine ⟨x, ?_, rfl⟩
    rw [← domainProjection_kernel]
    exact hx
  · rintro ⟨y, hy, he⟩
    have hy' : domainProjection F ζ hζ C L y = 1 := by
      change y ∈ (domainProjection F ζ hζ C L).ker
      rw [domainProjection_kernel]; exact hy
    have hh := congrArg (projection F ζ hζ C L) he
    change domainProjection F ζ hζ C L y = domainProjection F ζ hζ C L x at hh
    exact hh.symm.trans hy'

def phaseToCenter : phaseGroup F ζ hζ C L →* center F ζ hζ C L :=
  { toFun := fun k => ⟨QuotientGroup.mk (phaseInclusion F ζ hζ C L k),
      Subgroup.mem_map.mpr ⟨phaseInclusion F ζ hζ C L k, k.property, rfl⟩⟩
    map_one' := by apply Subtype.ext; exact map_one ((QuotientGroup.mk' _).comp (phaseInclusion F ζ hζ C L))
    map_mul' := by intro x y; apply Subtype.ext; exact map_mul ((QuotientGroup.mk' _).comp (phaseInclusion F ζ hζ C L)) x y }

theorem phaseToCenter_surjective : Function.Surjective (phaseToCenter F ζ hζ C L) := by
  rintro ⟨z, x, hx, rfl⟩
  exact ⟨⟨x.val, hx⟩, rfl⟩

theorem phaseToCenter_kernel :
    (phaseToCenter F ζ hζ C L).ker = (phaseCharacter F ζ hζ C L).ker := by
  ext k
  change (phaseToCenter F ζ hζ C L k = 1) ↔ phaseCharacter F ζ hζ C L k = 1
  rw [Subtype.ext_iff]
  change QuotientGroup.mk (phaseInclusion F ζ hζ C L k) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨k', hk', he⟩
    have he' : k' = k := (Subgroup.inclusion_injective _) he
    rwa [he'] at hk'
  · intro hk
    exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩

def centerCharacter : center F ζ hζ C L →* ℂˣ :=
  (phaseToCenter F ζ hζ C L).liftOfSurjective (phaseToCenter_surjective F ζ hζ C L)
    ⟨phaseCharacter F ζ hζ C L, by rw [phaseToCenter_kernel]⟩

theorem centerCharacter_phase (k : phaseGroup F ζ hζ C L) :
    centerCharacter F ζ hζ C L (phaseToCenter F ζ hζ C L k) = phaseCharacter F ζ hζ C L k := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem centerCharacter_faithful : Function.Injective (centerCharacter F ζ hζ C L) := by
  intro x y he
  obtain ⟨k, rfl⟩ := phaseToCenter_surjective F ζ hζ C L x
  obtain ⟨k', rfl⟩ := phaseToCenter_surjective F ζ hζ C L y
  rw [centerCharacter_phase, centerCharacter_phase] at he
  apply Subtype.ext
  change QuotientGroup.mk (phaseInclusion F ζ hζ C L k) = QuotientGroup.mk (phaseInclusion F ζ hζ C L k')
  apply QuotientGroup.eq.mpr
  apply Subgroup.mem_map.mpr
  refine ⟨k⁻¹ * k', ?_, by simp only [map_mul, map_inv]⟩
  change phaseCharacter F ζ hζ C L (k⁻¹ * k') = 1
  rw [map_mul, map_inv, he, inv_mul_cancel]

def rootPhase (ε : rootsOfUnity 3 F) : phaseGroup F ζ hζ C L :=
  ⟨(KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val, by
    have hz := (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).property
    have hb := KPGlobalProductPolarizationCharacter.center_le_B F ζ hζ C hz
    have hr : (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val ∈ R F ζ hζ :=
      Subgroup.mem_sup_right hz
    have hi : (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val ∈ R F ζ hζ ⊓ B F ζ hζ C := ⟨hr, hb⟩
    rw [KPGlobalProductPolarizationCharacter.rational_intersection_preimage F ζ hζ C] at hi
    have hp : pD F ζ hζ (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val = 1 := by
      have hker : KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε ∈
          (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).ker := by
        rw [← KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel F ζ hζ]
        exact ⟨ε, rfl⟩
      have hp : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
          (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val.val = 1 := by
        rw [KPGlobalCenterRationalCharacter.centralRoot_formula]
        exact MonoidHom.mem_ker.mp hker
      have ht : ((KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).restrict
          (fun t ht => ht)) (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val =
            (1 : KPGlobalTorusFunctionData.ordinaryTorus F) := Subtype.ext hp
      change QuotientGroup.mk' _ (KPGlobalTorusFunctionData.torusRatio F _) = 1
      rw [ht, map_one, map_one]
    change pD F ζ hζ (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val ∈ L.K
    rw [hp]; exact L.K.one_mem⟩

theorem rootPhase_character (ε : rootsOfUnity 3 F) :
    phaseCharacter F ζ hζ C L (rootPhase F ζ hζ C L ε) = KPGlobalTorusFunctionData.iota F ζ hζ ε := by
  let z := KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε
  let b : B F ζ hζ C := ⟨z.val, KPGlobalProductPolarizationCharacter.center_le_B F ζ hζ C z.property⟩
  change KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment b /
    KPGlobalCenterRationalCharacter.positiveComplex (KPGlobalCenterRationalCharacter.nu F ζ hζ z.val) = _
  rw [KPGlobalProductPolarizationCharacter.lambdaB_extends_center F ζ hζ C C.adjustment b z rfl,
    KPGlobalCenterRationalCharacter.nu_centralRoot, map_one, div_one,
    KPGlobalCenterRationalCharacter.omegaA_genuine]

def rootPhaseHom : rootsOfUnity 3 F →* phaseGroup F ζ hζ C L where
  toFun := rootPhase F ζ hζ C L
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ 1).val.val = 1
    rw [KPGlobalCenterRationalCharacter.centralRoot_formula, map_one]
  map_mul' ε δ := by
    apply Subtype.ext
    apply Subtype.ext
    change (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ (ε * δ)).val.val =
      (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val.val *
        (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ δ).val.val
    rw [KPGlobalCenterRationalCharacter.centralRoot_formula,
      KPGlobalCenterRationalCharacter.centralRoot_formula,
      KPGlobalCenterRationalCharacter.centralRoot_formula, map_mul]

def rootToH : rootsOfUnity 3 F →* H F ζ hζ C L :=
  (center F ζ hζ C L).subtype.comp ((phaseToCenter F ζ hζ C L).comp (rootPhaseHom F ζ hζ C L))

def cubicCenter : Subgroup (H F ζ hζ C L) := (rootToH F ζ hζ C L).range

theorem cubicCenter_le_center : cubicCenter F ζ hζ C L ≤ center F ζ hζ C L := by
  rintro _ ⟨ε, rfl⟩
  exact (phaseToCenter F ζ hζ C L (rootPhase F ζ hζ C L ε)).property

instance cubicCenter_finite : Finite (cubicCenter F ζ hζ C L) := by
  exact Set.finite_range _ |>.to_subtype

theorem rootToH_injective : Function.Injective (rootToH F ζ hζ C L) := by
  intro ε δ he
  have hc : phaseToCenter F ζ hζ C L (rootPhase F ζ hζ C L ε) =
      phaseToCenter F ζ hζ C L (rootPhase F ζ hζ C L δ) := Subtype.ext he
  have hi := congrArg (centerCharacter F ζ hζ C L) hc
  rw [centerCharacter_phase, centerCharacter_phase, rootPhase_character, rootPhase_character] at hi
  have h6 := KPLocalCover.coefficientEmbedding_injective F ζ hζ hi
  exact Subtype.ext (congrArg (fun t : rootsOfUnity 6 F => (t : Fˣ)) h6)

def cubicCenterEquiv : rootsOfUnity 3 F ≃* cubicCenter F ζ hζ C L :=
  MulEquiv.ofBijective (rootToH F ζ hζ C L).rangeRestrict
    ⟨fun x y h => rootToH_injective F ζ hζ C L
      (congrArg (fun z : cubicCenter F ζ hζ C L => (z : H F ζ hζ C L)) h),
      fun ⟨z, ε, hε⟩ => ⟨ε, Subtype.ext hε⟩⟩

end

end DedekindZetaZeroFree.TorusFiniteCenterQuotient

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.TorusFiniteCenterQuotient
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPGlobalTorusFiniteStages

variable (C : CompatibleModelData F ζ hζ) (L : Level F ζ hζ C)

private theorem commutator_root (x y : KPGlobalTorusFunctionData.E F ζ hζ) :
    x * y * x⁻¹ * y⁻¹ =
      (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ
        (KPGlobalCubicIdelePairing.beta3 F ζ hζ
          (KPGlobalProductPolarizationCharacter.pD F ζ hζ x)
          (KPGlobalProductPolarizationCharacter.pD F ζ hζ y) ^ 4)).val := by
  apply Subtype.ext
  have h := congrArg (fun t : KPGlobalCubicIdelePairing.E F ζ hζ => t.val.1)
    (KPGlobalCubicIdelePairing.actual_torus_commutator F ζ hζ
      (torusPullbackBridge F ζ hζ x) (torusPullbackBridge F ζ hζ y))
  rw [KPGlobalCenterRationalCharacter.centralRoot_formula]
  exact h

theorem domainProjection_surjective : Function.Surjective (domainProjection F ζ hζ C L) := by
  intro v
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective v
  obtain ⟨t, ht⟩ := KPGlobalTorusFiniteStagesCofinality.finiteTorusClassProjection_surjective F ζ hζ d.val
  have ht' : pD F ζ hζ t.val = d.val := ht
  refine ⟨⟨t.val, ?_⟩, ?_⟩
  · change pD F ζ hζ t.val ∈ annihilator F ζ hζ L.K
    rw [ht']; exact d.property
  · change QuotientGroup.mk (⟨pD F ζ hζ t.val, _⟩ : annihilator F ζ hζ L.K) = QuotientGroup.mk d
    apply congrArg QuotientGroup.mk
    exact Subtype.ext ht'

theorem projection_surjective : Function.Surjective (projection F ζ hζ C L) := by
  intro v
  obtain ⟨x, hx⟩ := domainProjection_surjective F ζ hζ C L v
  exact ⟨QuotientGroup.mk x, hx⟩

theorem center_central : center F ζ hζ C L ≤ Subgroup.center (H F ζ hζ C L) := by
  rintro z ⟨x, hx, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro h
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective h
  exact congrArg QuotientGroup.mk (Subgroup.mem_center_iff.mp (phaseInDomain_central F ζ hζ C L hx) y)

theorem commutator_formula (x y : stageDomain F ζ hζ C L) :
    QuotientGroup.mk (x * y * x⁻¹ * y⁻¹) =
      (phaseToCenter F ζ hζ C L (rootPhase F ζ hζ C L
        (stagePairing F ζ hζ C L (domainProjection F ζ hζ C L x)
          (domainProjection F ζ hζ C L y) ^ 4))).val := by
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  change x.val * y.val * x.val⁻¹ * y.val⁻¹ = _
  have hp : stagePairing F ζ hζ C L (domainProjection F ζ hζ C L x)
      (domainProjection F ζ hζ C L y) = KPGlobalCubicIdelePairing.beta3 F ζ hζ (pD F ζ hζ x.val) (pD F ζ hζ y.val) :=
    stagePairing_formula F ζ hζ C L _ _
  rw [hp]
  exact commutator_root F ζ hζ x.val y.val

end
end DedekindZetaZeroFree.TorusFiniteCenterQuotient

end

module

public import DedekindZetaZeroFree.Metaplectic.Torus.ProductPolarizationCharacter

@[expose] public section

open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def archUnit (z : KPGlobalTorusFunctionData.TorusArch F) (w : InfinitePlace F) : w.Completionˣ :=
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ w)
  if h : z w = 0 then 1 else Units.mk0 (e.symm (z w))
    (by exact fun h0 => h (by simpa using congrArg e h0))
 def archIdele (z : KPGlobalTorusFunctionData.TorusArch F) : KPGlobalTorusFunctionData.Ideles F where
  val := (fun w => (archUnit F ζ hζ z w).val, 1)
  inv := (fun w => (archUnit F ζ hζ z w).inv, 1)
  val_inv := by
    apply Prod.ext
    · funext w; exact (archUnit F ζ hζ z w).val_inv
    · exact one_mul _
  inv_val := by
    apply Prod.ext
    · funext w; exact (archUnit F ζ hζ z w).inv_val
    · exact one_mul _
private theorem arch_eval (z : KPGlobalTorusFunctionData.TorusArch F) (v : KPHilbert.Place F) :
    KPGlobalCubicIdelePairing.ideleEval F v (archIdele F ζ hζ z) =
      (match v with | Sum.inl w => archUnit F ζ hζ z w | Sum.inr q => 1) := by
  cases v with
  | inl w => apply Units.ext; rfl
  | inr q => apply Units.ext; rfl
private theorem arch_cube (z : KPGlobalTorusFunctionData.TorusArch F) :
    archIdele F ζ hζ z ∈ CubicCharacters.cubes (KPGlobalTorusFunctionData.Ideles F) := by
  apply (QuotientGroup.eq_one_iff _).mp
  apply KPGlobalCubicIdelePairing.classComparison_injective F
  rw [map_one]
  apply RestrictedProduct.ext
  intro v
  change KPGlobalCubicIdelePairing.localClass F v (KPGlobalCubicIdelePairing.ideleEval F v (archIdele F ζ hζ z)) = 1
  cases v with
  | inl w =>
    letI := KPGlobalCubicIdelePairing.local_complex_trivial F w
    exact Subsingleton.elim _ _
  | inr q => rw [arch_eval]; exact map_one _
private theorem arch_tuple (z : KPGlobalTorusFunctionData.TorusArch F) :
    KPGlobalCenterRationalCharacter.diagonalTuple F ζ hζ (archIdele F ζ hζ z) =
      KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ z := by
  apply RestrictedProduct.ext
  intro v
  change KPStandardLocalRootLifts.A F ζ hζ v (KPGlobalCubicIdelePairing.ideleEval F v (archIdele F ζ hζ z)) = _
  rw [arch_eval]
  cases v with
  | inl w => rfl
  | inr q => exact KPStandardLocalRootLifts.A_one F ζ hζ (Sum.inr q)
theorem arch_center (z : KPGlobalTorusFunctionData.TorusArch F) :
    ∃ c : KPGlobalCenterRationalCharacter.Z F ζ hζ,
      c.val = KPGlobalTorusFunctionData.torusArchChart F ζ hζ z ∧
      KPGlobalCenterRationalCharacter.omegaA F ζ hζ c =
        KPGlobalCenterRationalCharacter.positiveComplex
          (KPGlobalCenterRationalCharacter.nu F ζ hζ c.val) := by
  let y : CubicCharacters.cubes (KPGlobalTorusFunctionData.Ideles F) :=
    ⟨archIdele F ζ hζ z, arch_cube F ζ hζ z⟩
  let c := KPGlobalCenterRationalCharacter.cubeLift F ζ hζ y
  have hc : c.val = KPGlobalTorusFunctionData.torusArchChart F ζ hζ z := by
    apply Subtype.ext
    rw [KPGlobalCenterRationalCharacter.cubeLift_formula]
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ
        (KPGlobalCenterRationalCharacter.diagonalTuple F ζ hζ (archIdele F ζ hζ z))) = _
    rw [arch_tuple]
    rfl
  refine ⟨c, hc, ?_⟩
  have ho := KPGlobalCenterRationalCharacter.omegaA_cube F ζ hζ y
  have hn := KPGlobalCenterRationalCharacter.omegaA_norm F ζ hζ c
  have hp (u : (ℝ≥0)ˣ) :
      ‖((KPGlobalCenterRationalCharacter.positiveComplex u : ℂˣ) : ℂ)‖ = ((u : ℝ≥0) : ℝ) := by
    change ‖(((u : ℝ≥0) : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [ho, hp] at hn
  have hu : KPGlobalCenterRationalCharacter.sixthPower (KPGlobalTorusFunctionData.ideleAbs F y.val) =
      KPGlobalCenterRationalCharacter.nu F ζ hζ c.val := by
    apply Units.ext
    exact NNReal.eq hn
  exact ho.trans (congrArg KPGlobalCenterRationalCharacter.positiveComplex hu)

theorem normalized_arch_chart_character_one
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ :
      (Q.H = KPGlobalCenterRationalCharacter.R F ζ hζ ∧
        ∀ (r : Q.H) (s : KPGlobalCenterRationalCharacter.R F ζ hζ), r.val = s.val →
          Q.character r = KPGlobalCenterRationalCharacter.lambdaR F ζ hζ s /
            KPGlobalCenterRationalCharacter.positiveComplex
              (KPGlobalCenterRationalCharacter.nu F ζ hζ s.val)) ∨
      (Q.H = KPGlobalProductPolarizationCharacter.B F ζ hζ P ∧
        ∀ (r : Q.H) (s : KPGlobalProductPolarizationCharacter.B F ζ hζ P), r.val = s.val →
          Q.character r = KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T s /
            KPGlobalCenterRationalCharacter.positiveComplex
              (KPGlobalCenterRationalCharacter.nu F ζ hζ s.val))) :
    ∀ z : KPGlobalTorusFunctionData.TorusArch F,
      ∃ h : Q.H, h.val = KPGlobalTorusFunctionData.torusArchChart F ζ hζ z ∧
        Q.character h = 1 := by
  intro z
  obtain ⟨c, hc, hχc⟩ := arch_center F ζ hζ z
  rcases hQ with ⟨hH, hχ⟩ | ⟨hH, hχ⟩
  · have hr : c.val ∈ KPGlobalCenterRationalCharacter.R F ζ hζ :=
      Subgroup.mem_sup_right c.property
    let r : KPGlobalCenterRationalCharacter.R F ζ hζ := ⟨c.val, hr⟩
    let h : Q.H := ⟨c.val, hH.symm ▸ hr⟩
    refine ⟨h, hc, ?_⟩
    rw [hχ h r rfl]
    rw [KPGlobalCenterRationalCharacter.lambdaR_formula F ζ hζ r 1 c (by simp [r]), hχc]
    exact div_self' _
  · have hb : c.val ∈ KPGlobalProductPolarizationCharacter.B F ζ hζ P :=
      KPGlobalProductPolarizationCharacter.center_le_B F ζ hζ P c.property
    let b : KPGlobalProductPolarizationCharacter.B F ζ hζ P := ⟨c.val, hb⟩
    let h : Q.H := ⟨c.val, hH.symm ▸ hb⟩
    refine ⟨h, hc, ?_⟩
    rw [hχ h b rfl]
    rw [KPGlobalProductPolarizationCharacter.lambdaB_extends_center F ζ hζ P T b c rfl, hχc]
    exact div_self' _
end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality

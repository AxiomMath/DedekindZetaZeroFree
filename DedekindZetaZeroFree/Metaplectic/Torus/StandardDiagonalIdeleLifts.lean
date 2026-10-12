module

public import DedekindZetaZeroFree.Metaplectic.Torus.RationalCenterCharacterData

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

lemma restrictedProjection_eq_diagonal (y : Ideles F) (x : Raw F ζ hζ)
    (hx : ∀ v, x v = KPStandardLocalRootLifts.A F ζ hζ v
      (KPGlobalCubicIdelePairing.ideleEval F v y)) :
    KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ x =
      KPGlobalCubicIdelePairing.diagonalHom F y := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply Prod.ext
  · funext w
    have h := KPAdelicCoverRestrictedProduct.restrictedProjection_eval F ζ hζ x (Sum.inl w)
    have hh := congrArg (fun A : KPLocalCover.LocalGL2 F (Sum.inl w) => A i j) h
    rw [hx (Sum.inl w)] at hh
    change ((KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ x) i j).1 w =
      (KubotaRankTwo.d (KPHilbert.Completion F (Sum.inl w))
        (KPGlobalCubicIdelePairing.ideleEval F (Sum.inl w) y) 1) i j at hh
    fin_cases i <;> fin_cases j
    all_goals simp [KubotaRankTwo.d] at hh
    all_goals convert hh using 1 <;> rfl
  · apply RestrictedProduct.ext
    intro q
    have h := KPAdelicCoverRestrictedProduct.restrictedProjection_eval F ζ hζ x (Sum.inr q)
    have hh := congrArg (fun A : KPLocalCover.LocalGL2 F (Sum.inr q) => A i j) h
    rw [hx (Sum.inr q)] at hh
    change ((KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ x) i j).2 q =
      (KubotaRankTwo.d (KPHilbert.Completion F (Sum.inr q))
        (KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) y) 1) i j at hh
    fin_cases i <;> fin_cases j
    all_goals simp [KubotaRankTwo.d] at hh
    all_goals convert hh using 1 <;> rfl

theorem standard_diagonal_torus_ratio (y : Ideles F) (x : Raw F ζ hζ)
    (hx : ∀ v, x v = KPStandardLocalRootLifts.A F ζ hζ v
      (KPGlobalCubicIdelePairing.ideleEval F v y)) :
    ∃ t : E F ζ hζ,
      t.val = KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x) ∧
      KPGlobalTorusFunctionData.p F ζ hζ t = y := by
  set A := KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ x with hAdef
  have hA : A = KPGlobalCubicIdelePairing.diagonalHom F y :=
    restrictedProjection_eq_diagonal F ζ hζ y x hx
  have h10 : (A : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) 1 0 = 0 := by
    rw [hA]; simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix]
  have h01 : (A : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) 0 1 = 0 := by
    rw [hA]; simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix]
  have h00 : (A : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) 0 0 =
      (y : KPAdelicCoverRestrictedProduct.Adeles F) := by
    rw [hA]; simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix]
  have h11 : (A : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)) 1 1 = 1 := by
    rw [hA]; simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix]
  set g := KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x) with hgdef
  have hmk : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ g := by
    change QuotientGroup.mk' _ (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ x) =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
        (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x))
    rfl
  have hmem : g ∈ E F ζ hζ := ⟨A, hmk, h10, h01⟩
  refine ⟨⟨g, hmem⟩, rfl, ?_⟩
  show KPGlobalTorusFunctionData.torusRatio F
      ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ g, hmem⟩ = y
  apply Units.ext
  rw [KPGlobalTorusFunctionData.ratio_formula F
      ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ g, hmem⟩ A hmk h10 h01]
  have hu : ((KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit :
      KPAdelicCoverRestrictedProduct.Adeles F) =
      (y : KPAdelicCoverRestrictedProduct.Adeles F) := by
    rw [IsUnit.unit_spec, h00]
  have hw : ((KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit :
      KPAdelicCoverRestrictedProduct.Adeles F) = 1 := by
    rw [IsUnit.unit_spec, h11]
  have hw' : (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit = 1 :=
    Units.ext hw
  rw [hu, hw', inv_one, Units.val_one, mul_one]

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct

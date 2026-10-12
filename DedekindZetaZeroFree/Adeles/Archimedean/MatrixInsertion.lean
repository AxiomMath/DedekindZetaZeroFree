module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.TranslatedBigCellCoordinates
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ComplexStandardIntertwinerGerm

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming complexSectionHom → complexSectionHom
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming tuple_prod → tuple_prod
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming sectionTuple_insertion → sectionTuple_insertion

namespace DedekindZetaZeroFree.KPLiteralScalarHCCompactOrbit
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralChamber KPCplxCharacterHaar
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def archMatrixInsertion : (InfinitePlace F → ComplexGL2) →* G F ζ hζ where
  toFun a := scalarQuotient F ζ hζ (amalgamation F ζ hζ (sectionTuple F ζ hζ a))
  map_one' := by
    have he : sectionTuple F ζ hζ (1 : InfinitePlace F → ComplexGL2) = 1 := by
      apply RestrictedProduct.ext
      intro v
      cases v with
      | inl w => exact (complexSectionHom F ζ hζ w).map_one
      | inr q => rfl
    rw [he, map_one, map_one]
  map_mul' a b := by
    have he : sectionTuple F ζ hζ (a * b) = sectionTuple F ζ hζ a * sectionTuple F ζ hζ b := by
      apply RestrictedProduct.ext
      intro v
      cases v with
      | inl w => exact (complexSectionHom F ζ hζ w).map_mul (a w) (b w)
      | inr q => change (1 : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) = 1 * 1; simp
    rw [he, map_mul, map_mul]

theorem archMatrixInsertion_compact_mem (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (k : InfinitePlace F → ComplexSU2) :
    archMatrixInsertion F ζ hζ (fun w => complexSU2Embedding (k w)) ∈ K := by
  change scalarQuotient F ζ hζ (amalgamation F ζ hζ
    (sectionTuple F ζ hζ (fun w => complexSU2Embedding (k w)))) ∈ K
  rw [tuple_prod F ζ hζ (sectionTuple F ζ hζ (fun w => complexSU2Embedding (k w)))
    (by intro q; rfl), map_list_prod, map_list_prod, List.map_map, List.map_map]
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hg
  exact hK.2.2 w (k w)

end DedekindZetaZeroFree.KPLiteralScalarHCCompactOrbit

namespace DedekindZetaZeroFree.KPLiteralScalarHCSliceCharts
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralChamber
open KPLiteralScalarHCCompactOrbit KPCplxCharacterHaar
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem archMatrixInsertion_commutes_finite (a : InfinitePlace F → ComplexGL2)
    (b : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    Commute (archMatrixInsertion F ζ hζ a) b.val := by
  obtain ⟨r, hr, he⟩ := Subgroup.mem_map.mp b.property
  have hcomm : Commute (sectionTuple F ζ hζ a) r := by
    change sectionTuple F ζ hζ a * r = r * sectionTuple F ζ hζ a
    apply RestrictedProduct.ext
    intro v
    cases v with
    | inl w =>
      have hw : r (Sum.inl w) = 1 :=
        (Subgroup.mem_iInf.mp hr w)
      change _ * r (Sum.inl w) = r (Sum.inl w) * _
      rw [hw, mul_one, one_mul]
    | inr q => change 1 * r (Sum.inr q) = r (Sum.inr q) * 1; simp
  exact he ▸ hcomm.map ((scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ))

end DedekindZetaZeroFree.KPLiteralScalarHCSliceCharts

namespace DedekindZetaZeroFree.KPLiteralScalarHCLocalCovariance
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralChamber
open KPLiteralScalarHCCompactOrbit KPCplxCharacterHaar
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def archRootAdele (u : InfinitePlace F → ℂ) : KPGlobalTorusFunctionData.Adeles F :=
  ⟨fun w => (InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)).symm (u w), 0⟩

theorem archMatrixInsertion_upper (u : InfinitePlace F → ℂ) :
    archMatrixInsertion F ζ hζ (fun w => upperUnipotent (u w)) =
      KPGlobalTorusFunctionData.N F ζ hζ (archRootAdele F ζ hζ u) := by
  change scalarQuotient F ζ hζ (amalgamation F ζ hζ _) =
    scalarQuotient F ζ hζ (amalgamation F ζ hζ _)
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inl w =>
    change complexSectionHom F ζ hζ w (upperUnipotent (u w)) =
      KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w)
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm (u w))
    change KPLocalCover.CubicGL2Raw.mk _ 1 = KPLocalCover.CubicGL2Raw.mk _ 1
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map,
      upperUnipotent]
  | inr q =>
    change 1 = KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) 0
    exact (KPStandardLocalRootLifts.N_zero F ζ hζ (Sum.inr q)).symm

theorem archMatrixInsertion_projective_congr
    (a b : InfinitePlace F → ComplexGL2)
    (h : ∀ w, Matrix.ProjGenLinGroup.mk (a w) = Matrix.ProjGenLinGroup.mk (b w)) :
    archMatrixInsertion F ζ hζ a = archMatrixInsertion F ζ hζ b := by
  change scalarQuotient F ζ hζ (amalgamation F ζ hζ (sectionTuple F ζ hζ a)) =
    scalarQuotient F ζ hζ (amalgamation F ζ hζ (sectionTuple F ζ hζ b))
  rw [sectionTuple_insertion, sectionTuple_insertion]
  congr 1
  exact funext h

theorem archMatrixInsertion_diagonal (z : InfinitePlace F → ℂˣ) :
    archMatrixInsertion F ζ hζ (fun w => KubotaRankTwo.d ℂ (z w) 1) =
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ (fun w => (z w : ℂ))).val := by
  change scalarQuotient F ζ hζ (amalgamation F ζ hζ _) =
    scalarQuotient F ζ hζ (amalgamation F ζ hζ _)
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inr q => rfl
  | inl w =>
    change complexSectionHom F ζ hζ w (KubotaRankTwo.d ℂ (z w) 1) = _
    simp only [KPGlobalTorusFunctionData.archDiagonalTuple]
    change KPLocalCover.CubicGL2Raw.mk _ 1 = KPLocalCover.CubicGL2Raw.mk _ 1
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map]

private theorem upper_projective (a d : ℂˣ) (b : ℂ) :
    Matrix.ProjGenLinGroup.mk (KPCplxPrincipalSeriesCharts.upperTriangular a d b) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (a / d) 1 * upperUnipotent (b / a)) := by
  apply (Matrix.ProjGenLinGroup.mk_eq_mk_iff).mpr
  refine ⟨Units.mk0 ((d : ℂ)⁻¹) (inv_ne_zero d.ne_zero), ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [KPCplxPrincipalSeriesCharts.upperTriangular, upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]
  field_simp

end DedekindZetaZeroFree.KPLiteralScalarHCLocalCovariance

namespace DedekindZetaZeroFree.KPLiteralScalarHCCompactAction
open KPAdelicCoverRestrictedProduct KPLiteralChamber
open KPLiteralScalarHCCompactOrbit KPCplxCharacterHaar
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem archMatrixInsertion_compact_single (w : InfinitePlace F) (k : ComplexSU2) :
    archMatrixInsertion F ζ hζ (Function.update 1 w (complexSU2Embedding k)) =
      KPGlobalResidualConstruction.complexCompactLift F ζ hζ w k := by
  change scalarQuotient F ζ hζ (amalgamation F ζ hζ _) = _
  change scalarQuotient F ζ hζ (amalgamation F ζ hζ _) =
    scalarQuotient F ζ hζ (amalgamation F ζ hζ _)
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inl j =>
    by_cases hj : j = w
    · subst j
      change complexSectionHom F ζ hζ w
        ((Function.update (1 : InfinitePlace F → ComplexGL2) w (complexSU2Embedding k)) w) = _
      rw [Function.update_self]
      simp [localToRestricted, RestrictedProduct.coe_mulSingle_apply, complexSectionHom]
    · change complexSectionHom F ζ hζ j
        ((Function.update (1 : InfinitePlace F → ComplexGL2) w (complexSU2Embedding k)) j) = _
      rw [Function.update_of_ne hj]
      simp [localToRestricted, RestrictedProduct.coe_mulSingle_apply, hj]
  | inr q =>
    change (1 : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) = _
    simp [localToRestricted, RestrictedProduct.coe_mulSingle_apply]

end DedekindZetaZeroFree.KPLiteralScalarHCCompactAction

namespace DedekindZetaZeroFree.SheetRescaling.ArchMatrixGeometry
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open KPLiteralScalarHCCompactOrbit KPLiteralScalarHCLocalCovariance KPLiteralScalarHCSliceCharts
open RepresentationTheory.KPComplexStandardIntertwinerGermProve
open DedekindZetaZeroFree.KPComplexIntertwinerParameterMajorant
open KPComplexStandardIntertwinerGerm
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def chosenCompact (g : InfinitePlace F → ComplexGL2) : InfinitePlace F → ComplexSU2 :=
  fun w => KPComplexStandardIntertwinerGerm.compactRepresentative (bottomRowLine (g w))

theorem chosen_factorization (g : InfinitePlace F → ComplexGL2) :
    ∃ (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ),
    (∀ w, g w = upperTriangular (a w) (d w) (b w) * complexSU2Embedding (chosenCompact F g w)) ∧
    (∀ w, rowRatio (g w) = ‖(a w : ℂ) / (d w : ℂ)‖) := by
  choose a d b h using fun w => same_line_upper (g w)
    (complexSU2Embedding (chosenCompact F g w)) (by dsimp [chosenCompact]; rw [bottomRowLine_compactRepresentative])
  refine ⟨a, d, b, h, ?_⟩
  intro w
  rw [h w, rowRatio_upper_mul, rowRatio_su2, mul_one]

theorem inserted_factorization
    (a d : InfinitePlace F → ℂˣ) (u : InfinitePlace F → ℂ)
    (k : InfinitePlace F → ComplexSU2)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    c.val * archMatrixInsertion F ζ hζ
      (fun w => upperTriangular (a w) (d w) (u w) * complexSU2Embedding (k w)) =
    (((KPGlobalTorusFunctionData.torusArchChart F ζ hζ
       (fun w => ((a w / d w : ℂˣ) : ℂ))).val *
      KPGlobalTorusFunctionData.N F ζ hζ (archRootAdele F ζ hζ (fun w => u w / a w))) * c.val) *
      archMatrixInsertion F ζ hζ (fun w => complexSU2Embedding (k w)) := by
  have he := archMatrixInsertion_projective_congr F ζ hζ
    (fun w => upperTriangular (a w) (d w) (u w) * complexSU2Embedding (k w))
    (fun w => (KubotaRankTwo.d ℂ (a w / d w) 1 * upperUnipotent (u w / a w)) * complexSU2Embedding (k w))
    (fun w => by simp only [map_mul, upper_projective])
  rw [he]
  change c.val * archMatrixInsertion F ζ hζ
    (((fun w => KubotaRankTwo.d ℂ (a w / d w) 1) * (fun w => upperUnipotent (u w / a w))) *
      (fun w => complexSU2Embedding (k w))) = _
  rw [map_mul, map_mul]
  rw [← mul_assoc, ← mul_assoc,
    ← (archMatrixInsertion_commutes_finite F ζ hζ (fun w => KubotaRankTwo.d ℂ (a w / d w) 1) c).eq,
    mul_assoc, mul_assoc, ← mul_assoc c.val,
    ← (archMatrixInsertion_commutes_finite F ζ hζ (fun w => upperUnipotent (u w / a w)) c).eq,
    mul_assoc, ← mul_assoc, archMatrixInsertion_diagonal, archMatrixInsertion_upper]
  exact (mul_assoc _ _ _).symm

end DedekindZetaZeroFree.SheetRescaling.ArchMatrixGeometry

end

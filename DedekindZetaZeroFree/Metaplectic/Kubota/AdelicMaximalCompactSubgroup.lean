module

public import DedekindZetaZeroFree.Theta.Profiles.IdelicDilation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField
open scoped Classical NumberField Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def complexSU2Compact (R : PrincipalMellin.ActualRecipe S η) (w : InfinitePlace F) :
    Subgroup (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)) :=
  Subgroup.closure {x | ∃ k : KPCplxCharacterHaar.ComplexSU2,
    x = KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
      (Matrix.GeneralLinearGroup.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).symm.toRingHom
        (KPCplxCharacterHaar.complexSU2Embedding k))}

def integralRawCompact (R : PrincipalMellin.ActualRecipe S η) (q : KPFinitePlace F) :
    Subgroup (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :=
  (KPTameCompact.inclusion F q).range.comap
    (KPLocalCover.projection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))

def iwasawaCompactFactor (R : PrincipalMellin.ActualRecipe S η) (v : KPHilbert.Place F) :
    Subgroup (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 v) :=
  match v with
  | Sum.inl w => complexSU2Compact R w
  | Sum.inr q => if KPAdelicCoverRestrictedProduct.Bad F q then integralRawCompact R q
      else KPAdelicCoverRestrictedProduct.finiteCompact F R.A.zeta12 R.A.primitive_zeta12 q

theorem finite_compact_le_iwasawa_compact_factor (R : PrincipalMellin.ActualRecipe S η) (q : KPFinitePlace F) :
    KPAdelicCoverRestrictedProduct.finiteCompact F R.A.zeta12 R.A.primitive_zeta12 q ≤
      iwasawaCompactFactor R (Sum.inr q) := by
  intro r hr
  dsimp only [iwasawaCompactFactor]
  split_ifs with hb
  · rw [KPAdelicCoverRestrictedProduct.finiteCompact, dif_pos hb] at hr
    obtain ⟨g, rfl⟩ := hr
    obtain ⟨k, hk, hkg⟩ := g.property
    exact ⟨k, hkg⟩
  · exact hr

def fullProductCompactPreimage (R : PrincipalMellin.ActualRecipe S η) :
    Subgroup (KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12) where
  carrier := {x | ∀ v, x v ∈ iwasawaCompactFactor R v}
  one_mem' := by intro v; exact (iwasawaCompactFactor R v).one_mem
  mul_mem' := by intro x y hx hy v; exact (iwasawaCompactFactor R v).mul_mem (hx v) (hy v)
  inv_mem' := by intro x hx v; exact (iwasawaCompactFactor R v).inv_mem (hx v)

def fullProductCompact (R : PrincipalMellin.ActualRecipe S η) : Subgroup (Group R) :=
  (fullProductCompactPreimage R).map
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12))

theorem complex_compact_lift_mem_full_product_compact (R : PrincipalMellin.ActualRecipe S η)
    (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2) :
    KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k ∈ fullProductCompact R := by
  refine Subgroup.mem_map.mpr ⟨
    KPAdelicCoverRestrictedProduct.localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
      (KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
        (Matrix.GeneralLinearGroup.map
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).symm.toRingHom
          (KPCplxCharacterHaar.complexSU2Embedding k))), ?_, rfl⟩
  intro v
  rw [KPAdelicCoverRestrictedProduct.localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
    RestrictedProduct.coe_mulSingle_apply]
  rcases eq_or_ne v (Sum.inl w) with rfl | hne
  · rw [Pi.mulSingle_eq_same]
    exact Subgroup.subset_closure ⟨k, rfl⟩
  · rw [Pi.mulSingle_eq_of_ne hne]
    exact (iwasawaCompactFactor R v).one_mem

theorem iwasawa_compact_factor_eq_arithmetic_compact_eventually (R : PrincipalMellin.ActualRecipe S η) :
    ∀ᶠ v in Filter.cofinite, iwasawaCompactFactor R v =
      KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 v := by
  have hf : {v : KPHilbert.Place F | ∃ w : InfinitePlace F, v = Sum.inl w}.Finite := by
    exact (Set.finite_range Sum.inl).subset (by rintro v ⟨w,rfl⟩; exact ⟨w,rfl⟩)
  have hb := (KPAdelicCoverRestrictedProduct.bad_finite F).image
    (Sum.inr : KPFinitePlace F → KPHilbert.Place F)
  have hfi : ∀ᶠ v : KPHilbert.Place F in Filter.cofinite,
      ¬ (∃ w : InfinitePlace F, v = Sum.inl w) := by
    exact Filter.eventually_cofinite.mpr (by simpa using hf)
  have hbi : ∀ᶠ v : KPHilbert.Place F in Filter.cofinite,
      v ∉ Sum.inr '' {q | KPAdelicCoverRestrictedProduct.Bad F q} := by
    apply Filter.eventually_cofinite.mpr
    simpa only [not_not, Set.setOf_mem_eq] using hb
  filter_upwards [hfi, hbi] with v hv hvb
  cases v with
  | inl w => exact False.elim (hv ⟨w,rfl⟩)
  | inr q =>
    have hn : ¬ KPAdelicCoverRestrictedProduct.Bad F q := by
      intro h
      exact hvb ⟨q,h,rfl⟩
    simp [iwasawaCompactFactor, hn, KPAdelicCoverRestrictedProduct.compact]

end DedekindZetaZeroFree.ThetaExpansion

end

module

public import DedekindZetaZeroFree.Theta.Profiles.ResidualCoreAndUnitRotations

@[expose] public section

section

noncomputable section
open NumberField
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualFiniteTranslationEstimates

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem archChart_commutes_finite (x : ArchCoordinates F)
    (a : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    Commute (archChart F ζ hζ x) a.val := by
  obtain ⟨b, hb, he⟩ := a.property
  let t : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ :=
    ⟨fun v => match v with
      | Sum.inr _ => 1
      | Sum.inl w =>
        let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)
        KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) (e.symm (x w 0)) *
        KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w)
          (if h : x w 1 = 0 then 1 else Units.mk0 (e.symm (x w 1))
            (by exact fun h0 => h (by simpa using congrArg e h0))) *
        KPStandardLocalRootLifts.LowerN F ζ hζ (Sum.inl w) (e.symm (x w 2)), by
      apply Filter.Eventually.of_forall
      intro v
      cases v with
      | inl w => exact Subgroup.mem_top _
      | inr q => exact Subgroup.one_mem _⟩
  have hc : Commute t b := by
    show t * b = b * t
    apply RestrictedProduct.ext
    intro v
    cases v with
    | inl w =>
      have hw : b (Sum.inl w) = 1 := (Subgroup.mem_iInf.mp hb) w
      simp [hw]
    | inr q =>
      change 1 * b (Sum.inr q) = b (Sum.inr q) * 1
      simp
  have hm := hc.map ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))
  convert hm using 1 <;> simp only [MonoidHom.comp_apply, he, archChart, t]
  congr 2

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualFiniteTranslationEstimates

end

end

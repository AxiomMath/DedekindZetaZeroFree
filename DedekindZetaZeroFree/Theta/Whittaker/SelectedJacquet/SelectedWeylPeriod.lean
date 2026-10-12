module

public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.CompactWeyl

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPGlobalResidualConstruction
open NumberField
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (w : InfinitePlace F)

theorem complex_section_scalar_quotient
    (g : KPLocalCover.LocalGL2 F (Sum.inl w))
    (u : (KPHilbert.Completion F (Sum.inl w))ˣ) :
    KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
        (g * Matrix.GeneralLinearGroup.scalar (Fin 2) u)) =
    KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inl w) g) := by
  have hm : KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
      (g * Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      KPLocalCover.sectionMap F ζ hζ (Sum.inl w) g *
        KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w) u := by
    change KPLocalCover.CubicGL2Raw.mk _ _ = KPLocalCover.CubicGL2Raw.mk _ _
    simp [KPLocalChartTopology.complex_sigmaTwo_eq_one, KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift, KPLocalCover.sectionMap]
  rw [hm, map_mul]
  have hu : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)
      (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w) u) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩
  rw [hu, mul_one]

theorem complexCompactLift_weyl :
    complexCompactLift F ζ hζ w compactWeyl =
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl w)
          (KPRationalAdelicSplitting.WCoordinates F ζ hζ (Sum.inl w))) := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)
  let g := Matrix.GeneralLinearGroup.map e.symm.toRingHom (complexSU2Embedding compactWeyl)
  let u := Units.map e.symm.toRingHom.toMonoidHom
    (Units.mk0 (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero))
  have hg : g * Matrix.GeneralLinearGroup.scalar (Fin 2) u =
      KPStandardLocalRootLifts.weylSwap (KPHilbert.Completion F (Sum.inl w)) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [g, u, complexSU2Embedding, compactWeyl, KPStandardLocalRootLifts.weylSwap,
        Matrix.mul_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, ← map_mul]
  obtain ⟨j, _, _, hj⟩ := KPAdelicCoverRestrictedProduct.local_pgl_injection F ζ hζ (Sum.inl w)
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl w)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inl w) g)) = _
  rw [← hj, ← hj]
  apply congrArg j
  rw [← complex_section_scalar_quotient ζ hζ w g u, hg]
  rfl

end DedekindZetaZeroFree.SheetRescaling

end

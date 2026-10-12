module

public import DedekindZetaZeroFree.Eisenstein.Residues.MetaplecticRealizations
public import DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology Matrix MatrixGroups
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralPeriod
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def eCplx (w : InfinitePlace F) : ℂ →+* w.Completion :=
  (InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom

def sl2ToLocal (w : InfinitePlace F) : SL(2, ℂ) →* KPLocalCover.LocalGL2 F (Sum.inl w) :=
  (Matrix.GeneralLinearGroup.map (eCplx F ζ hζ w)).comp Matrix.SpecialLinearGroup.toGL

def localSectionHom (w : InfinitePlace F) : KPLocalCover.LocalGL2 F (Sum.inl w) →*
    KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) where
  toFun := KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
  map_one' := rfl
  map_mul' g h := by
    rw [KPLocalCover.sectionMap_mul,
      KPLocalChartTopology.complex_sigmaTwo_eq_one F ζ hζ w g h, map_one, one_mul]

def complexSL2 (w : InfinitePlace F) : SL(2, ℂ) →* KPGlobalTorusFunctionData.G F ζ hζ :=
  ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
    (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inl w))).comp
    ((localSectionHom F ζ hζ w).comp (sl2ToLocal F ζ hζ w))

 theorem complexSL2_upper (w : InfinitePlace F) (z : ℂ) :
    complexSL2 F ζ hζ w (Matrix.SpecialLinearGroup.transvection (i := 0) (j := 1) (by decide) z) =
      KPGlobalTorusFunctionData.N F ζ hζ (KPRationalAdelicSplitting.localAdele F (Sum.inl w) (eCplx F ζ hζ w z)) := by
  have hN (x) : KPGlobalTorusFunctionData.N F ζ hζ x = KPRationalAdelicSplitting.pglN F ζ hζ x := rfl
  rw [hN, KPRationalAdelicSplitting.pglN, KPRationalAdelicSplitting.N_local]
  simp only [complexSL2, MonoidHom.comp_apply]
  congr 2
  change KPLocalCover.sectionMap F ζ hζ (Sum.inl w) _ = KPLocalCover.sectionMap F ζ hζ (Sum.inl w) _
  apply congrArg (KPLocalCover.sectionMap F ζ hζ (Sum.inl w))
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2ToLocal, Matrix.SpecialLinearGroup.transvection_coe, KubotaRankTwo.n,
      Matrix.GeneralLinearGroup.map, Matrix.SpecialLinearGroup.toGL]
 theorem complexSL2_lower (w : InfinitePlace F) (z : ℂ) :
    complexSL2 F ζ hζ w (Matrix.SpecialLinearGroup.transvection (i := 1) (j := 0) (by decide) z) =
      KPRationalAdelicSplitting.pglLowerN F ζ hζ (KPRationalAdelicSplitting.localAdele F (Sum.inl w) (eCplx F ζ hζ w z)) := by
  rw [KPRationalAdelicSplitting.pglLowerN, KPRationalAdelicSplitting.LowerN_local]
  simp only [complexSL2, MonoidHom.comp_apply]
  congr 2
  change KPLocalCover.sectionMap F ζ hζ (Sum.inl w) _ = KPLocalCover.sectionMap F ζ hζ (Sum.inl w) _
  apply congrArg (KPLocalCover.sectionMap F ζ hζ (Sum.inl w))
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2ToLocal, Matrix.SpecialLinearGroup.transvection_coe, KPStandardLocalRootLifts.lowerN,
      Matrix.GeneralLinearGroup.map, Matrix.SpecialLinearGroup.toGL]
 theorem literal_rationalLift_mk (m : Matrix.GeneralLinearGroup (Fin 2) F) :
    rationalLift F ζ hζ (Matrix.ProjGenLinGroup.mk m) =
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ m) := by
  let n := Quotient.out (Matrix.ProjGenLinGroup.mk m)
  have hn : Matrix.ProjGenLinGroup.mk n = Matrix.ProjGenLinGroup.mk m := Quotient.out_eq _
  obtain ⟨z, hz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hn
  let φ := (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
    (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ)
  have hs : φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = 1 :=
    KPRationalAdelicSplitting.rationalScalars_le_ker F ζ hζ ⟨z, rfl⟩
  change φ n = φ m
  rw [← hz, map_mul, hs, mul_one]

end DedekindZetaZeroFree.KPLiteralPeriod

end

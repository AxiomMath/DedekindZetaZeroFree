module

public import DedekindZetaZeroFree.Theta.Periods.FirstRootDifferentiation
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.WordCutoff

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem diagonal_one (R : PrincipalMellin.ActualRecipe S η) :
    diagonal R (1 : R.A.G) = 1 := by
  unfold diagonal localIdele
  simp only [Prod.fst_one, Prod.snd_one, Pi.one_apply, KPRationalAdelicSplitting.localIdele,
    map_one, Finset.prod_const_one, one_mul]
  unfold KPRationalAdelicSplitting.pglA KPRationalAdelicSplitting.A KPRationalAdelicSplitting.ATuple
  have ht : KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 1 = 1 := by
    ext v
    simp [KPRationalAdelicSplitting.ATuple, KPRationalAdelicSplitting.ACoordinates, KPStandardLocalRootLifts.A,
      KPLocalCover.sectionMap, KubotaRankTwo.d]
    have hm : (Matrix.GeneralLinearGroup.mkOfDetNeZero
        (!![(1 : KPHilbert.Completion F v), 0; 0, 1]) (by simp)) =
        (1 : Matrix.GeneralLinearGroup (Fin 2) (KPHilbert.Completion F v)) := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp
    change KPLocalCover.CubicGL2Raw.mk _ 1 = KPLocalCover.CubicGL2Raw.mk 1 1
    rw [hm]
  change KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12
      (KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 1)) = 1
  rw [ht, map_one, map_one]

theorem first_root_derivatives_nondegenerate (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R)
    (J : FirstRootProjected R N A B) :
    (∀ v, fourier R J.base.sources.dq
      (firstRootDerivatives R J.cutoffs (J.base.realization.theta v)) 1 ≠ 0) ∧
    (∀ v, firstRootDerivatives R J.cutoffs (J.base.realization.theta v) ≠ 0) ∧
    Nontrivial (Functions R) := by
  have hm : firstRootMultiplier R J.cutoffs (1 : R.A.G) = 1 := by
    simp [firstRootMultiplier, DHCubic.angular]
  have hp (v : R.A.UnitQuotient) : fourier R J.base.sources.dq
      (firstRootDerivatives R J.cutoffs (J.base.realization.theta v)) 1 ≠ 0 := by
    rw [← diagonal_one R,
      RootDerivatives.firstRootDerivatives_period R N A B J v 1, hm, one_mul, J.radial]
    exact FiniteWhittakerProjectors.radialProfile_one_ne_zero R J.cutoffs
  have hn (v : R.A.UnitQuotient) :
      firstRootDerivatives R J.cutoffs (J.base.realization.theta v) ≠ 0 := by
    intro hz
    apply hp v
    rw [hz]
    simp [MomentSources.fourier]
  exact ⟨hp, hn, inferInstance⟩

end DedekindZetaZeroFree.ThetaExpansion

end

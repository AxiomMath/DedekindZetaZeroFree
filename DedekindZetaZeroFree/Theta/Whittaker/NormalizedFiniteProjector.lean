module

public import DedekindZetaZeroFree.Theta.Whittaker.DifferentiatedTensorFactorization
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.ProjectedRealization

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources ThetaExpansion NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem finite_projector_native
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R)
    (hNative : SourceNativeLie R A.base.factorization) :
    ∃ J : FirstRootProjected R N A B, SourceNativeLie R J.base.factorization := by
  obtain ⟨C,I,inst,c,t,he,hle,hsub,hcut⟩ := FiniteWhittakerProjectors.cutoff_word_exists R A B
  letI := inst
  obtain ⟨Q,T,hdq,hpin⟩ := projected_realization R  hR A.base I c t
    (Finset.univ : Finset R.A.Sf).toList
  have hrad (v : R.A.UnitQuotient) (y : R.A.G) :
      fourier R Q.dq (T.theta v) (diagonal R y) = firstRootRadialProfile R C y := by
    rw [hdq,hpin]
    exact hcut v y
  have hd1 : diagonal R (1 : R.A.G) = 1 := by
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
    rw [ht,map_one,map_one]
  have hn (v : R.A.UnitQuotient) : fourier R Q.dq (T.theta v) 1 ≠ 0 := by
    rw [← hd1,hrad]
    exact FiniteWhittakerProjectors.radialProfile_one_ne_zero R C
  obtain ⟨D,hDN,hM,hH,E⟩ := projected_factorization_native R A.base I c t T hdq hpin hn hNative
  let base : JointExteriorCoefficientSources R N := {
    aligned := hR
    transport := N
    transport_exact := rfl
    sources := Q
    realization := T
    factorization := D
    localHaarTransport := fun q => by
      have hh := A.base.localHaarTransport q
      rw [A.base.transport_exact] at hh
      exact hh.trans (congrArg (fun μ => ENNReal.ofReal (PoissonS.integerVolume F q) • μ) (hH q).symm)
    exterior := E }
  exact ⟨⟨C,he,hle,hsub,base,hrad⟩,hDN⟩
end DedekindZetaZeroFree.RootDerivatives

end

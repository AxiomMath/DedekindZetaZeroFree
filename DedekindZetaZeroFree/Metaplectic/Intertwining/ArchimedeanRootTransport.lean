module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Bruhat.OpenCellSummand

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem archDiagonalIdele_lift (u : InfinitePlace F → ℝ) :
    KPRationalAdelicSplitting.pglA F ζ hζ (archDiagonalIdele F ζ hζ u) =
      (KPContFlatArchDiagonalMultiplier.aInfinity F ζ hζ u).val := by
  unfold KPRationalAdelicSplitting.pglA KPRationalAdelicSplitting.A
    KPContFlatArchDiagonalMultiplier.aInfinity KPGlobalTorusFunctionData.torusArchChart
    KPGlobalTorusFunctionData.archDiagonalLift
  apply congrArg
  apply congrArg
  ext v
  change KPStandardLocalRootLifts.A F ζ hζ v
    (Units.map (KPAdelicCoverRestrictedProduct.adeleEval F v)
      (archDiagonalIdele F ζ hζ u)) = KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ
        (fun w => (Real.exp (u w) : ℂ)) v
  cases v with
  | inr q =>
    simp only [KPRationalAdelicSplitting.ATuple, KPRationalAdelicSplitting.ACoordinates,
      archDiagonalIdele, KPAdelicCoverRestrictedProduct.adeleEval,
      KPGlobalTorusFunctionData.archDiagonalTuple]
    exact KPStandardLocalRootLifts.A_one F ζ hζ (Sum.inr q)
  | inl w =>
    simp only [KPRationalAdelicSplitting.ATuple, KPRationalAdelicSplitting.ACoordinates,
      archDiagonalIdele, KPAdelicCoverRestrictedProduct.adeleEval,
      KPGlobalTorusFunctionData.archDiagonalTuple]
    congr 1
    apply Units.ext
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm (Real.exp (u w) : ℂ) = _
    simp

theorem forward_root_arch_transport (u : InfinitePlace F → ℝ) (x : Adeles F) :
    ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x *
      (KPContFlatArchDiagonalMultiplier.aInfinity F ζ hζ u).val =
    (KPContFlatArchDiagonalMultiplier.aInfinity F ζ hζ (fun w => -u w)).val *
      (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ
        (x * ((archDiagonalIdele F ζ hζ u)⁻¹).val)) := by
  have hN : ∀ x, KPGlobalTorusFunctionData.N F ζ hζ x =
      KPRationalAdelicSplitting.pglN F ζ hζ x := by
    intro x
    rfl
  rw [← archDiagonalIdele_lift, hN, mul_assoc,
    KPRationalAdelicSplitting.quotient_upper_diagonal, ← mul_assoc]
  change KPRationalAdelicSplitting.pglW F ζ hζ *
    KPRationalAdelicSplitting.pglA F ζ hζ (archDiagonalIdele F ζ hζ u) * _ = _
  rw [KPRationalAdelicSplitting.quotient_weyl_diagonal,
    ← archDiagonalIdele_neg, archDiagonalIdele_lift, mul_assoc]
  rfl

theorem forward_integrand_arch_transport
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (s : ℂ) (v : S) (u : InfinitePlace F → ℝ) (x : Adeles F) (g : Cover F ζ hζ) :
    KPContActualSphericalFlatStage.L F ζ hζ U ι s v
      (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x *
        ((KPContFlatArchDiagonalMultiplier.aInfinity F ζ hζ u).val * g)) =
    Complex.exp (-(((4 : ℂ) / 3 + 2 * s) * ((∑ w, u w : ℝ) : ℂ))) *
      KPContActualSphericalFlatStage.L F ζ hζ U ι s v
        (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ
          (x * ((archDiagonalIdele F ζ hζ u)⁻¹).val) * g) := by
  rw [← mul_assoc, forward_root_arch_transport, mul_assoc]
  have h := KPContFlatArchDiagonalMultiplier.flatR_covariance F ζ hζ s
    (fun w => -u w) (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι v)
    (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ
      (x * ((archDiagonalIdele F ζ hζ u)⁻¹).val) * g)
  change (KPContFlatSourceRecipe.flatR F ζ hζ s
    (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι v)).val _ =
    Complex.exp _ * (KPContFlatSourceRecipe.flatR F ζ hζ s
      (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι v)).val _
  simpa only [Finset.sum_neg_distrib, Complex.ofReal_neg, mul_neg] using h

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end

module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightInvariantDifferentialWords
public import DedekindZetaZeroFree.Theta.Periods.SphericalTensorResidueData
public import DedekindZetaZeroFree.Theta.Profiles.FirstRootSphericalRadialModel

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory RootDerivatives
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def sphericalHCSpan (R : PrincipalMellin.ActualRecipe S η) (f : Functions R) :
    Submodule ℂ (Functions R) :=
  Submodule.span ℂ {h | ∃ (a : Group R)
    (word : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))),
    h = KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a
      (KPContActualSphericalRightFieldIdentification.actualRightWord
        F R.A.zeta12 R.A.primitive_zeta12 word f)}

structure SphericalTransportData (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N) where
  tensor : PreparedSphericalTensor R A.factorization
  localForm : ∀ w : InfinitePlace F,
    KPCplxActualImage.Theta KPReferenceChange.StandardComplexImage.frequency →L[ℂ] ℂ
  restriction : ∀ w z, localForm w (coreInStandardImage z) = A.factorization.ell (Sum.inl w) z
  whittaker : ∀ w, localForm w ∈ localWhittakerSpace _
    (KPCplxActualImage.Theta KPReferenceChange.StandardComplexImage.frequency)
    (KPActualReflectionData.StandardLocalSource.complexRootAction R.A w)
    (KPActualReflectionData.StandardLocalSource.complexRawPsi w).toAddChar.toMonoidHom
  seed_nonzero : ∀ w, localForm w sphericalSeed ≠ 0
  period_nonzero : fourier R A.sources.dq tensor.value 1 ≠ 0
  source_detected : ∃ v, (A.sources.flat v).val 0 ≠ 0 ∧ A.realization.theta v ≠ 0 ∧
    fourier R A.sources.dq (A.realization.theta v) 1 ≠ 0
  arch_product : ∀ y : R.A.G,
    fourier R A.sources.dq tensor.value (diagonal R (y.1, 1)) =
      ∏ w : InfinitePlace F, localForm w
        (KPReferenceChange.StandardComplexImage.action R.A w
          (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) (y.1 w)) sphericalSeed)
  core_generated : ∀ x, A.factorization.coreMap x ∈ sphericalHCSpan R tensor.value

end DedekindZetaZeroFree.ThetaExpansion

end

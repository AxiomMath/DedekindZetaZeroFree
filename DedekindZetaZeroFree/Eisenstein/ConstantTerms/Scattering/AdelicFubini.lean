module

public import DedekindZetaZeroFree.Adeles.Haar.AdditiveCoordinateDecomposition
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Scattering.AdelicCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct MomentSources KPLiteralRaw
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (N : TraceHaarTransport R)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C)
  (plusReference R.A P C) (bad R.A P C)
attribute [local irreducible] coreFlatInsertion
set_option backward.isDefEq.respectTransparency true

theorem coreScattering_split_integrable (x : V) (q : KPFinitePlace F)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : G F ζ hζ) :
    letI := N.finiteHaar_add q
    Integrable (fun p : AdditiveCoordinate.Away F q × q.adicCompletion F =>
      (coreFlatInsertion R P C x).val s
        (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ
          (p.1.val + KPRationalAdelicSplitting.localAdele F (Sum.inr q) p.2) * g))
      ((AdditiveCoordinate.awayMeasure F q (N.finiteHaar q)).prod (N.finiteHaar q)) := by
  letI := N.finiteHaar_add q
  exact (AdditiveCoordinate.join_measurePreserving F q (N.finiteHaar q)).integrable_comp_of_integrable
    (coreScattering_integrable R P C x s hs g)

theorem coreScattering_fubini (x : V) (q : KPFinitePlace F)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : G F ζ hζ) :
    letI := N.finiteHaar_add q
    coreScattering R P C x s g =
      ∫ u : AdditiveCoordinate.Away F q,
        (∫ y : q.adicCompletion F, (coreFlatInsertion R P C x).val s
          (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ
            (u.val + KPRationalAdelicSplitting.localAdele F (Sum.inr q) y) * g) ∂N.finiteHaar q)
        ∂AdditiveCoordinate.awayMeasure F q (N.finiteHaar q) := by
  letI := N.finiteHaar_add q
  let e : (AdditiveCoordinate.Away F q × q.adicCompletion F) ≃ₜ KPAdeles F :=
    { toEquiv := (AdditiveCoordinate.join F q).toEquiv
      continuous_toFun := AdditiveCoordinate.continuous_join F q
      continuous_invFun := AdditiveCoordinate.continuous_join_symm F q }
  have hi := coreScattering_split_integrable R P C N x q s hs g
  have he := (AdditiveCoordinate.join_measurePreserving F q (N.finiteHaar q)).integral_comp
    e.measurableEmbedding
    (fun y => (coreFlatInsertion R P C x).val s
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ y * g))
  exact he.symm.trans (integral_prod _ hi)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end

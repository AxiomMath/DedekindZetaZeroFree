module

public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.ArchimedeanChamber
public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.FlatFiberVector

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct BigOperators NNReal
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField KPGlobalTorusFiniteStages KPLiteralRaw KPAdelicCoverRestrictedProduct
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open KPGlobalTorusPeriodizationInverse hiding productModel
attribute [local instance] KPGlobalTorusPeriodizationInverse.modelTopology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "Core" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem rawCoreValue_normOne_torus (x : Core)
    (u g : Raw R.A) (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (a d : InfinitePlace F → ℂˣ) (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (.inr q) (u (.inr q)))
    (hp : ∀ v, complexMatrix R.A v (u (.inl v)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a v) (d v) 0)
    (he : scalarQuotient F ζ hζ (amalgamation F ζ hζ u) = e.val)
    (hδ : KPGlobalTorusFunctionData.delta F ζ hζ e = 1) :
    rawCoreValue R.A P C (u*g) x =
      (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F ζ hζ P
        (rawCoreFiber R.A P C g x)).val.val e := by
  rw [rawCoreValue_fiber, rawCoreFiber_torus R.A P C x u g t a d (fun _ => 0) e ht hp he,
    map_smul, map_smul]
  change (KPGlobalTorusFunctionData.deltaHalf F ζ hζ e *
    ((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℂ)) *
    ((untwistRational F ζ hζ).symm (unitaryPeriodization F ζ hζ P
      (rightAction F ζ hζ (productModel F ζ hζ P) e (rawCoreFiber R.A P C g x)))).val.val 1 =
    ((untwistRational F ζ hζ).symm (unitaryPeriodization F ζ hζ P
      (rawCoreFiber R.A P C g x))).val.val e
  rw [unitaryPeriodization_intertwines, retwistRational_formula, rightAction_formula,
    one_mul, retwistRational_formula]
  have hn : KPGlobalCenterRationalCharacter.nu F ζ hζ e = 1 := by
    change KPGlobalCenterRationalCharacter.sixthPower (KPGlobalTorusFunctionData.delta F ζ hζ e) = 1
    rw [hδ, map_one]
  simp [KPGlobalTorusFunctionData.deltaHalf, hδ, hn]

theorem height_normOne_torus (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (hδ : KPGlobalTorusFunctionData.delta F ζ hζ e = 1) (g : MomentSources.Group R) :
    ThetaExpansion.iwasawaLogHeight R (e.val*g) = ThetaExpansion.iwasawaLogHeight R g := by
  change KPContFlatFullProductIwasawa.alpha F ζ hζ (e.val*g) =
    KPContFlatFullProductIwasawa.alpha F ζ hζ g
  have hN : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  simpa [hδ, hN] using KPContFlatFullProductIwasawa.alpha_borel_mul F ζ hζ e 0 g

theorem coreFlatFiber_normOne_value (x : Core) (z : ℂ) (g : Raw R.A)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (hδ : KPGlobalTorusFunctionData.delta F ζ hζ e = 1) :
    (coreFlatFiber R P C x z g).val.val e =
      (coreFlatInsertion R P C x).val z
        (e.val * scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) := by
  obtain ⟨u,t,a,d,ht,hp,he⟩ := EisensteinReferenceSections.TorusNorms.raw_lifts F ζ hζ e
  rw [← he, ← map_mul, ← map_mul, coreFlatInsertion_raw]
  change _ = Complex.exp (z * (ThetaExpansion.iwasawaLogHeight R
    (scalarQuotient F ζ hζ (amalgamation F ζ hζ (u*g))) : ℂ)) * rawCoreValue R.A P C (u*g) x
  rw [rawCoreValue_normOne_torus R P C x u g t a d e ht hp he hδ]
  have hh : ThetaExpansion.iwasawaLogHeight R
      (scalarQuotient F ζ hζ (amalgamation F ζ hζ (u*g))) =
      ThetaExpansion.iwasawaLogHeight R (scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) := by
    rw [map_mul, map_mul, he]
    exact height_normOne_torus R e hδ _
  rw [hh]
  rfl

theorem chamberRaw_spec (y : KPGlobalTorusFunctionData.Adeles F) :
    scalarQuotient F ζ hζ (amalgamation F ζ hζ (CofactorChamber.chamberRaw F ζ hζ y)) =
      KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ y := by
  simp only [CofactorChamber.chamberRaw, map_mul]
  rfl

theorem coreFlatFiber_chamber_normOne_value (x : Core) (z : ℂ)
    (y : KPGlobalTorusFunctionData.Adeles F) (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (hδ : KPGlobalTorusFunctionData.delta F ζ hζ e = 1) :
    (coreFlatFiber R P C x z (CofactorChamber.chamberRaw F ζ hζ y)).val.val e =
      (coreFlatInsertion R P C x).val z
        (e.val * (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ y)) := by
  rw [coreFlatFiber_normOne_value R P C x z _ e hδ, chamberRaw_spec]

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end

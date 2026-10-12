module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightChartJetsAndFlowWords
public import DedekindZetaZeroFree.Eisenstein.Continuation.LocalJointPoleClearingAndContinuity
public import DedekindZetaZeroFree.Eisenstein.Continuation.LocallyDiscretePoleLoci
public import DedekindZetaZeroFree.Eisenstein.Continuation.RegularSymmetriesAndUniformRightLevels
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ComplexStandardIntertwinerGerm
public import DedekindZetaZeroFree.LFunctions.Hecke.EntireRegularizations
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveTrivialCharacter
public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarCompactPicturesAndLocalQuotientTensors

@[expose] public section

noncomputable section

set_option maxHeartbeats 4000000

set_option synthInstance.maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

open scoped Classical NumberField

open NumberField IsDedekindDomain

noncomputable section

open scoped Classical NumberField

open DedekindZetaZeroFree

open _root_.DedekindZetaZeroFree.ScalarRationalProductTransport renaming scalar_injective → scalar_injective

namespace DedekindZetaZeroFree.KPGlobalResidualKernel.IntertwinerRegularization.FactorizationSources.NormalizedCoordinateAnalyticity

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local notation "Q" => KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ

local notation "V" => KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ Q

theorem zero_pol : (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) = Q := by
  unfold KPMsRationalCompactCrossPairing.sourcePolarization KPGlobalTorusBorelTwistCompatibility.twist
  congr 1
  ext h
  change ((KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).character h : ℂ) * KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ 0 h.val = ((KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).character h : ℂ)
  simp [KPGlobalTorusBorelTwistCompatibility.normPower]

def castScalar (P P' : KPGlobalTorusFunctionData.Polarization F ζ hζ) (h : P = P') :
    KPGlobalTorusFunctionData.BorelFunctions F ζ hζ P →ₗ[ℂ]
      KPGlobalTorusFunctionData.BorelFunctions F ζ hζ P' := by
  subst P'
  exact LinearMap.id

private theorem castScalar_apply (P P' : KPGlobalTorusFunctionData.Polarization F ζ hζ) (h : P = P')
    (v : KPGlobalTorusFunctionData.BorelFunctions F ζ hζ P) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    (castScalar F ζ hζ P P' h v).val g = v.val g := by
  subst P'; rfl

def scalarZero : V →ₗ[ℂ] KPMsRationalCompactCrossPairing.Source F ζ hζ 0 :=
  (castScalar F ζ hζ Q (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) (zero_pol F ζ hζ).symm).comp
    (KPGlobalTorusBorelTwistCompatibility.scalarSection F ζ hζ Q)

private theorem scalarZero_value (v : V) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    (scalarZero F ζ hζ v).val g = (v.val.val g).val.val 1 := by
  exact castScalar_apply F ζ hζ _ _ _ _ _

private theorem scalarZero_injective : Function.Injective (scalarZero F ζ hζ) := by
  intro v w h
  apply scalar_injective F ζ hζ Q
  funext g
  exact (scalarZero_value F ζ hζ v g).symm.trans ((congrArg (fun t => t.val g) h).trans (scalarZero_value F ζ hζ w g))

local instance scalarStageInducedAdd : AddCommGroup V := KPGlobalTorusBorelTwistCompatibility.inducedAddGroup F ζ hζ Q

variable (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)

variable (typStage : KPGlobalEisensteinData.CompactTypeStage
    ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)).comp D.K.subtype))

set_option maxHeartbeats 4000000

set_option backward.isDefEq.respectTransparency false

abbrev scalarLiftStage (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (typStage : KPGlobalEisensteinData.CompactTypeStage
      ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)).comp D.K.subtype)) : Submodule ℂ V :=
  typStage.space.comap (scalarZero F ζ hζ)

def stageScalar : scalarLiftStage F ζ hζ D typStage →ₗ[ℂ] typStage.space :=
  ((scalarZero F ζ hζ).comp (scalarLiftStage F ζ hζ D typStage).subtype).codRestrict typStage.space (fun v => v.property)

theorem stageScalar_injective : Function.Injective (stageScalar F ζ hζ D typStage) := by
  intro v w h
  apply Subtype.ext
  apply scalarZero_injective F ζ hζ
  exact congrArg Subtype.val h

instance stageFinite : FiniteDimensional ℂ (scalarLiftStage F ζ hζ D typStage) := by
  let := typStage.finiteDimensional
  exact @FiniteDimensional.of_injective ℂ (scalarLiftStage F ζ hζ D typStage) _
    (scalarLiftStage F ζ hζ D typStage).addCommGroup (scalarLiftStage F ζ hζ D typStage).module
    typStage.space typStage.space.addCommGroup typStage.space.module
    (stageScalar F ζ hζ D typStage) (stageScalar_injective F ζ hζ D typStage) typStage.finiteDimensional

end DedekindZetaZeroFree.KPGlobalResidualKernel.IntertwinerRegularization.FactorizationSources.NormalizedCoordinateAnalyticity

end

end

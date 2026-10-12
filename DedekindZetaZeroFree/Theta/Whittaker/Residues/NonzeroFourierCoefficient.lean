module

public import DedekindZetaZeroFree.Adeles.Characters.StandardAdditiveCharacter
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Casimir.ArchimedeanInvariantKernel
public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.NonzeroResidueExistence
public import DedekindZetaZeroFree.Theta.Periods.Residues.UpperAndSL2Invariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages ThetaExpansion TensorActionSource
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C)
  (plusReference R.A P C) (bad R.A P C)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem coreResidue_zero_of_period_zero (x : V)
    (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (hψ : KPReflectionSpec.NontrivialCharacter ψ)
    (μ : Measure (KPAdditiveQuotient F)) (hμ : μ.IsAddHaarMeasure)
    (hp : ∀ g, KPLiteralRaw.period F ζ hζ ψ μ
      (KPLiteralRaw.rightAction F ζ hζ g (coreResidue R P C x)) = 0) :
    coreResidue R P C x = 0 := by
  have hu := coreResidue_upper_invariant_of_period_zero R P C x ψ hψ μ hμ hp
  have hsl := coreResidue_sl2_invariant_of_upper_invariant R P C x hu
  have ha := ResidualArchSL2.arch_invariant_of_sl2_invariant F ζ hζ
    (coreResidue R P C x) hsl
  have hn := (coreResidue_raw_automorphic R P C x).1.2.1
  have hd : 0 < KPCuspLogShape.dimension F := KPCuspLogShape.dimension_pos F
    (InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by decide : 2 < 12) hζ)
  have heig : KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) 0 ≠ 0 := by
    rw [KPContinuation.spectralCoordinate_zero]
    have hdc : ((KPCuspLogShape.dimension F : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    exact div_ne_zero (mul_ne_zero (by norm_num) hdc) (by norm_num)
  funext g
  have hc := ResidualArchSL2.casimir_zero_of_arch_invariant (coreResidue R P C x) hn ha g
  rw [coreResidue_native_eigen R P C x g] at hc
  exact (mul_eq_zero.mp hc).resolve_left heig

theorem exists_coreResidue_period_ne_zero
    (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (hψ : KPReflectionSpec.NontrivialCharacter ψ)
    (μ : Measure (KPAdditiveQuotient F)) (hμ : μ.IsAddHaarMeasure) :
    ∃ (x : V) (g : MomentSources.Group R), KPLiteralRaw.period F ζ hζ ψ μ
      (KPLiteralRaw.rightAction F ζ hζ g (coreResidue R P C x)) ≠ 0 := by
  obtain ⟨x,hx⟩ := CofactorChamber.exists_coreResidue_ne_zero_unconditional R P C
  by_contra h
  push Not at h
  exact hx (coreResidue_zero_of_period_zero R P C x ψ hψ μ hμ (h x))

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end

module

public import DedekindZetaZeroFree.Theta.Whittaker.SexticRadialValues
public import DedekindZetaZeroFree.Theta.Whittaker.ReferenceSphericalShellValues

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem exterior_whittaker_value_generator_pow_nat (R : PrincipalMellin.ActualRecipe S η)
    (hR : RootAligned R) {N : TraceHaarTransport R} (C : JointHaarFactorizedSources R N)
    (hW : ExteriorWhittakerEquivariance R C) (p : ThetaBranch.ExteriorPrime R.A) (e : ℕ) :
    exteriorWhittakerValue R C p (exteriorCompletionGenerator R p ^ (e : ℤ)) =
      sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p) (Characters.psi R p) (e : ℤ) := by
  letI : Fintype (IsLocalRing.ResidueField
      (ValuativeRel.valuation (p.val.adicCompletion F)).integer) := Fintype.ofFinite _
  obtain ⟨π, hπ, hp⟩ := ExteriorWhittakerValues.ShellArithmetic.negativeGenerator_integer_irreducible R p
  have hv := ExteriorWhittakerValues.ActualStoredShells.stored_nonnegative_values R C hW p
    (ExteriorWhittakerValues.ShellArithmetic.exterior_tame_char R p) (ExteriorWhittakerValues.exterior_not_bad p)
    (ExteriorWhittakerValues.exterior_good_six p) π hπ (ExteriorWhittakerValues.ShellArithmetic.tracePsi p.val)
    (ExteriorWhittakerValues.ShellArithmetic.tracePsi_continuous p.val)
    (ExteriorWhittakerValues.ShellArithmetic.tracePsi_unitary p.val)
    (ExteriorWhittakerValues.ShellArithmetic.tracePsi_conductorZero R p π hπ) (fun _ => rfl)
    (ExteriorWhittakerValues.ShellArithmetic.residueChi R p)
    (ExteriorWhittakerValues.ShellArithmetic.residueChi_unitCharacter R hR p)
    (ExteriorWhittakerValues.ShellArithmetic.residuePsi R p)
    (ExteriorWhittakerValues.ShellArithmetic.residuePsi_trace R p π hπ hp) e
  have hu : ExteriorWhittakerValues.ActualJacquet.uniformizerUnit F p.val π hπ = -exteriorCompletionGenerator R p :=
    Units.ext hp
  rw [hu, ExteriorWhittakerValues.ShellArithmetic.negativeGenerator_value R hR C p e,
    ExteriorWhittakerValues.ShellArithmetic.radialValue_eq_sextic R p] at hv
  exact hv

end DedekindZetaZeroFree.ThetaExpansion

end

module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SixthRootAlignment

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.MomentSources
open scoped NumberField Classical
open NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
structure SignedUniformizerTransport (R : PrincipalMellin.ActualRecipe S η) where
  uniformizer : ∀ p : ThetaBranch.ExteriorPrime R.A, (p.val.adicCompletion F)ˣ
  uniformizer_norm : ∀ p, ‖(uniformizer p : p.val.adicCompletion F)‖ = (R.A.exteriorNorm (ThetaBranch.primeIdeal R.A p))⁻¹
  witnessPsi : ∀ p : ThetaBranch.ExteriorPrime R.A, AddChar (DHCubic.Residue F p.val) ℂ
  witnessPsi_trace : ∀ p (t : 𝓞 F), witnessPsi p (Ideal.Quotient.mk p.val.asIdeal t) =
    (ResidueTrace.localTraceCharacter p.val
      (algebraMap (𝓞 F) (p.val.adicCompletion F) t / (uniformizer p : p.val.adicCompletion F)) : ℂ)
  delta : ∀ p : ThetaBranch.ExteriorPrime R.A, (DHCubic.Residue F p.val)ˣ
  delta_actual : ∀ p (t : 𝓞 F), Ideal.Quotient.mk p.val.asIdeal t = (delta p : DHCubic.Residue F p.val) →
    ‖algebraMap (𝓞 F) (p.val.adicCompletion F) t +
      (uniformizer p : p.val.adicCompletion F) /
        algebraMap F (p.val.adicCompletion F)
          (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)‖ < 1
  signed_shift : ∀ p, Characters.psi R p = (witnessPsi p).mulShift (delta p)

end DedekindZetaZeroFree.MomentSources

end

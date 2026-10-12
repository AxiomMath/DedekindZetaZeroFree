module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SixthRootAlignment

@[expose] public section

namespace DedekindZetaZeroFree.MomentSources
noncomputable section
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]

theorem separated_summand_norm_summable
    (A : SArithmeticData F) (G : ThetaBranch.AllowedRecipe A)
    (U : ThetaBranch.UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ThetaBranch.ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p, (ψ p).IsPrimitive)
    (L : Fˣ →* ℂ) (hL : ∀ x, ‖L x‖ = 1)
    (H : A.UnitQuotient → A.V → ℝ → ℂ)
    (hH : RMSeparatedExpansion.FiniteProfileFamily A H)
    (u : A.UnitQuotient) (h d : A.Exterior) (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun i : RMSeparatedExpansion.Index A h =>
      ‖RMSeparatedExpansion.summand A G U σ ψ L (H u) i.1.val d i.2 Z‖) := by
  obtain ⟨K, hK, hbound⟩ :=
    RMParameterAbsorption.finiteProfileFamily_reciprocal_bound A H hH
  let W : RMParameterAbsorption.CompactMajorantIndex A h → ℝ := fun k =>
    A.exteriorNorm k.1.val.val ^ 2 * positiveRowWeight k.1.val 1 k.2.2
  let c : ℝ := K * A.exteriorNorm d ^ 2 / Z
  let e := RMParameterAbsorption.compactMajorantIndexMap A h
  have hW : Summable W := RMParameterAbsorption.compactWeightedMajorant_summable A h
  have he : Function.Injective e :=
    RMParameterAbsorption.compactMajorantIndexMap_injective A h
  have hs := (hW.comp_injective he).mul_left c
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro i
  have hi := RMParameterAbsorption.summand_positiveRowWeight_bound
    A G U σ ψ hψ L hL (H u) K hK (hbound u) i.1.val d i.2 Z hZ
  convert hi using 1 <;>
    dsimp [c, W, e, RMParameterAbsorption.compactMajorantIndexMap,
      RMSeparatedExpansion.activeSupport] <;> ring

end
end DedekindZetaZeroFree.MomentSources

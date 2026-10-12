module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.HarishChandra.ScalarWordSpan
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.FiniteTranslationLieCommutation

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.HCGeneration
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
local notation "W" => KPContActualSphericalRightFieldIdentification.actualRightWord
  F R.A.zeta12 R.A.primitive_zeta12
local notation "A" => KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12

theorem hcHeckeSpan_right (T : Realization R Q) {f : Functions R}
    (hf : f ∈ hcHeckeSpan T) (a : Group R) : A a f ∈ hcHeckeSpan T := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v, b, w, rfl⟩ := hf
    apply Submodule.subset_span
    refine ⟨v, a * b, w, ?_⟩
    funext g
    simp [KPLiteralRaw.rightAction, mul_assoc]
  | zero => simpa only [map_zero] using (hcHeckeSpan T).zero_mem
  | add f g hf hg ihf ihg =>
    simpa only [map_add] using (hcHeckeSpan T).add_mem ihf ihg
  | smul c f hf ihf => simpa only [map_smul] using (hcHeckeSpan T).smul_mem c ihf

end DedekindZetaZeroFree.FourierContinuation.HCGeneration

end

module

public import DedekindZetaZeroFree.Theta.Periods.DetectedTensorAssembly
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.Wild.MirabolicEmbedding
public import DedekindZetaZeroFree.Theta.Periods.ScalarQuotientsAndFourierDescent

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildCurrentTensor
open MomentSources KPKirillovFiniteTensor KPKirillovGenuineSectionCharts
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
variable (D : TensorActions R N) (W : Finset (KPFinitePlace F))
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
abbrev depth (v : W) := KPAdelicCoverRestrictedProduct.depth F ζ hζ v.val
abbrev depth_valid (v : W) := KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ v.val
abbrev character (v : W) := KPKirillovOrbitMapFaithful.ψ F v.val
abbrev fiber (v : W) := actualLocal R D.finiteData (Sum.inr v.val)
abbrev action (v : W) := WildActualMirabolic.rho F ζ hζ v.val
  (D.finiteData v.val).inducing (D.finiteData v.val).inducing.polarization
  (D.finiteData v.val).haar (D.finiteData v.val).haar_integer

def localData : LocalEmbeddingData F ζ hζ W (depth (R := R) W) (depth_valid (R := R) W)
    (character W) (fiber D W) (action D W) where
  character_lc v := (KPWildCompactProjectorKirillov.ActualInput.standardCharacter_properties F v.val).1
  character_ne v := (KPWildCompactProjectorKirillov.ActualInput.standardCharacter_properties F v.val).2.1
  smooth_genuine v := ⟨WildActualMirabolic.image_smooth F ζ hζ v.val
    (D.finiteData v.val).inducing (D.finiteData v.val).inducing.polarization
    (D.finiteData v.val).haar (D.finiteData v.val).haar_integer _ (depth_valid (R := R) W v),
    WildActualMirabolic.image_genuine F ζ hζ v.val
    (D.finiteData v.val).inducing (D.finiteData v.val).inducing.polarization
    (D.finiteData v.val).haar (D.finiteData v.val).haar_integer⟩
  j v := WildActualMirabolic.embedding F ζ hζ v.val
    (D.finiteData v.val).inducing (D.finiteData v.val).inducing.polarization
    (D.finiteData v.val).haar (D.finiteData v.val).haar_integer _ (depth_valid (R := R) W v)
  injective v := WildActualMirabolic.embedding_injective F ζ hζ v.val
    (D.finiteData v.val).inducing (D.finiteData v.val).inducing.polarization
    (D.finiteData v.val).haar (D.finiteData v.val).haar_integer _ (depth_valid (R := R) W v)
  equivariant v p x := WildActualMirabolic.embedding_equivariant F ζ hζ v.val
    (D.finiteData v.val).inducing (D.finiteData v.val).inducing.polarization
    (D.finiteData v.val).haar (D.finiteData v.val).haar_integer _ (depth_valid (R := R) W v) p x
  evaluation v := by
    apply TensorProduct.ext'
    intro f e
    exact WildActualMirabolic.embedding_evaluation F ζ hζ v.val
      (D.finiteData v.val).inducing (D.finiteData v.val).inducing.polarization
      (D.finiteData v.val).haar (D.finiteData v.val).haar_integer _ (depth_valid (R := R) W v) f e

theorem exists_fixed_injective :
    ∃ f : ∀ v, ScalarSections F ζ hζ W (depth (R := R) W) (character W) v,
      (∀ v, sectionValue F ζ hζ v.val (depth (R := R) W v) (character W v) (f v) 1 = 1) ∧
      Function.Injective (KPWildNormalizedCoefficientInsertion.fixedCoefficientMap F ζ hζ W
        (depth (R := R) W) (depth_valid (R := R) W) (character W) (fiber D W) (action D W)
        (localData D W) f) := by
  choose f hf using fun v : W => KPWildNormalizedCoefficientInsertion.exists_normalized_scalar_section
    F ζ hζ v.val (depth (R := R) W v) (depth_valid (R := R) W v) (character W v)
    ((localData D W).character_lc v)
  exact ⟨f,hf,KPWildNormalizedCoefficientInsertion.fixedCoefficientMap_injective F ζ hζ W
    (depth (R := R) W) (depth_valid (R := R) W) (character W) (fiber D W) (action D W)
    (localData D W) f hf⟩
end DedekindZetaZeroFree.FourierContinuation.WildCurrentTensor

end

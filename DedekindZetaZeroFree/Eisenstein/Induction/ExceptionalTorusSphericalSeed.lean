module

public import DedekindZetaZeroFree.Eisenstein.Induction.CompactIwasawaGeometry
public import DedekindZetaZeroFree.Eisenstein.Induction.SectionKFinite
public import DedekindZetaZeroFree.Metaplectic.Torus.CompatibleCharacterFibers

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField
open scoped Classical NumberField Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

structure InducedSourceSeed (R : PrincipalMellin.ActualRecipe S η) where
  value : Functions R
  induced : KPLiteralRaw.Induced F R.A.zeta12 R.A.primitive_zeta12 0 value
  kfinite : KPLiteralRaw.KFinite F R.A.zeta12 R.A.primitive_zeta12 (fullProductCompact R) value
  level : KPGlobalTorusFunctionData.FiniteLevel F R.A.zeta12 R.A.primitive_zeta12
  level_le : KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 level ≤ fullProductCompact R
  fixed : ∀ g u, u ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 level →
    value (g * u) = value g
  spherical : ∀ (p : KPFinitePlace F), p ∉ R.A.Sf →
    ∀ k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p),
    k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) →
    ∀ g, value (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) k)) = value g
  at_one : value 1 ≠ 0

theorem induced_source_seed_exists (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R) :
    Nonempty (InducedSourceSeed R) := by
  obtain ⟨P, C, _, hC⟩ := EisensteinReferenceSections.FrozenFibers.exists_model_fibers R.A R.classKilled
  exact ⟨{
    value := EisensteinReferenceSections.RawSource.scalarValue F R.A.zeta12 R.A.primitive_zeta12 P C
    induced := EisensteinReferenceSections.SourceSmooth.scalar_induced F R.A.zeta12 R.A.primitive_zeta12 P C
    kfinite := EisensteinReferenceSections.SourceKFinite.scalar_kfinite R P C
    level := EisensteinReferenceSections.SourceLevels.level F R.A.zeta12 R.A.primitive_zeta12 P C
    level_le := EisensteinReferenceSections.CompactSource.sourceLevel_le R P C
    fixed := EisensteinReferenceSections.SourceLevels.scalar_fixed F R.A.zeta12 R.A.primitive_zeta12 P C
    spherical := EisensteinReferenceSections.CompactSource.scalar_spherical R P C hC
    at_one := by rw [EisensteinReferenceSections.RawSource.scalarValue_one]; exact one_ne_zero }⟩

end DedekindZetaZeroFree.ThetaExpansion

end

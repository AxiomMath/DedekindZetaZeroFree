module

public import DedekindZetaZeroFree.Eisenstein.Induction.CompactIwasawaGeometry
public import DedekindZetaZeroFree.Eisenstein.Induction.Height.IwasawaRegularity

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open NumberField
namespace DedekindZetaZeroFree.HeightGeometry
open ThetaExpansion MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem height_continuous (R : PrincipalMellin.ActualRecipe S η) : Continuous (iwasawaLogHeight R) :=
  logModulus_continuous F R.A.zeta12 R.A.primitive_zeta12 (fullProductIwasawaData R)

theorem height_right_chart_smooth (R : PrincipalMellin.ActualRecipe S η) (g : Group R) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => iwasawaLogHeight R (g * KPGlobalResidualConstruction.archChart
        F R.A.zeta12 R.A.primitive_zeta12 z)) (KPGlobalResidualConstruction.archDomain F) :=
  logModulus_right_chart_smooth F R.A.zeta12 R.A.primitive_zeta12
    (fullProductIwasawaData R) (complex_compact_lift_mem_full_product_compact R) g
end DedekindZetaZeroFree.HeightGeometry

end

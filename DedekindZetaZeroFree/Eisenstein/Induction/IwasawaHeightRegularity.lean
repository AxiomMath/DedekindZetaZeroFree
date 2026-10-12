module

public import DedekindZetaZeroFree.Eisenstein.Induction.Height.ContinuityAndSmoothness

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField
open scoped Classical NumberField Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem iwasawa_log_height_regular (R : PrincipalMellin.ActualRecipe S η) :
    Continuous (iwasawaLogHeight R) ∧
    ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => iwasawaLogHeight R (g * KPGlobalResidualConstruction.archChart
        F R.A.zeta12 R.A.primitive_zeta12 x))
      (KPGlobalResidualConstruction.archDomain F) := by
  exact ⟨HeightGeometry.height_continuous R,
    HeightGeometry.height_right_chart_smooth R⟩

end DedekindZetaZeroFree.ThetaExpansion

end

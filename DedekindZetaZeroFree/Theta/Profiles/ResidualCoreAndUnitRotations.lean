module

public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction
namespace ElementaryOutputs

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rationalSplitting : RationalSplitting F ζ hζ where
  lift := QuotientGroup.lift (Subgroup.center (KubotaRankTwo.GL2 F))
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ)) (by
        simpa only [Matrix.GeneralLinearGroup.center_eq_range_scalar,
          KPRationalAdelicSplitting.rationalScalars] using
          KPRationalAdelicSplitting.rationalScalars_le_ker F ζ hζ)
  on_matrix := by intro g; rfl

end ElementaryOutputs
end DedekindZetaZeroFree.KPGlobalResidualConstruction

end

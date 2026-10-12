module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicMaximalCompactness
public import DedekindZetaZeroFree.Metaplectic.Kubota.PGLIwasawaDecomposition
public import DedekindZetaZeroFree.Eisenstein.Induction.IwasawaCompactOverlap

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField
open scoped Classical NumberField Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem full_product_compact_geometry (R : PrincipalMellin.ActualRecipe S η) :
    IsCompact (fullProductCompact R : Set (Group R)) ∧
    ∀ g : Group R, ∃ (t : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12)
      (x : KPAdeles F) (k : fullProductCompact R),
      g = (t.val * KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x) * k.val := by
  exact ⟨full_product_compact_is_compact R, covered_iwasawa_decomposition R⟩

theorem full_product_compact_iwasawa (R : PrincipalMellin.ActualRecipe S η) :
    KPLiteralRaw.IwasawaCompact F R.A.zeta12 R.A.primitive_zeta12 (fullProductCompact R) :=
  ⟨(full_product_compact_geometry R).1, (full_product_compact_geometry R).2, complex_compact_lift_mem_full_product_compact R⟩

def fullProductIwasawaData (R : PrincipalMellin.ActualRecipe S η) :
    KPGlobalTorusBorelTwistCompatibility.IwasawaData F R.A.zeta12 R.A.primitive_zeta12 where
  K := fullProductCompact R
  compact := (full_product_compact_iwasawa R).1
  decomposition := (full_product_compact_iwasawa R).2.1
  overlap := KPLiteralChamber.compact_overlap F R.A.zeta12 R.A.primitive_zeta12
    (fullProductCompact R) (full_product_compact_iwasawa R).1

def iwasawaLogHeight (R : PrincipalMellin.ActualRecipe S η) (g : Group R) : ℝ :=
  Real.log ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F R.A.zeta12 R.A.primitive_zeta12
    (fullProductIwasawaData R) g : NNReal) : ℝ)

end DedekindZetaZeroFree.ThetaExpansion

end

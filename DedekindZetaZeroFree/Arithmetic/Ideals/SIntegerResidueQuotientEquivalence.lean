module

public import DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerResidueQuotientInjectivity
public import DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerResidueQuotientSurjectivity

@[expose] public section

open scoped NumberField
open NumberField

namespace DedekindZetaZeroFree.ArithGaussCRT

noncomputable section
variable {F : Type} [Field F] [NumberField F]

def exteriorQuotientEquiv (A : SArithmeticData F) (I : A.Exterior) :
    (𝓞 F ⧸ I.val) ≃+* (A.R ⧸ A.extendIdeal I) :=
  RingEquiv.ofBijective
    (Ideal.quotientMap (A.extendIdeal I) (algebraMap (𝓞 F) A.R)
      (show I.val ≤ (A.extendIdeal I).comap (algebraMap (𝓞 F) A.R) from
        Ideal.le_comap_map))
    ⟨exteriorQuotientMap_injective A I, exteriorQuotientMap_surjective A I⟩

@[simp] theorem exteriorQuotientEquiv_mk (A : SArithmeticData F) (I : A.Exterior)
    (x : 𝓞 F) :
    exteriorQuotientEquiv A I (Ideal.Quotient.mk I.val x) =
      Ideal.Quotient.mk (A.extendIdeal I) (algebraMap (𝓞 F) A.R x) := rfl

end

end DedekindZetaZeroFree.ArithGaussCRT

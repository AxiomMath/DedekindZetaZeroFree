module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AutomorphicHilbertFlows
public import DedekindZetaZeroFree.Adeles.Quotients.SmoothLocalCharts

@[expose] public section

noncomputable section
open scoped Classical NumberField
open Topology

namespace DedekindZetaZeroFree.KPContSectorCoveredQuotientVocabulary

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev ActualCover := KPSmoothLocalQuotientCharts.ActualCover F ζ hζ

end DedekindZetaZeroFree.KPContSectorCoveredQuotientVocabulary

namespace DedekindZetaZeroFree.KPContActualSphericalRightFieldIdentification

open KPContSectorCoveredQuotientVocabulary
variable (F : Type) [Field F] [NumberField F]

abbrev LieIndex := NumberField.InfinitePlace F × Fin 3 × Fin 2
abbrev groupDimension := Fintype.card (LieIndex F)

def lieEnumeration : Fin (groupDimension F) ≃ LieIndex F :=
  (Fintype.equivFin _).symm

variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def actualRight (b : Fin (groupDimension F)) (f : ActualCover F ζ hζ → ℂ)
    (g : ActualCover F ζ hζ) : ℂ :=
  deriv (fun t : ℝ => f (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPSmoothLocalQuotientCharts.matrixExp F
      (t • Pi.single (lieEnumeration F b) 1)))) 0

def actualRightWord : List (Fin (groupDimension F)) →
    (ActualCover F ζ hζ → ℂ) → ActualCover F ζ hζ → ℂ
  | [], f => f
  | b :: w, f => actualRight F ζ hζ b (actualRightWord w f)

end DedekindZetaZeroFree.KPContActualSphericalRightFieldIdentification

end

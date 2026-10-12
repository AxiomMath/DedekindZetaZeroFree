module

public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.RotationCalculus

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts
open KPCplxCharacterHaar KPCplxIntertwinerEigenvalues

def HasHopfCoordinates (H : ComplexSU2 → Sphere) : Prop :=
  ∀ k, (H k : Ambient) =
    WithLp.toLp 2 (fun i => (compactSphereCoordinate k i).re)

theorem upperTriangular_coe_matrix (a d : ℂˣ) (b : ℂ) :
    ((KPCplxPrincipalSeriesCharts.upperTriangular a d b : KPCplxCharacterHaar.ComplexGL2) :
      Matrix (Fin 2) (Fin 2) ℂ) = !![(a : ℂ), b; 0, (d : ℂ)] := by
  rfl

end DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts

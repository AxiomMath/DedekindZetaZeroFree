module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.ComplexPrincipalSeries.TopologicalImage
public import DedekindZetaZeroFree.Metaplectic.Kubota.GLCoverCoordinates

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField
namespace DedekindZetaZeroFree.KPReferenceChange.StandardCover
open StandardComplexImage KPCplxActualImage KPCplxPrincipalSeriesCharts
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F) (w : InfinitePlace F)

def complexRho : Representation ℂ (G F A.zeta12 A.primitive_zeta12 (Sum.inr w))
    (Theta frequency) where
  toFun g := {
    toFun := action A w g
    map_add' := by
      intro x y
      unfold action
      rw [← smul_add]
      congr 1
      induction matrix A w g using Quotient.inductionOn with
      | _ m => rfl
    map_smul' := by
      intro c x
      unfold action
      have hh : imageAction frequency (matrix A w g) (c • x) =
          c • imageAction frequency (matrix A w g) x := by
        induction matrix A w g using Quotient.inductionOn with
        | _ m => rfl
      rw [hh, smul_comm]
      rfl }
  map_one' := LinearMap.ext (fun x => action_one A w x)
  map_mul' g h := LinearMap.ext (fun x => action_mul A w g h x)

end DedekindZetaZeroFree.KPReferenceChange.StandardCover

end

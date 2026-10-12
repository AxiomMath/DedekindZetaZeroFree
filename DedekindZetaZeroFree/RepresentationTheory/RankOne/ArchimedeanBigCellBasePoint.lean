module

public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPInterface.ResidueConstruction.Raw
open KPGlobalResidualConstruction
open scoped Topology

theorem archChart_base (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    archChart F ζ hζ (archBase F) = 1 := by
  unfold archChart
  dsimp only
  suffices ht : (⟨_, _⟩ : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) =
      (1 : RestrictedProduct (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v)
        (fun v => (KPAdelicCoverRestrictedProduct.compact F ζ hζ v : Set _)) Filter.cofinite) by
    rw [ht, map_one, map_one]
  apply Subtype.ext
  funext v
  cases v <;> simp [archBase] <;> rfl

end DedekindZetaZeroFree.KPInterface.ResidueConstruction.Raw

end

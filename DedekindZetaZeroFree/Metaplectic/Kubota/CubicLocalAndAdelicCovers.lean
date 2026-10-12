module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicRationalSplitting

@[expose] public section

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPCubicCoverConstruction

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev LocalGL2Cover (v : KPHilbert.Place F) := KPLocalCover.CubicGL2Raw F ζ hζ v

abbrev localTopology (v : KPHilbert.Place F) :=
  KPAdelicCoverRestrictedProduct.localTopology F ζ hζ v

theorem local_topological_cover (v : KPHilbert.Place F) :
    letI := localTopology F ζ hζ v
    T2Space (LocalGL2Cover F ζ hζ v) ∧
      LocallyCompactSpace (LocalGL2Cover F ζ hζ v) ∧
      IsTopologicalGroup (LocalGL2Cover F ζ hζ v) ∧
      IsLocalHomeomorph (KPLocalCover.projection F ζ hζ v) ∧
      DiscreteTopology (KPLocalCover.projection F ζ hζ v).ker ∧
      ∀ g : KPLocalCover.LocalGL2 F v,
        Nat.card {x : LocalGL2Cover F ζ hζ v |
          KPLocalCover.projection F ζ hζ v x = g} = 3 := by
  cases v with
  | inl w => exact KPLocalChartTopology.complex_topological_cover F ζ hζ w
  | inr q =>
    let m := KPAdelicCoverRestrictedProduct.depth F ζ hζ q
    have hm := KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q
    have ht := KPLocalChartTopology.finite_topological_group F ζ hζ q m hm
    have hp := KPLocalChartTopology.finite_projection F ζ hζ q m hm
    exact ⟨ht.1, ht.2.1, ht.2.2, hp.1,
      (KPLocalChartTopology.finite_discrete_kernel F ζ hζ q m hm).1, hp.2⟩

abbrev AdelicGL2Cover := KPAdelicCoverRestrictedProduct.CubicGL2Adelic F ζ hζ

abbrev AdelicPGL2Cover := KPAdelicCoverRestrictedProduct.CubicPGL2Adelic F ζ hζ

theorem adelic_topological_covers :
    (T2Space (AdelicGL2Cover F ζ hζ) ∧ LocallyCompactSpace (AdelicGL2Cover F ζ hζ) ∧
      IsTopologicalGroup (AdelicGL2Cover F ζ hζ) ∧
      IsLocalHomeomorph (KPAdelicCoverRestrictedProduct.projection F ζ hζ)) ∧
    (T2Space (AdelicPGL2Cover F ζ hζ) ∧ LocallyCompactSpace (AdelicPGL2Cover F ζ hζ) ∧
      IsTopologicalGroup (AdelicPGL2Cover F ζ hζ) ∧
      IsLocalHomeomorph (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ)) := by
  exact ⟨KPAdelicCoverRestrictedProduct.adelic_topological_cover F ζ hζ,
    KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ⟩

abbrev adelicW := KPRationalAdelicSplitting.W F ζ hζ

end
end DedekindZetaZeroFree.KPCubicCoverConstruction

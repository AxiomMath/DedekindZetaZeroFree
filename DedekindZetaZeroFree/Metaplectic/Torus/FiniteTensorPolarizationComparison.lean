module

public import DedekindZetaZeroFree.Metaplectic.Torus.PeriodizationAndAveraging
public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData

@[expose] public section

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree
namespace KPGlobalResidualConstruction
namespace TorusCoreComparison

open KPGlobalTorusFiniteStages

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem finiteTensorCore_lift_exists
    (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
    (C : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P) :
    ∃ φ : RestrictedTensorSimple.Core (KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C)
        (KPGlobalTorusFiniteStages.localReference F ζ hζ P C) C.exceptional →ₗ[ℂ]
        KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ
          (KPGlobalTorusFiniteStages.productModel F ζ hζ P),
      Function.Injective φ ∧ φ.range = ⊤ ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
        (x : RestrictedTensorSimple.Stage
          (KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C) S),
        φ (RestrictedTensorSimple.stageInclusion
          (KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C)
          (KPGlobalTorusFiniteStages.localReference F ζ hζ P C) C.exceptional
          ⟨S, hS⟩ x) =
        KPGlobalTorusFiniteStages.finiteTensorRealization F ζ hζ P C S hS x := by
  let g : ∀ s : RestrictedTensorSimple.Level C.exceptional,
      RestrictedTensorSimple.Stage (KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C) s.1 →ₗ[ℂ]
        KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ
          (KPGlobalTorusFiniteStages.productModel F ζ hζ P) :=
    fun s => KPGlobalTorusFiniteStages.finiteTensorRealization F ζ hζ P C s.1 s.2
  have Hg : ∀ i j (hij : i ≤ j) x,
      g j (RestrictedTensorSimple.transition (KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C)
        (KPGlobalTorusFiniteStages.localReference F ζ hζ P C) C.exceptional i j hij x) = g i x :=
    fun i j hij x => congrFun (congrArg DFunLike.coe
      (KPGlobalTorusFiniteStages.tensor_insertion_compatible F ζ hζ P C i.1 j.1 i.2 hij)) x
  refine ⟨Module.DirectLimit.lift ℂ (RestrictedTensorSimple.Level C.exceptional)
    (fun s : RestrictedTensorSimple.Level C.exceptional =>
      RestrictedTensorSimple.Stage (KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C) s.1)
    (RestrictedTensorSimple.transition (KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C)
      (KPGlobalTorusFiniteStages.localReference F ζ hζ P C) C.exceptional) g Hg, ?_, ?_, ?_⟩
  · exact Module.DirectLimit.lift_injective (g := g) (Hg := Hg) (fun s =>
      KPGlobalTorusFiniteStages.finiteTensorRealization_injective F ζ hζ P C s.1 s.2)
  · rw [LinearMap.range_eq_top]
    intro f
    obtain ⟨S, hS, x, hx⟩ :=
      KPGlobalTorusFiniteStages.product_core_finite_modifications F ζ hζ P C f
    refine ⟨RestrictedTensorSimple.stageInclusion _ _ _ ⟨S, hS⟩ x, ?_⟩
    simp only [RestrictedTensorSimple.stageInclusion]
    rw [Module.DirectLimit.lift_of]
    exact hx
  · intro S hS x
    simp only [RestrictedTensorSimple.stageInclusion]
    rw [Module.DirectLimit.lift_of]

attribute [local instance] KPGlobalTorusPeriodizationInverse.modelTopology

end TorusCoreComparison
end KPGlobalResidualConstruction
end DedekindZetaZeroFree

end

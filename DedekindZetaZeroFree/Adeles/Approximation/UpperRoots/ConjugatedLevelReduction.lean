module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CuspCoordinatesAndTruncation

@[expose] public section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm.FiberStability

variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem finite_root_reduction
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (σ c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (n : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F →
      KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (hn : Continuous n) (hn0 : n 0 = 1)
    (z : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) :
    ∃ b : F, c⁻¹ * σ *
      n (z - algebraMap F
        (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) b) *
      σ⁻¹ * c ∈ U.toOpenSubgroup := by
  let f := fun w => c⁻¹ * σ * n (z - w) * σ⁻¹ * c
  have hf : Continuous f := by
    fun_prop
  have hfz : f z = 1 := by
    dsimp [f]
    rw [sub_self, hn0]
    group
  have hopen : IsOpen (f ⁻¹' (U.toOpenSubgroup : Set _)) :=
    U.toOpenSubgroup.isOpen.preimage hf
  have hz : z ∈ f ⁻¹' (U.toOpenSubgroup : Set _) := by
    change f z ∈ U.toOpenSubgroup
    rw [hfz]
    exact U.toOpenSubgroup.one_mem
  obtain ⟨b, hb⟩ := (finiteAdele_dense F).exists_mem_open hopen ⟨z, hz⟩
  exact ⟨b, hb⟩

end DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm.FiberStability

end

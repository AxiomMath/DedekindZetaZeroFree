module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteTensorRealizations

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
local notation "KPFinitePlace" F => HeightOneSpectrum (𝓞 F)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.EisensteinReferenceSections.TorusReference
open KPGlobalTorusFiniteStages
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

theorem localReference_one (q : KPFinitePlace F) :
    (localReference F ζ hζ P C q).val 1 = 1 := by
  simp only [localReference, map_one]
  simp only [Subgroup.one_mem, dite_true]
  change (((C.polarization q).ωL 1 : ℂˣ) : ℂ) = 1
  rw [map_one, Units.val_one]

theorem localUntwistedEvaluation_reference_one (q : KPFinitePlace F) :
    localUntwistedEvaluation F ζ hζ P C q (localReference F ζ hζ P C q) 1 = 1 := by
  unfold localUntwistedEvaluation
  rw [localReference_one, map_one]
  simp [KPGlobalCenterRationalCharacter.localAbs]

def finiteReference (T : Finset (KPFinitePlace F)) (hT : C.exceptional ⊆ T) :
    KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ (productModel F ζ hζ P) :=
  finiteTensorRealization F ζ hζ P C T hT
    (PiTensorProduct.tprod ℂ (fun q : T => localReference F ζ hζ P C q.val))

theorem finiteReference_one (T : Finset (KPFinitePlace F)) (hT : C.exceptional ⊆ T) :
    (finiteReference F ζ hζ P C T hT).val.val 1 = 1 := by
  have he := finiteTensorRealization_formula F ζ hζ P C T hT
    (fun q : T => localReference F ζ hζ P C q.val)
    1 (fun _ => 1) 1 (by intro w; rfl) (by intro q; simp) (by simp)
  change (finiteReference F ζ hζ P C T hT).val.val 1 = _ at he
  rw [he]
  have hvalues : (fun q : KPFinitePlace F => localUntwistedEvaluation F ζ hζ P C q
      (if h : q ∈ T then localReference F ζ hζ P C q else localReference F ζ hζ P C q) 1) =
      fun _ => (1 : ℂ) := by
    funext q
    simp only [dite_eq_ite, ite_self]
    exact localUntwistedEvaluation_reference_one F ζ hζ P C q
  rw [hvalues]
  exact finprod_one

end DedekindZetaZeroFree.EisensteinReferenceSections.TorusReference

end

section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
local notation "KPFinitePlace" F => HeightOneSpectrum (𝓞 F)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.EisensteinReferenceSections.TorusReference
open KPGlobalTorusFiniteStages
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

theorem localReference_ne_zero (q : KPFinitePlace F) :
    localReference F ζ hζ P C q ≠ 0 := by
  intro h
  have he := congrArg (fun v : LocalFiber F ζ hζ P C q => v.val 1) h
  rw [localReference_one] at he
  exact one_ne_zero he

end DedekindZetaZeroFree.EisensteinReferenceSections.TorusReference

end
end

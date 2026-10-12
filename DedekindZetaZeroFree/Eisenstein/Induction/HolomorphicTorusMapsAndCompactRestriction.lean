module

public import DedekindZetaZeroFree.Eisenstein.Induction.UniformConjugateTorusFiberLevels

@[expose] public section

section

open scoped NumberField Classical NNReal BigOperators Pointwise
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance smoothTopology4 (P : Polarization F ζ hζ) :
    TopologicalSpace (Smooth F ζ hζ P) :=
  KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ P

local instance inducedTop4 (P : Polarization F ζ hζ) : TopologicalSpace (Induced F ζ hζ P) :=
  inducedTopology F ζ hζ P

private theorem induced_smooth (P : Polarization F ζ hζ)
    (f : Induced F ζ hζ P) (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (f.val.val (groupArchChart F ζ hζ z * g)).val.val 1)
      (groupArchDomain F) := by
  have hf := f.property
  change f.val ∈ ⨆ J, InducedLevel F ζ hζ P J at hf
  exact Submodule.iSup_induction (motive := fun x : InducedFunctions F ζ hζ P =>
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (x.val (groupArchChart F ζ hζ z * g)).val.val 1)
      (groupArchDomain F)) (fun J => InducedLevel F ζ hζ P J) hf
      (fun J x hx => hx.1 g) contDiffOn_const (fun x y hx hy => hx.add hy)

 theorem induced_mem_level (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (f : Induced F ζ hζ P)
    (hf : ∀ (g : G F ζ hζ) (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
      f.val.val (g * j.val) = f.val.val g) :
    f.val ∈ InducedLevel F ζ hζ P J :=
  ⟨induced_smooth F ζ hζ P f, hf⟩

 def inducedLevelMap (P Q : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (m : Induced F ζ hζ P →ₗ[ℂ] Induced F ζ hζ Q)
    (hm : ∀ f : InducedLevel F ζ hζ P J, ∀ (g : G F ζ hζ)
      (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
      (m (inducedStageInclusion F ζ hζ P J f)).val.val (g * j.val) =
      (m (inducedStageInclusion F ζ hζ P J f)).val.val g) :
    InducedLevel F ζ hζ P J →ₗ[ℂ] InducedLevel F ζ hζ Q J :=
  ((Induced F ζ hζ Q).subtype.comp (m.comp (inducedStageInclusion F ζ hζ P J))).codRestrict
    (InducedLevel F ζ hζ Q J) (fun f =>
      induced_mem_level F ζ hζ Q J (m (inducedStageInclusion F ζ hζ P J f)) (hm f))

local instance inducedFunctionsAddGroup4 (P : Polarization F ζ hζ) :
    AddCommGroup (InducedFunctions F ζ hζ P) := @Submodule.addCommGroup ℂ (G F ζ hζ → Smooth F ζ hζ P)
      inferInstance inferInstance inferInstance (InducedFunctions F ζ hζ P)

local instance inducedLevelAddGroup4 (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    AddCommGroup (InducedLevel F ζ hζ P J) := @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
      inferInstance inferInstance inferInstance (InducedLevel F ζ hζ P J)

local instance inducedAddGroup4 (P : Polarization F ζ hζ) :
    AddCommGroup (Induced F ζ hζ P) := @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
      inferInstance inferInstance inferInstance (Induced F ζ hζ P)

def levelRestriction (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    InducedLevel F ζ hζ P J →ₗ[ℂ] (K → Smooth F ζ hζ P) where
  toFun f k := f.val.val k.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def CompactLevel (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    Submodule ℂ (K → Smooth F ζ hζ P) := (levelRestriction F ζ hζ P J K).range

def restrictLevel (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    InducedLevel F ζ hζ P J →ₗ[ℂ] CompactLevel F ζ hζ P J K :=
  (levelRestriction F ζ hζ P J K).rangeRestrict

def compactLevelTopology (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (K : Subgroup (G F ζ hζ)) :
    TopologicalSpace (CompactLevel F ζ hζ P J K) :=
  TopologicalSpace.coinduced (restrictLevel F ζ hζ P J K) (inducedLevelTopology F ζ hζ P J)

end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport

end

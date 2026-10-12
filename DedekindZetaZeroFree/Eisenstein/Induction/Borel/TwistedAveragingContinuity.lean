module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.InducedJetsAndFinalTopology

@[expose] public section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance smoothTopology (P : Polarization F ζ hζ) :
    TopologicalSpace (Smooth F ζ hζ P) :=
  KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ P

local instance inducedFunctionsAddGroup (P : Polarization F ζ hζ) :
    AddCommGroup (InducedFunctions F ζ hζ P) :=
  @Submodule.addCommGroup ℂ (G F ζ hζ → Smooth F ζ hζ P)
    inferInstance inferInstance inferInstance (InducedFunctions F ζ hζ P)

local instance inducedLevelAddGroup (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    AddCommGroup (InducedLevel F ζ hζ P J) :=
  @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
    inferInstance inferInstance inferInstance (InducedLevel F ζ hζ P J)

local instance inducedAddGroup (P : Polarization F ζ hζ) :
    AddCommGroup (Induced F ζ hζ P) :=
  @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
    inferInstance inferInstance inferInstance (Induced F ζ hζ P)

local instance inducedTop (P : Polarization F ζ hζ) :
    TopologicalSpace (Induced F ζ hζ P) := inducedTopology F ζ hζ P

def functionsMap (P Q : Polarization F ζ hζ)
    (T : Smooth F ζ hζ P →ₗ[ℂ] Smooth F ζ hζ Q)
    (hT : ∀ (a : E F ζ hζ) (v : Smooth F ζ hζ P),
      T (KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P a v) =
        KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ Q a (T v)) :
    InducedFunctions F ζ hζ P →ₗ[ℂ] InducedFunctions F ζ hζ Q where
  toFun f := ⟨fun g => T (f.val g), by
    intro t x g
    change T (f.val ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g)) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ t •
        KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ Q t (T (f.val g))
    rw [f.property t x g, map_smul, hT]⟩
  map_add' := by
    intro f k
    apply Subtype.ext
    funext g
    exact T.map_add _ _
  map_smul' := by
    intro c f
    apply Subtype.ext
    funext g
    exact T.map_smul c _

def functionsP (C : ModelData F ζ hζ) (s : ℂ) :
    InducedFunctions F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) →ₗ[ℂ]
      InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) :=
  functionsMap F ζ hζ _ _ (twistedP F ζ hζ C s).toLinearMap
    (twistedP_intertwines F ζ hζ C s)

def functionsQ (C : ModelData F ζ hζ) (s : ℂ) :
    InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) →ₗ[ℂ]
      InducedFunctions F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) :=
  functionsMap F ζ hζ _ _ (twistedQ F ζ hζ C s).toLinearMap
    (twistedQ_intertwines F ζ hζ C s)

def levelMap (P Q : Polarization F ζ hζ)
    (L : InducedFunctions F ζ hζ P →ₗ[ℂ] InducedFunctions F ζ hζ Q)
    (hL : ∀ J f, f ∈ InducedLevel F ζ hζ P J →
      L f ∈ InducedLevel F ζ hζ Q J)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    InducedLevel F ζ hζ P J →ₗ[ℂ] InducedLevel F ζ hζ Q J :=
  L.restrict (hL J)

def unionMap (P Q : Polarization F ζ hζ)
    (L : InducedFunctions F ζ hζ P →ₗ[ℂ] InducedFunctions F ζ hζ Q)
    (hL : ∀ J f, f ∈ InducedLevel F ζ hζ P J →
      L f ∈ InducedLevel F ζ hζ Q J) :
    Induced F ζ hζ P →ₗ[ℂ] Induced F ζ hζ Q := by
  refine L.restrict ?_
  have hle : Induced F ζ hζ P ≤ (Induced F ζ hζ Q).comap L := by
    apply iSup_le
    intro J f hf
    exact Submodule.mem_iSup_of_mem J (hL J f hf)
  exact fun f hf => hle hf

theorem unionMap_continuous (P Q : Polarization F ζ hζ)
    (L : InducedFunctions F ζ hζ P →ₗ[ℂ] InducedFunctions F ζ hζ Q)
    (hL : ∀ J f, f ∈ InducedLevel F ζ hζ P J →
      L f ∈ InducedLevel F ζ hζ Q J)
    (hcont : ∀ J,
      @Continuous (InducedLevel F ζ hζ P J) (InducedLevel F ζ hζ Q J)
        (inducedLevelTopology F ζ hζ P J) (inducedLevelTopology F ζ hζ Q J)
        (levelMap F ζ hζ P Q L hL J)) :
    @Continuous (Induced F ζ hζ P) (Induced F ζ hζ Q)
      (inducedTopology F ζ hζ P) (inducedTopology F ζ hζ Q)
      (unionMap F ζ hζ P Q L hL) := by
  have hp : WithSeminorms (fun q : inducedFinalSeminorms F ζ hζ P => q.val) := ⟨rfl⟩
  have hq : WithSeminorms (fun q : inducedFinalSeminorms F ζ hζ Q => q.val) := ⟨rfl⟩
  letI := hp.isTopologicalAddGroup
  apply WithSeminorms.continuous_of_continuous_comp hq
    (unionMap F ζ hζ P Q L hL)
  intro q
  apply hp.continuous_seminorm
    ⟨q.val.comp (unionMap F ζ hζ P Q L hL), ?_⟩
  intro J
  letI := inducedLevelTopology F ζ hζ P J
  letI := inducedLevelTopology F ζ hζ Q J
  have he : (q.val.comp (unionMap F ζ hζ P Q L hL)) ∘
      inducedStageInclusion F ζ hζ P J =
      (q.val ∘ inducedStageInclusion F ζ hζ Q J) ∘
        levelMap F ζ hζ P Q L hL J := by
    funext f
    rfl
  rw [he]
  exact (q.property J).comp (hcont J)

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction

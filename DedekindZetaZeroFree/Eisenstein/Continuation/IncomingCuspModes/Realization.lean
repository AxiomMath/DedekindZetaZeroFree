module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspGeometry.BufferedCollars
public import DedekindZetaZeroFree.Eisenstein.Induction.Cubic.SphericalFlatFamilies

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators ContDiff
open Topology

namespace DedekindZetaZeroFree.KPContActualCutoffSmoothDescent

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

abbrev level := KPContFlatCuspIncomingEvaluation.atlasLevel F ζ hζ C R P H U
abbrev Base := KPContActualCollarBuffer.Base F ζ hζ (level F ζ hζ C R P H U)
abbrev Covered := KPContActualCollarBuffer.Covered F ζ hζ (level F ζ hζ C R P H U)
abbrev Cusps := KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)

def ends (a : Cusps F ζ hζ C R P H U) : Set (Covered F ζ hζ C R P H U) :=
  KPContSectorCoveredQuotientVocabulary.q F ζ hζ (level F ζ hζ C R P H U) ⁻¹'
    KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H B.τ a

def height (a : Cusps F ζ hζ C R P H U) (x : Covered F ζ hζ C R P H U) : ℝ :=
  KPContActualCollarBuffer.height F ζ hζ (level F ζ hζ C R P H U) R P H B.τ a
    (KPContSectorCoveredQuotientVocabulary.q F ζ hζ (level F ζ hζ C R P H U) x)

def coveredPoint (a : Cusps F ζ hζ C R P H U) (ε : rootsOfUnity 3 F)
    (z : KPCuspCharts.Coordinates F) : Covered F ζ hζ C R P H U :=
  Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
    (level F ζ hζ C R P H U))
    (KPContSectorSmoothFramesSupport.cuspPoint F ζ hζ (level F ζ hζ C R P H U)
      R P H a.1 a.2 z,
      KPCuspGenuineMonodromy.central F ζ hζ ε *
        (KPContFlatCuspIncomingEvaluation.atlas F ζ hζ C R P H U).representative a.1)

def incomingValue (a : Cusps F ζ hζ C R P H U) (s : ℂ) (v : S)
    (z : KPCuspCharts.Coordinates F) : ℂ :=
  (KPContFlatCuspIncomingEvaluation.W F ζ hζ C R P H U a ι s v z.2 z.1.2).val
    (QuotientAddGroup.mk z.1.1)

structure EndLift (x : Covered F ζ hζ C R P H U) where
  cusp : Cusps F ζ hζ C R P H U
  sheet : rootsOfUnity 3 F
  coordinates : KPCuspCharts.Coordinates F
  high : B.τ < coordinates.2
  point : coveredPoint F ζ hζ C R P H U cusp sheet coordinates = x

 def identitySheet_add (a : Cusps F ζ hζ C R P H U) (s : ℂ) (v w : S) (t : ℝ)
    (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    KPContFlatCuspIncomingEvaluation.identitySheet F ζ hζ C R P H U a ι s (v+w) t x b ε =
      KPContFlatCuspIncomingEvaluation.identitySheet F ζ hζ C R P H U a ι s v t x b ε +
      KPContFlatCuspIncomingEvaluation.identitySheet F ζ hζ C R P H U a ι s w t x b ε := by
  rw [KPContFlatCuspIncomingEvaluation.identitySheet_reindexed,
      KPContFlatCuspIncomingEvaluation.identitySheet_reindexed,
      KPContFlatCuspIncomingEvaluation.identitySheet_reindexed]
  exact congr_fun (map_add (KPContFlatCommonLevelKernel.L F ζ hζ U ι s) v w)
    (KPContFlatCuspIncomingEvaluation.localGroup F ζ hζ C R P H U a t x b ε)

 def identitySheet_smul (a : Cusps F ζ hζ C R P H U) (s : ℂ) (c : ℂ) (v : S) (t : ℝ)
    (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    KPContFlatCuspIncomingEvaluation.identitySheet F ζ hζ C R P H U a ι s (c • v) t x b ε =
      c * KPContFlatCuspIncomingEvaluation.identitySheet F ζ hζ C R P H U a ι s v t x b ε := by
  rw [KPContFlatCuspIncomingEvaluation.identitySheet_reindexed,
      KPContFlatCuspIncomingEvaluation.identitySheet_reindexed]
  exact congr_fun (map_smul (KPContFlatCommonLevelKernel.L F ζ hζ U ι s) c v)
    (KPContFlatCuspIncomingEvaluation.localGroup F ζ hζ C R P H U a t x b ε)

 def incomingValue_add (a : Cusps F ζ hζ C R P H U) (s : ℂ) (v w : S)
    (z : KPCuspCharts.Coordinates F) :
    incomingValue F ζ hζ C R P H U ι a s (v + w) z =
      incomingValue F ζ hζ C R P H U ι a s v z + incomingValue F ζ hζ C R P H U ι a s w z := by
  simp only [incomingValue, KPContFlatCuspIncomingEvaluation.W]
  have hfun : (fun ε => KPContFlatCuspIncomingEvaluation.identitySheet F ζ hζ C R P H U a ι s (v+w) z.2 0 z.1.2 ε) =
      (fun ε => KPContFlatCuspIncomingEvaluation.identitySheet F ζ hζ C R P H U a ι s v z.2 0 z.1.2 ε) +
      (fun ε => KPContFlatCuspIncomingEvaluation.identitySheet F ζ hζ C R P H U a ι s w z.2 0 z.1.2 ε) := by
    funext ε; exact identitySheet_add F ζ hζ C R P H U ι a s v w z.2 0 z.1.2 ε
  rw [hfun, map_add]
  rfl

 def incomingValue_smul (a : Cusps F ζ hζ C R P H U) (s : ℂ) (c : ℂ) (v : S)
    (z : KPCuspCharts.Coordinates F) :
    incomingValue F ζ hζ C R P H U ι a s (c • v) z =
      c * incomingValue F ζ hζ C R P H U ι a s v z := by
  simp only [incomingValue, KPContFlatCuspIncomingEvaluation.W]
  have hfun : (fun ε => KPContFlatCuspIncomingEvaluation.identitySheet F ζ hζ C R P H U a ι s (c • v) z.2 0 z.1.2 ε) =
      c • (fun ε => KPContFlatCuspIncomingEvaluation.identitySheet F ζ hζ C R P H U a ι s v z.2 0 z.1.2 ε) := by
    funext ε; rw [identitySheet_smul F ζ hζ C R P H U ι a s c v z.2 0 z.1.2 ε]; rfl
  rw [hfun, map_smul]
  rfl

def incomingRealization (s : ℂ) : S →ₗ[ℂ] (Covered F ζ hζ C R P H U → ℂ) where
  toFun v x := if h : Nonempty (EndLift F ζ hζ C R P H U B x) then
    let l := Classical.choice h
    (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ l.sheet : ℂ) *
      incomingValue F ζ hζ C R P H U ι l.cusp s v l.coordinates
    else 0
  map_add' := by
    intro v w
    funext x
    by_cases h : Nonempty (EndLift F ζ hζ C R P H U B x)
    · simp only [Pi.add_apply, dif_pos h]
      rw [incomingValue_add, mul_add]
    · simp only [Pi.add_apply, dif_neg h]
      simp
  map_smul' := by
    intro c v
    funext x
    by_cases h : Nonempty (EndLift F ζ hζ C R P H U B x)
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, dif_pos h]
      rw [incomingValue_smul]
      ring
    · simp only [Pi.smul_apply, dif_neg h]
      simp

end DedekindZetaZeroFree.KPContActualCutoffSmoothDescent

end

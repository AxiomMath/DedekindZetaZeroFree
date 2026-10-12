module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Resolvent.ClearedNegativeGraphGerms
public import DedekindZetaZeroFree.Eisenstein.Continuation.Spherical.HolomorphicSmoothSectionGluing

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCutoffPlusClearedGerm

open KPContLocalNorm KPContSectorCoveredQuotientVocabulary

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
local notation "Covered" => KPContActualAllCuspSource.Covered F ζ hζ C R P H U
local notation "Charts" => KPContActualSmoothLineGluing.ChartBall F ζ hζ level R P H
local notation "GroupCharts" => KPContActualSphericalRightFieldIdentification.GroupChart
  F ζ hζ level R P H
local notation "scalar" => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
local notation "coefficient" => KPContActualSmoothLineGluing.coefficient F ζ hζ level R P H

def chartPullback (A : Charts) : (Covered → ℂ) →ₗ[ℂ]
    (Space (KPCuspLogShape.dimension F * 3) → ℂ) where
  toFun f p := if hp : p ∈ KPContActualChartRestrictionDensity.chartDomain
      F ζ hζ level R P H A.component A.center A.chart then
    f (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ level R P H
      A.component A.center A.chart
      (Quotient.mk _ (A.phase, ⟨KPContActualChartRestrictionDensity.coordinates F p, hp⟩))).val
    else 0
  map_add' := by
    intro f g
    funext p
    split <;> rename_i h <;> simp [h]
  map_smul' := by
    intro c f
    funext p
    split <;> rename_i h <;> simp [h]

def groupScalar (Z : Smooth) : ActualCover F ζ hζ → ℂ :=
  scalar Z ∘ KPContSectorQuotientRelationsComparison.piTilde F ζ hζ level ∘
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ

def actualRightCombination
    (terms : List (ℂ × List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))))
    (u : ActualCover F ζ hζ → ℂ) (g : ActualCover F ζ hζ) : ℂ :=
  (terms.map (fun t => t.1 *
    KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ t.2 u g)).sum

structure SmoothTaylorData (O : Set ℂ) (Z : ℂ → Smooth) : Prop where
  holomorphic : ∀ A : Charts,
    KPCutoffSource.ChartSmoothHolomorphicOn A.ball
      (fun s => coefficient (Z s).val A) O
  right_holomorphic : ∀ D : GroupCharts,
    KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
      (fun s x => groupScalar F ζ hζ C R P H U (Z s) (D.groupLift x)) O
  disks : ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → Metric.closedBall c ρ ⊆ O →
    ∃ b : ℕ → Smooth,
      (∀ A : Charts, SmoothPowerSeriesOn A.ball c ρ
        (fun j => coefficient (b j).val A)
        (fun s => coefficient (Z s).val A)) ∧
      (∀ (D : GroupCharts)
        (K : Set (Space (KPContActualSphericalRightFieldIdentification.groupDimension F))),
        IsCompact K → K ⊆ D.T.carrier →
        ∀ terms : List (ℂ × List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))),
        ∀ r' : ℝ, 0 ≤ r' → r' < ρ → ∀ ε : ℝ, 0 < ε →
          ∃ n : ℕ, ∀ M ≥ n, ∀ s ∈ Metric.closedBall c r', ∀ x ∈ K,
            ‖(∑ j ∈ Finset.range M, (s - c) ^ j *
                actualRightCombination F ζ hζ terms
                  (groupScalar F ζ hζ C R P H U (b j)) (D.groupLift x)) -
              actualRightCombination F ζ hζ terms
                (groupScalar F ζ hζ C R P H U (Z s)) (D.groupLift x)‖ < ε)

end DedekindZetaZeroFree.KPContActualCutoffPlusClearedGerm

end

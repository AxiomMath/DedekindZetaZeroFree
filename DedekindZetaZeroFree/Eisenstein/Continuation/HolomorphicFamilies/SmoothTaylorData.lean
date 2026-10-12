module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothHolomorphy.TaylorData
public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothSections.RightDifferentialHolomorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree

namespace ClearedSmoothPromotionProof

open KPContActualSphericalRightFieldIdentification KPContSectorSmoothFramesSupport
open KPContSectorQuotientRelationsComparison KPContSectorLineL2Isometry
open KPContActualCommonDiskRightHolomorphy KPContSectorScalarLineAlgebra
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private lemma lifted_smooth (D : GroupChart F ζ hζ U R P H)
    (w : smoothSections F ζ hζ U R P H) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => lift F ζ hζ U R P H w.val (D.groupLift x)) D.T.carrier := by
  have he : S F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H w.val) = w.val :=
    (S F ζ hζ U R P H).apply_symm_apply w.val
  have hs := D.frame_smooth.mul
    ((w.property D.component).comp (baseCoordinates F).contDiff |>.contDiffOn |>.comp D.π_smooth
      (fun _ _ => Set.mem_univ _))
  apply hs.congr
  intro x hx
  simpa only [lift, he, KPContRightJets.scalarLift, Function.comp_apply] using D.global_scalar_pullback
    (scalarRepresentative F ζ hζ U R P H w.val) x hx

private lemma combination_smooth {m b : ℕ} (T : KPContLocalNorm.LocalBall m)
    (fields : Fin b → KPContLocalNorm.Space m → KPContLocalNorm.Space m)
    (hf : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fields i) T.carrier)
    (terms : List (ℂ × List (Fin b))) (f : KPContLocalNorm.Space m → ℂ)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) f T.carrier) :
    ContDiffOn ℝ (⊤ : ℕ∞) (KPContRightJets.rightCombination fields terms f) T.carrier := by
  have hw (w : List (Fin b)) : ContDiffOn ℝ (⊤ : ℕ∞) (KPContRightJets.rightWord fields w f) T.carrier := by
    induction w with
    | nil => exact hs
    | cons i w ih => exact (ih.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply (hf i)
  induction terms with
  | nil => exact contDiffOn_const
  | cons t ts ih => exact (contDiffOn_const.mul (hw t.2)).add ih

private lemma combination_identification (D : GroupChart F ζ hζ U R P H)
    (terms : Combination F) (w : smoothSections F ζ hζ U R P H)
    (x : KPContLocalNorm.Space (groupDimension F)) (hx : x ∈ D.T.carrier) :
    rightCombination F ζ hζ terms (lift F ζ hζ U R P H w.val) (D.groupLift x) =
    KPContRightJets.rightCombination D.fields terms
      (fun y => lift F ζ hζ U R P H w.val (D.groupLift y)) x := by
  unfold rightCombination KPContRightJets.rightCombination
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [D.identification.right_iteration _ (lifted_smooth D w) t.2 x hx]

private lemma right_holomorphic
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (O : Set ℂ) (hO : IsOpen O)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (W : ℂ → smoothSections F ζ hζ U R P H)
    (h : KPContActualSmoothLineGluing.HolomorphicData F ζ hζ U R P H O u W)
    (D : GroupChart F ζ hζ U R P H) :
    KPClearedResolvent.RightSmoothHolomorphicOn D.T D.fields
      (fun s x => lift F ζ hζ U R P H (W s).val (D.groupLift x)) O := by
  classical
  have hs := fun s => lifted_smooth D (W s)
  refine ⟨fun s _ => hs s, ?_⟩
  intro K hK hKT terms
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let j : ℂ → C(K, ℂ) := fun s =>
    ⟨fun x => KPContRightJets.rightCombination D.fields terms
      (fun y => lift F ζ hζ U R P H (W s).val (D.groupLift y)) x,
      ((combination_smooth D.T D.fields D.fields_smooth_actual terms _ (hs s)).continuousOn.mono hKT).restrict⟩
  refine ⟨j, ?_, fun _ _ _ => rfl⟩
  intro s₀ hs₀
  obtain ⟨ρ, hρ, hρO⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hs₀)
  obtain ⟨b, _, _, hb, _⟩ := h.disks s₀ ρ hρ hρO
  let C := D.groupLift '' K
  have hC : IsCompact C := hK.image_of_continuousOn (D.groupLift_continuous.mono hKT)
  have hp := kp_cont_actual_common_disk_right_holomorphy F ζ hζ U R P H
    realization O hO W b s₀ ρ hρ (Set.Subset.trans Metric.ball_subset_closedBall hρO) hb C hC terms
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  obtain ⟨f, a, hf, _, hfd, _, _⟩ := hp.2.2
  let e : C(K, C) := ⟨fun x => ⟨D.groupLift x, ⟨x, x.property, rfl⟩⟩,
    ((D.groupLift_continuous.mono hKT).restrict).subtype_mk _⟩

  let L := ContinuousMap.compCLM ℂ ℂ e
  have heq : Set.EqOn j (fun s => L (f s)) (Metric.ball s₀ ρ) := by
    intro s hsball
    apply ContinuousMap.ext
    intro x
    change KPContRightJets.rightCombination D.fields terms
      (fun y => lift F ζ hζ U R P H (W s).val (D.groupLift y)) x = f s (e x)
    rw [hf s hsball (e x)]
    exact (combination_identification D terms (W s) x (hKT x.property)).symm
  have hd : DifferentiableOn ℂ (fun s => L (f s)) (Metric.ball s₀ ρ) :=
    L.differentiable.comp_differentiableOn hfd
  exact (hd.congr heq).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hρ)) |>.differentiableWithinAt

end ClearedSmoothPromotionProof

theorem kp_cont_actual_cleared_smooth_promotion
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
    (O : Set ℂ) (hO : IsOpen O)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R
      (KPContActualAllCuspSource.level F ζ hζ C R P H U))
    (W : ℂ → KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U)
    (h : KPContActualSmoothLineGluing.HolomorphicData F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H O u W) :
    KPContActualCutoffPlusClearedGerm.SmoothTaylorData F ζ hζ C R P H U O W := by
  refine ⟨h.holomorphic, ?_, ?_⟩
  · intro D
    exact ClearedSmoothPromotionProof.right_holomorphic realization O hO u W h D
  · intro c ρ hρ hdisk

    obtain ⟨b, _, _, hb, _⟩ := h.disks c ρ hρ hdisk
    refine ⟨b, hb, ?_⟩
    intro D K hK hKT terms r' hr' hr'ρ ε hε
    have hC := hK.image_of_continuousOn (D.groupLift_continuous.mono hKT)
    have hp := kp_cont_actual_common_disk_right_holomorphy F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H
      realization O hO W b c ρ hρ
      (Set.Subset.trans Metric.ball_subset_closedBall hdisk) hb
      (D.groupLift '' K) hC terms
    obtain ⟨N, hN⟩ := hp.2.1 r' hr' hr'ρ ε hε
    exact ⟨N, fun M hM s hs x hx => hN M hM s hs (D.groupLift x) ⟨x, hx, rfl⟩⟩

end DedekindZetaZeroFree

end

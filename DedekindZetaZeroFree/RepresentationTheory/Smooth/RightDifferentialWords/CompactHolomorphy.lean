module

public import DedekindZetaZeroFree.Eisenstein.Continuation.PoleClearedSmoothResolvent
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.RaisingOperators.SphericalDerivativeReconstruction

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPContinuation.NativeWordCompactHolomorphy
open KPContLocalNorm KPContRightJets KPClearedResolvent
open Filter Set Topology
open scoped NumberField Classical
open _root_.DedekindZetaZeroFree.KPContRightJets renaming rightWord_smooth → rightWord_smooth

private theorem rightWord_append {m b : ℕ}
    (fields : Fin b → Space m → Space m) (v w : List (Fin b)) (f : Space m → ℂ) :
    rightWord fields v (rightWord fields w f) = rightWord fields (v ++ w) f := by
  induction v with
  | nil => rfl
  | cons i v ih => simp only [rightWord, List.cons_append, ih]

private theorem rightCombination_append {m b : ℕ}
    (fields : Fin b → Space m → Space m) (terms : List (ℂ × List (Fin b)))
    (w : List (Fin b)) (f : Space m → ℂ) :
    rightCombination fields terms (rightWord fields w f) =
      rightCombination fields (terms.map (fun t => (t.1, t.2 ++ w))) f := by
  funext x
  simp only [rightCombination, List.map_map, Function.comp_def, rightWord_append]

private theorem rightSmoothHolomorphicOn_word {m b : ℕ} (T : LocalBall m)
    (fields : Fin b → Space m → Space m)
    (hf : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fields i) T.carrier)
    (u : ℂ → Space m → ℂ) (O : Set ℂ)
    (hu : RightSmoothHolomorphicOn T fields u O) (w : List (Fin b)) :
    RightSmoothHolomorphicOn T fields (fun s => rightWord fields w (u s)) O := by
  refine ⟨fun s hs => rightWord_smooth T fields hf w (u s) (hu.1 s hs), ?_⟩
  intro K hK hKT terms
  obtain ⟨j, hj, he⟩ := hu.2 K hK hKT (terms.map (fun t => (t.1, t.2 ++ w)))
  refine ⟨j, hj, ?_⟩
  intro s hs x
  rw [rightCombination_append]
  exact he s hs x

private theorem rightWord_eqOn {m b : ℕ} (T : LocalBall m)
    (fields : Fin b → Space m → Space m) (w : List (Fin b))
    (f g : Space m → ℂ) (he : Set.EqOn f g T.carrier) :
    Set.EqOn (rightWord fields w f) (rightWord fields w g) T.carrier := by
  induction w with
  | nil => exact he
  | cons i w ih =>
    intro x hx
    have hfg : rightWord fields w f =ᶠ[𝓝 x] rightWord fields w g :=
      Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hx) (fun y hy => ih hy)
    exact congrArg (fun D : Space m →L[ℝ] ℂ => D (fields i x)) hfg.fderiv_eq

private theorem rightCombination_eqOn {m b : ℕ} (T : LocalBall m)
    (fields : Fin b → Space m → Space m) (terms : List (ℂ × List (Fin b)))
    (f g : Space m → ℂ) (he : Set.EqOn f g T.carrier) :
    Set.EqOn (rightCombination fields terms f) (rightCombination fields terms g) T.carrier := by
  intro x hx
  unfold rightCombination
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [rightWord_eqOn T fields t.2 f g he hx]

private theorem rightSmoothHolomorphicOn_congr {m b : ℕ} (T : LocalBall m)
    (fields : Fin b → Space m → Space m) (u v : ℂ → Space m → ℂ) (O : Set ℂ)
    (hu : RightSmoothHolomorphicOn T fields u O)
    (he : ∀ s ∈ O, Set.EqOn (u s) (v s) T.carrier) :
    RightSmoothHolomorphicOn T fields v O := by
  refine ⟨fun s hs => (hu.1 s hs).congr (he s hs).symm, ?_⟩
  intro K hK hKT terms
  obtain ⟨j, hj, hjv⟩ := hu.2 K hK hKT terms
  refine ⟨j, hj, ?_⟩
  intro s hs x
  exact (hjv s hs x).trans
    (rightCombination_eqOn T fields terms (u s) (v s) (he s hs) (hKT x.property))

open KPContActualSphericalRightFieldIdentification
open KPContSectorCoveredQuotientVocabulary

 theorem actualRightWord_append
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (v w : List (Fin (groupDimension F))) (f : ActualCover F ζ hζ → ℂ) :
    actualRightWord F ζ hζ v (actualRightWord F ζ hζ w f) =
      actualRightWord F ζ hζ (v ++ w) f := by
  induction v with
  | nil => rfl
  | cons i v ih => simp only [actualRightWord, List.cons_append, ih]

section ActualChart
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

 theorem actualRightWord_compact_holomorphy
    (D : GroupChart F ζ hζ U R P H) (u : ℂ → ActualCover F ζ hζ → ℂ)
    (O : Set ℂ) (hu : RightSmoothHolomorphicOn D.T D.fields
      (fun s x => u s (D.groupLift x)) O) (w : List (Fin (groupDimension F))) :
    RightSmoothHolomorphicOn D.T D.fields
      (fun s x => actualRightWord F ζ hζ w (u s) (D.groupLift x)) O := by
  have hw := rightSmoothHolomorphicOn_word D.T D.fields D.fields_smooth_actual
    (fun s x => u s (D.groupLift x)) O hu w
  apply rightSmoothHolomorphicOn_congr D.T D.fields _ _ O hw
  intro s hs x hx
  exact (D.identification.right_iteration (u s) (hu.1 s hs) w x hx).symm

end ActualChart
end DedekindZetaZeroFree.KPContinuation.NativeWordCompactHolomorphy

end

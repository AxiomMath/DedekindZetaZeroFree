module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.PositiveNativeCharts
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightChartJetsAndFlowWords

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeWordAction
open KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming word → word
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativePositiveChart renaming word_reindex → word_reindex
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem actual_eq_word (w : List (Fin (groupDimension F))) (u : G F ζ hζ → ℂ) :
    actualRightWord F ζ hζ w u =
      word F ζ hζ (w.map (fun b =>
        KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource.actualBasisReindex F (lieEnumeration F b))) u := by
  rw [word_reindex]
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [List.map_cons, List.foldr_cons, word] at *
    rw [← ih]
    rfl

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeWordAction

end

section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeWordAction

open scoped Topology ContDiff Matrix Matrix.Norms.Elementwise
open Filter KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification
open KPLiteralChamber
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming word → word
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming rightWord_level → rightWord_level
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming rightWord_continuous_of_chart_smooth → rightWord_continuous_of_chart_smooth
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming word_add → word_add
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming word_smul → word_smul
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming rightWord_hasDerivAt_of_chart_smooth → rightWord_hasDerivAt_of_chart_smooth
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativePositiveChart renaming word_reindex → word_reindex
open _root_.DedekindZetaZeroFree.RightFrame.PullbackWords renaming word_smooth → word_smooth
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming rightCoordinates_nonzero → rightCoordinates_nonzero
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeChartProduct renaming domain_open → domain_open
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem chart_base : archChart F ζ hζ (archBase F) = 1 := by
  rw [right_insertion]
  have hh : (fun v : NumberField.InfinitePlace F => Matrix.ProjGenLinGroup.mk
      (rightMatrix (archBase F v))) = 1 := by
    funext v
    have hm : rightMatrix (archBase F v) = 1 := by
      apply Units.ext
      rw [rightMatrix_val _ (by simp [archBase])]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [archBase]
    rw [hm, map_one]
    rfl
  rw [hh]
  exact (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1

private theorem recenter (O : Set (ArchCoordinates F)) (hO : IsOpen O)
    (hb : archBase F ∈ O) (x₀ : ArchCoordinates F) (hx₀ : x₀ ∈ archDomain F) :
    ∃ (V : Set (ArchCoordinates F)) (q : ArchCoordinates F → ArchCoordinates F),
      IsOpen V ∧ x₀ ∈ V ∧ ContDiffOn ℝ (⊤ : ℕ∞) q V ∧ Set.MapsTo q V O ∧
      ∀ x ∈ V, archChart F ζ hζ x = archChart F ζ hζ x₀ * archChart F ζ hζ (q x) := by
  let m := fun (x : ArchCoordinates F) (v : NumberField.InfinitePlace F) =>
    (rightMatrix (x₀ v))⁻¹ * rightMatrix (x v)
  let D := archDomain F
  let A := D ∩ {x | ∀ v, (m x v).val 1 1 ≠ 0}
  let q := fun x v => rightCoordinates (m x v).val
  have hm0 (v) : m x₀ v = 1 := by dsimp [m]; simp
  have hq0 : q x₀ = archBase F := by
    funext v i
    simp only [q, hm0]
    fin_cases i <;> simp [rightCoordinates, archBase]
  have hm (v) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (m x v).val) D := by
    let P := fun x : ArchCoordinates F => ((rightMatrix (x₀ v))⁻¹).val *
      (!![x v 1 + x v 0*x v 2, x v 0; x v 2, 1])
    have hp : ContDiff ℝ (⊤ : ℕ∞) P := by
      dsimp [P]
      apply contDiff_pi.mpr; intro i
      apply contDiff_pi.mpr; intro j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> fun_prop
    exact hp.contDiffOn.congr (by intro x hx; simp only [m, Units.val_mul, rightMatrix_val _ (hx v)]; rfl)
  have he (v) (i j : Fin 2) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (m x v).val i j) D :=
    (contDiffOn_pi.mp (contDiffOn_pi.mp (hm v) i)) j
  have hA : IsOpen A := by
    have ho : IsOpen (⋂ v, D ∩ {x | (m x v).val 1 1 ≠ 0}) := by
      apply isOpen_iInter_of_finite
      intro v
      exact (he v 1 1).continuousOn.isOpen_inter_preimage (domain_open F)
        (isOpen_ne_fun continuous_id continuous_const)
    convert ho using 1
    ext x
    simp only [A, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hx v; exact ⟨hx.1, hx.2 v⟩
    · intro hx; exact ⟨(hx (Classical.choice inferInstance)).1, fun v => (hx v).2⟩
  have hxA : x₀ ∈ A := ⟨hx₀, by intro v; simp [hm0]⟩
  have hq : ContDiffOn ℝ (⊤ : ℕ∞) q A := by
    apply contDiffOn_pi.mpr; intro v
    apply contDiffOn_pi.mpr; intro i
    have hn : ∀ x ∈ A, (m x v).val 1 1 ≠ 0 := fun x hx => hx.2 v
    have hentry (i j : Fin 2) := (he v i j).mono (show A ⊆ D from fun _ hx => hx.1)
    have hdet : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (m x v).val.det) A := by
      simp only [Matrix.det_fin_two]
      exact ((hentry 0 0).mul (hentry 1 1)).sub ((hentry 0 1).mul (hentry 1 0))
    fin_cases i <;> simp [q, rightCoordinates, div_eq_mul_inv]
    · exact (hentry 0 1).mul ((hentry 1 1).inv hn)
    · exact hdet.mul (((hentry 1 1).pow 2).inv (fun x hx => pow_ne_zero _ (hn x hx)))
    · exact (hentry 1 0).mul ((hentry 1 1).inv hn)
  let V := A ∩ q ⁻¹' O
  refine ⟨V, q, hq.continuousOn.isOpen_inter_preimage hA hO,
    ⟨hxA, by change q x₀ ∈ O; rw [hq0]; exact hb⟩, hq.mono Set.inter_subset_left, fun x hx => hx.2, ?_⟩
  intro x hx
  rw [right_insertion, right_insertion, right_insertion,
    ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  congr 1
  funext v
  change Matrix.ProjGenLinGroup.mk (rightMatrix (x v)) =
    Matrix.ProjGenLinGroup.mk (rightMatrix (x₀ v)) * Matrix.ProjGenLinGroup.mk (rightMatrix (q x v))
  rw [rightCoordinates_reconstruct (m x v) (hx.1.2 v), ← map_mul]
  dsimp [m]
  simp

 theorem native_word_smooth (u : G F ζ hζ → ℂ)
    (hu : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => u (g * archChart F ζ hζ x)) (archDomain F))
    (w : List (Fin (groupDimension F))) :
    ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => actualRightWord F ζ hζ w u (g * archChart F ζ hζ x)) (archDomain F) := by
  obtain ⟨O, fields, hO, hb, hOD, hf, hreal⟩ := NativePositiveChart.actual_rightWord_chart_realization F ζ hζ
  intro g
  apply contDiffOn_of_locally_contDiffOn
  intro x₀ hx₀
  obtain ⟨V, q, hV, hxV, hq, hqO, he⟩ := recenter F ζ hζ O hO hb x₀ hx₀
  have hs := word_smooth O hO fields hf w _ ((hu (g * archChart F ζ hζ x₀)).mono hOD)
  refine ⟨V, hV, hxV, ((hs.comp hq hqO).mono Set.inter_subset_right).congr ?_⟩
  intro x hx
  rw [he x hx.2, ← mul_assoc]
  exact hreal u hu w (g * archChart F ζ hζ x₀) (q x) (hqO hx.2)

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeWordAction

end
end

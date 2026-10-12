module

public import DedekindZetaZeroFree.Eisenstein.Sections.FlatRightWordJets

@[expose] public section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMovingCompact

open KPContinuation.ChamberFlatSource.ChartMatrix

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem continuous_chartMatrix :
    Continuous (fun x : {x : Fin 3 → ℂ // x 1 ≠ 0} => chartMatrix x.val) := by
  have hc (i : Fin 3) : Continuous (fun x : {x : Fin 3 → ℂ // x 1 ≠ 0} => x.val i) :=
    (continuous_apply i).comp continuous_subtype_val
  have hval : Continuous (fun x : {x : Fin 3 → ℂ // x 1 ≠ 0} => (chartMatrix x.val).val) := by
    apply continuous_pi; intro i; apply continuous_pi; intro j
    have he : (fun x : {x : Fin 3 → ℂ // x 1 ≠ 0} =>
        (chartMatrix x.val).val i j) =
        (fun x => (!![x.val 1 + x.val 0 * x.val 2, x.val 0; x.val 2, 1] :
          Matrix (Fin 2) (Fin 2) ℂ) i j) := by
      funext x
      rw [chartMatrix_val x.val x.property]
    change Continuous (fun x : {x : Fin 3 → ℂ // x 1 ≠ 0} => (chartMatrix x.val).val i j)
    rw [he]
    fin_cases i <;> fin_cases j <;> simp
    · exact (hc 1).add ((hc 0).mul (hc 2))
    · exact hc 0
    · exact hc 2
    · exact continuous_const
  apply Units.continuous_iff.mpr
  refine ⟨hval, ?_⟩
  change Continuous (fun x : {x : Fin 3 → ℂ // x 1 ≠ 0} => ((chartMatrix x.val)⁻¹).val)
  simp_rw [Matrix.GeneralLinearGroup.coe_inv]
  rw [continuous_iff_continuousAt]
  intro x
  apply (continuousAt_matrix_inv _ ?_).comp hval.continuousAt
  have he : (Ring.inverse : ℂ → ℂ) = Inv.inv := funext Ring.inverse_eq_inv
  rw [he]
  exact continuousAt_inv₀ (Matrix.GeneralLinearGroup.det_ne_zero (chartMatrix x.val))

theorem archChart_continuousOn
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    ContinuousOn (archChart F ζ hζ) (archDomain F) := by
  rw [continuousOn_iff_continuous_restrict]
  have hi := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1
  have he : (fun x : archDomain F => archChart F ζ hζ x.val) =
      (fun x => KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (chartMatrix (x.val w)))) := by
    funext x
    exact archChart_eq_insertion_chartMatrix F ζ hζ x.val
  change Continuous (fun x : archDomain F => archChart F ζ hζ x.val)
  rw [he]
  apply hi.comp
  apply continuous_pi
  intro w
  have hmk : Continuous (Matrix.ProjGenLinGroup.mk (n := Fin 2) (R := ℂ)) :=
    QuotientGroup.continuous_mk
  apply hmk.comp
  let ev : archDomain F → {x : Fin 3 → ℂ // x 1 ≠ 0} :=
    fun x => ⟨x.val w, x.property w⟩
  have hev : Continuous ev :=
    Continuous.subtype_mk ((continuous_apply w).comp
      (continuous_subtype_val : Continuous (fun x : archDomain F => x.val)))
      (fun x => x.property w)
  change Continuous (fun x : archDomain F => chartMatrix (ev x).val)
  exact continuous_chartMatrix.comp hev

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMovingCompact

end

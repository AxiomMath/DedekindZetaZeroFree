module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AutomorphicHilbertFlows
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.ComplexRootGeneration

@[expose] public section

noncomputable section
open scoped Classical MatrixGroups NumberField
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualArchSL2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem exists_sl2_representative (g : Matrix.ProjGenLinGroup (Fin 2) ℂ) :
    ∃ a : SL(2, ℂ), Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL a) = g := by
  induction g using Quotient.inductionOn with
  | h g =>
    let c : ℂ := Complex.exp (Complex.log (Matrix.det g.val) / 2)
    have hc : c ≠ 0 := Complex.exp_ne_zero _
    have hc2 : c ^ 2 = Matrix.det g.val := by
      dsimp [c]
      rw [pow_two, ← Complex.exp_add]
      convert Complex.exp_log (Matrix.GeneralLinearGroup.det_ne_zero g) using 1; ring
    let a : SL(2, ℂ) := ⟨c⁻¹ • g.val, by
      rw [Matrix.det_smul]
      simp only [Fintype.card_fin, ← hc2, inv_pow]
      exact inv_mul_cancel₀ (pow_ne_zero _ hc)⟩
    refine ⟨a, Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr ⟨Units.mk0 c hc, ?_⟩⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change ((c⁻¹ • g.val) * Matrix.scalar (Fin 2) c) i j = g.val i j
    simp [Matrix.mul_apply, Matrix.scalar, Matrix.diagonal, hc, mul_comm]

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem arch_invariant_of_sl2_invariant
    (θ : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (hθ : ∀ (w : InfinitePlace F) (a : SL(2, ℂ)) g,
      θ (KPLiteralPeriod.complexSL2 F ζ hζ w a * g) = θ g)
    (k : KPSmoothActualFlowData.GInfinity F) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    θ (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k * g) = θ g := by
  let a := fun w => (exists_sl2_representative (k w)).choose
  have hk : k = fun w => Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (a w)) := by
    funext w
    exact (exists_sl2_representative (k w)).choose_spec.symm
  rw [hk, (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.2]
  change θ (((Finset.univ : Finset (InfinitePlace F)).toList.map
    (fun w => KPLiteralPeriod.complexSL2 F ζ hζ w (a w))).prod * g) = θ g
  suffices H : ∀ (l : List (InfinitePlace F)) g,
      θ ((l.map (fun w => KPLiteralPeriod.complexSL2 F ζ hζ w (a w))).prod * g) = θ g by
    exact H _ g
  intro l
  induction l with
  | nil => intro g; simp
  | cons w l ih =>
    intro g
    simp only [List.map_cons, List.prod_cons, mul_assoc]
    rw [hθ, ih]

end DedekindZetaZeroFree.FourierContinuation.ResidualArchSL2

end

module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.CompactFaithfulness

@[expose] public section

noncomputable section
open scoped Classical Topology
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxJacquetFunctional
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem jacquetEvaluation_eq_of_compacts
    (f h : PrincipalSeries positiveParameter)
    (he : ∀ k : ComplexSU2, KPCplxJacquetFunctional.jacquetEvaluation f (complexSU2Embedding k) =
      KPCplxJacquetFunctional.jacquetEvaluation h (complexSU2Embedding k)) :
    KPCplxJacquetFunctional.jacquetEvaluation f = KPCplxJacquetFunctional.jacquetEvaluation h := by
  have hz : f - h = 0 := by
    apply jacquet_compacts_separate
    intro k
    change KPCplxJacquetFunctional.jacquetEvaluation (f-h) (complexSU2Embedding k) = 0
    rw [map_sub, Pi.sub_apply, sub_eq_zero]
    exact he k
  exact congrArg KPCplxJacquetFunctional.jacquetEvaluation (sub_eq_zero.mp hz)

theorem product_eq_of_compact_slices {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : (I → ComplexGL2) → ℂ)
    (hP : ∀ w g₀, (fun g => P (Function.update g₀ w g)) ∈ KPCplxJacquetFunctional.jacquetEvaluation.range)
    (hQ : ∀ w g₀, (fun g => Q (Function.update g₀ w g)) ∈ KPCplxJacquetFunctional.jacquetEvaluation.range)
    (he : ∀ k : I → ComplexSU2, P (fun w => complexSU2Embedding (k w)) =
      Q (fun w => complexSU2Embedding (k w))) : P = Q := by
  have hs : ∀ s : Finset I, ∀ (g : I → ComplexGL2) (k : I → ComplexSU2),
      P (fun w => if w ∈ s then g w else complexSU2Embedding (k w)) =
      Q (fun w => if w ∈ s then g w else complexSU2Embedding (k w)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g k
      simpa only [Finset.notMem_empty, ite_false] using he k
    | @insert w s hw ih =>
      intro g k
      let a := fun u => if u ∈ s then g u else complexSU2Embedding (k u)
      obtain ⟨f,hf⟩ := hP w a
      obtain ⟨h,hh⟩ := hQ w a
      have heval : KPCplxJacquetFunctional.jacquetEvaluation f = KPCplxJacquetFunctional.jacquetEvaluation h := by
        apply jacquetEvaluation_eq_of_compacts
        intro b
        rw [hf,hh]
        have ha : Function.update a w (complexSU2Embedding b) =
            (fun u => if u ∈ s then g u else complexSU2Embedding (Function.update k w b u)) := by
          funext u
          by_cases hu : u = w
          · subst u; simp [a,hw]
          · simp [Function.update_of_ne hu,a]
        dsimp only
        rw [ha]
        exact ih g (Function.update k w b)
      have ha : Function.update a w (g w) =
          (fun u => if u ∈ insert w s then g u else complexSU2Embedding (k u)) := by
        funext u
        by_cases hu : u = w
        · subst u; simp
        · simp [Function.update_of_ne hu,Finset.mem_insert,hu,a]
      have hx := congrFun heval (g w)
      rw [hf,hh] at hx
      dsimp only at hx
      rw [ha] at hx
      exact hx
  funext g
  simpa only [Finset.mem_univ, ite_true] using hs Finset.univ g (fun _ => 1)

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end

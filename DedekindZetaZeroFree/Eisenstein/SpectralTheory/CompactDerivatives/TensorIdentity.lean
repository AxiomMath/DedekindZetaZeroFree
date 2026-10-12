module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Conormal.CompactCartanCancellation
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AutomorphicWordRegularity
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.CompactAugmentedCoercivity

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology BigOperators
namespace DedekindZetaZeroFree.FourierContinuation.ResidualCompactTensor
open KPMsClearedTruncationL2
open KPSmoothActualFlowData (LieCoordinates exponential flow flow_properties archimedean_insertion_properties)

open KPMsGreenFlux (rightDerivative compactInsertion)
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes renaming compactCoefficients → compactCoefficients
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes renaming compactDirection → compactDirection
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes renaming compactDirectionCurve → compactDirectionCurve
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes renaming directionJet → directionJet
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes renaming direction_hasDerivAt → direction_hasDerivAt
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes renaming compact_direction_curve_insertion → compact_direction_curve_insertion
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalWordRegularity renaming word_mem_smoothSpace → word_mem_smoothSpace
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.FullSixCoercivity renaming compactTensor → compactTensor
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : Level F ζ hζ}

 theorem compact_directionJet (v : G F ζ hζ → ℂ)
    (w : NumberField.InfinitePlace F) (c : Fin 3) (g : G F ζ hζ) :
    directionJet (compactDirection w c) v g =
      ![rightDerivative F ζ hζ w 1 v g,
        rightDerivative F ζ hζ w 2 v g - rightDerivative F ζ hζ w 4 v g,
        rightDerivative F ζ hζ w 3 v g + rightDerivative F ζ hζ w 5 v g] c := by
  unfold directionJet compactDirection
  simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  fin_cases c <;> simp [compactCoefficients, Fin.sum_univ_succ, sub_eq_add_neg]

 theorem compact_curve_zero (w : NumberField.InfinitePlace F) (c : Fin 3)
    (g : G F ζ hζ) :
    g * compactInsertion F ζ hζ (compactDirectionCurve w c 0) = g := by
  rw [compact_direction_curve_insertion]
  have hz : exponential F (0 : LieCoordinates F) = 1 := by
    convert (flow_properties F (w,0)).1 using 1
    unfold flow
    congr 1
    funext b
    simp
  simp only [zero_smul, hz, (archimedean_insertion_properties F ζ hζ).1, mul_one]

private theorem word_compact_hasDerivAt
    (u : smoothSpace F ζ hζ U) (word : List (KPSmoothActualFlowData.B F))
    (w : NumberField.InfinitePlace F) (c : Fin 3) (g : G F ζ hζ) (t : ℝ) :
    let v := word.foldr (fun b f => rightDerivative F ζ hζ b.1 b.2 f)
      (fun a => u.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a))
    HasDerivAt (fun s : ℝ => v (g * compactInsertion F ζ hζ (compactDirectionCurve w c s)))
      (![rightDerivative F ζ hζ w 1 v,
         fun a => rightDerivative F ζ hζ w 2 v a - rightDerivative F ζ hζ w 4 v a,
         fun a => rightDerivative F ζ hζ w 3 v a + rightDerivative F ζ hζ w 5 v a] c
        (g * compactInsertion F ζ hζ (compactDirectionCurve w c t))) t := by
  dsimp only
  have hword := word_mem_smoothSpace u word
  have hs := KPMsSameContinuationGreen.SmoothDescent.smooth_pullback _ hword.1
  have he : (fun a => KPSmoothActualFlowData.wordDerivative F ζ hζ word u.val
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a)) =
      word.foldr (fun b f => rightDerivative F ζ hζ b.1 b.2 f)
        (fun a => u.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a)) := by
    exact (KPMsGreenFlux.IntrinsicAveraging.pullback_word u.val word).symm
  rw [he] at hs
  have hd := direction_hasDerivAt _ hs g (compactDirection w c) t
  simp only [← compact_direction_curve_insertion, compact_directionJet] at hd
  fin_cases c <;> exact hd

private theorem compact_second_binding
    (u : smoothSpace F ζ hζ U) (w : NumberField.InfinitePlace F) (c : Fin 3) (g : G F ζ hζ) :
    let v := fun a => u.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a)
    deriv (fun t => deriv (fun r => v (g *
      compactInsertion F ζ hζ (compactDirectionCurve w c t) *
      compactInsertion F ζ hζ (compactDirectionCurve w c r))) 0) 0 =
      ![rightDerivative F ζ hζ w 1 (rightDerivative F ζ hζ w 1 v) g,
        rightDerivative F ζ hζ w 2 (rightDerivative F ζ hζ w 2 v) g -
          rightDerivative F ζ hζ w 4 (rightDerivative F ζ hζ w 2 v) g -
          rightDerivative F ζ hζ w 2 (rightDerivative F ζ hζ w 4 v) g +
          rightDerivative F ζ hζ w 4 (rightDerivative F ζ hζ w 4 v) g,
        rightDerivative F ζ hζ w 3 (rightDerivative F ζ hζ w 3 v) g +
          rightDerivative F ζ hζ w 5 (rightDerivative F ζ hζ w 3 v) g +
          rightDerivative F ζ hζ w 3 (rightDerivative F ζ hζ w 5 v) g +
          rightDerivative F ζ hζ w 5 (rightDerivative F ζ hζ w 5 v) g] c := by
  dsimp only
  have hinner (t : ℝ) := (word_compact_hasDerivAt u [] w c
    (g * compactInsertion F ζ hζ (compactDirectionCurve w c t)) 0).deriv
  simp only [List.foldr_nil, compact_curve_zero] at hinner
  simp_rw [hinner]
  have h1 := word_compact_hasDerivAt u [(w,1)] w c g 0
  have h2 := word_compact_hasDerivAt u [(w,2)] w c g 0
  have h3 := word_compact_hasDerivAt u [(w,3)] w c g 0
  have h4 := word_compact_hasDerivAt u [(w,4)] w c g 0
  have h5 := word_compact_hasDerivAt u [(w,5)] w c g 0
  simp only [List.foldr_cons, List.foldr_nil, compact_curve_zero] at h1 h2 h3 h4 h5
  fin_cases c
  · exact h1.deriv
  · have hd := (h2.sub h4).deriv
    dsimp at hd ⊢
    convert hd using 1 <;> try ring
  · have hd := (h3.add h5).deriv
    dsimp at hd ⊢
    convert hd using 1 <;> try ring

theorem compactTensor_binding
    (u : smoothSpace F ζ hζ U) (w : NumberField.InfinitePlace F) (x : X F ζ hζ) :
    compactTensor (fun i j => KPSmoothActualFlowData.wordDerivative F ζ hζ [(w,i),(w,j)] u.val x) =
      -∑ c : Fin 3, deriv (fun t => deriv (fun r => u.val
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (x.out *
          compactInsertion F ζ hζ (compactDirectionCurve w c t) *
          compactInsertion F ζ hζ (compactDirectionCurve w c r)))) 0) 0 := by
  have hp (i j : Fin 6) : rightDerivative F ζ hζ w i (rightDerivative F ζ hζ w j
      (fun a => u.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a))) x.out =
      KPSmoothActualFlowData.wordDerivative F ζ hζ [(w,i),(w,j)] u.val x := by
    change KPSmoothActualFlowData.wordDerivative F ζ hζ [(w,i),(w,j)] u.val
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ x.out) = _
    have hq : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ x.out = x := Quotient.out_eq x
    rw [hq]
  simp_rw [compact_second_binding u w _ x.out, hp]
  simp only [compactTensor, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, add_zero]
  simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Matrix.cons_val_one, Matrix.cons_val_zero]
  ring
end DedekindZetaZeroFree.FourierContinuation.ResidualCompactTensor

end

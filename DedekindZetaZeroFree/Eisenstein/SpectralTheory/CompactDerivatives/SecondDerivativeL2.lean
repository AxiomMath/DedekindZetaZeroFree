module

public import DedekindZetaZeroFree.Adeles.Quotients.Haar.CompactTranslation
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactDerivatives.TensorIdentity
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.CompactOrbitL2

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
open scoped Classical NumberField Topology ENNReal BigOperators
open MeasureTheory

namespace DedekindZetaZeroFree.FourierContinuation.ResidualCompactSecondL2
open KPMsClearedTruncationL2

open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.CompactOrbitL2 renaming span_memLp → span_memLp

private theorem compact_second_memLp
    {X K : Type*} [MeasurableSpace X] [Group K]
    (μ : Measure X) (a : K → X → X)
    (ha : ∀ k, MeasurePreserving (a k) μ μ)
    (hadd : ∀ k l x, a l (a k x) = a (k*l) x)
    (f : X → ℂ) (hf : MemLp f 2 μ)
    [FiniteDimensional ℂ (Submodule.span ℂ (Set.range (fun k => f ∘ a k)))]
    (k l : ℝ → K)
    (hd : ∀ t x, DifferentiableAt ℝ (fun r => f (a (l r) (a (k t) x))) 0)
    (hdd : ∀ x, DifferentiableAt ℝ (fun t => deriv (fun r => f (a (l r) (a (k t) x))) 0) 0) :
    MemLp (fun x => deriv (fun t => deriv (fun r => f (a (l r) (a (k t) x))) 0) 0) 2 μ := by
  let o : K → X → ℂ := fun b => f ∘ a b
  let V := Submodule.span ℂ (Set.range o)
  have ho (b : K) : MemLp (o b) 2 μ := hf.comp_measurePreserving (ha b)
  have hfirst (t : ℝ) : (fun x => deriv (fun r => f (a (l r) (a (k t) x))) 0) ∈ V := by
    let v : ℝ → X → ℂ := fun r x => f (a (l r) (a (k t) x))
    have hv (r : ℝ) : v r ∈ V := by
      have he : v r = o (k t * l r) := by funext x; exact congrArg f (hadd _ _ x)
      rw [he]
      exact Submodule.subset_span (Set.mem_range_self _)
    have ht : Filter.Tendsto (fun r : ℝ => fun x =>
        (r : ℂ)⁻¹ * (v r x - v 0 x)) (𝓝[≠] 0)
        (𝓝 (fun x => deriv (fun r => v r x) 0)) := by
      apply tendsto_pi_nhds.mpr
      intro x
      simpa only [zero_add, Complex.real_smul, Complex.ofReal_inv] using
        (hd t x).hasDerivAt.tendsto_slope_zero
    exact V.closed_of_finiteDimensional.mem_of_tendsto ht
      (Filter.Eventually.of_forall fun r => V.smul_mem _ (V.sub_mem (hv r) (hv 0)))
  apply span_memLp μ o ho
  have ht : Filter.Tendsto (fun t : ℝ => fun x => (t : ℂ)⁻¹ *
      (deriv (fun r => f (a (l r) (a (k t) x))) 0 -
       deriv (fun r => f (a (l r) (a (k 0) x))) 0)) (𝓝[≠] 0)
      (𝓝 (fun x => deriv (fun t => deriv (fun r => f (a (l r) (a (k t) x))) 0) 0)) := by
    apply tendsto_pi_nhds.mpr
    intro x
    simpa only [zero_add, Complex.real_smul, Complex.ofReal_inv] using
      (hdd x).hasDerivAt.tendsto_slope_zero
  exact V.closed_of_finiteDimensional.mem_of_tendsto ht
    (Filter.Eventually.of_forall fun t => V.smul_mem _ (V.sub_mem (hfirst t) (hfirst 0)))
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {U : Level F ζ hζ}

 abbrev WD := KPSmoothActualFlowData.wordDerivative F ζ hζ

open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes renaming direction_hasDerivAt → direction_hasDerivAt

open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes renaming compactDirection → compactDirection
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes renaming compactDirectionCurve → compactDirectionCurve
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes renaming compact_direction_curve_insertion → compact_direction_curve_insertion
open _root_.DedekindZetaZeroFree.FourierContinuation.ResidualCompactTensor renaming compact_directionJet → compact_directionJet
open _root_.DedekindZetaZeroFree.FourierContinuation.ResidualCompactTensor renaming compact_curve_zero → compact_curve_zero
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalWordRegularity renaming word_mem_smoothSpace → word_mem_smoothSpace
open _root_.DedekindZetaZeroFree.FourierContinuation.ResidualCompactHaar renaming quotient_compact_measurePreserving → quotient_compact_measurePreserving

 def compactAction (k : KPMsGreenFlux.K F) : X F ζ hζ → X F ζ hζ :=
  KPSmoothActualFlowData.rightTranslate F ζ hζ (KPMsGreenFlux.compactInsertion F ζ hζ k)

private theorem compactAction_mul (k l : KPMsGreenFlux.K F) (x : X F ζ hζ) :
    compactAction l (compactAction k x) = compactAction (k*l) x := by
  induction x using Quotient.inductionOn with
  | h g =>
    change KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (g * KPMsGreenFlux.compactInsertion F ζ hζ k * KPMsGreenFlux.compactInsertion F ζ hζ l) = _
    congr 1
    rw [mul_assoc]
    exact congrArg (fun a => g*a)
      ((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1 _ _).symm

private theorem smooth_word_compact_hasDerivAt
    (u : smoothSpace F ζ hζ U) (word : List (KPSmoothActualFlowData.B F))
    (w : NumberField.InfinitePlace F) (c : Fin 3) (x : X F ζ hζ) (t : ℝ) :
    HasDerivAt (fun r => WD word u.val (compactAction (compactDirectionCurve w c r) x))
      (![WD ((w,1)::word) u.val,
        fun a => WD ((w,2)::word) u.val a - WD ((w,4)::word) u.val a,
        fun a => WD ((w,3)::word) u.val a + WD ((w,5)::word) u.val a] c
        (compactAction (compactDirectionCurve w c t) x)) t := by
  let v : smoothSpace F ζ hζ U := ⟨WD word u.val,
    word_mem_smoothSpace u word⟩
  have hv := KPMsSameContinuationGreen.SmoothDescent.smooth_pullback v.val v.property.1
  induction x using Quotient.inductionOn with
  | h g =>
    have hh := direction_hasDerivAt
      (fun a => v.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a)) hv
      g (compactDirection w c) t
    simp only [← compact_direction_curve_insertion, compact_directionJet] at hh
    fin_cases c <;> exact hh

private theorem smooth_compact_second_differentiable
    (u : smoothSpace F ζ hζ U) (w : NumberField.InfinitePlace F) (c : Fin 3)
    (x : X F ζ hζ) :
    DifferentiableAt ℝ (fun t => deriv (fun r => u.val
      (compactAction (compactDirectionCurve w c r)
        (compactAction (compactDirectionCurve w c t) x))) 0) 0 := by
  have hz (y : X F ζ hζ) : compactAction (compactDirectionCurve w c 0) y = y := by
    induction y using Quotient.inductionOn with
    | h g => exact congrArg (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) (compact_curve_zero w c g)
  have hi (t : ℝ) := (smooth_word_compact_hasDerivAt u [] w c
    (compactAction (compactDirectionCurve w c t) x) 0).deriv
  simp only [KPSmoothActualFlowData.wordDerivative, hz] at hi
  simp_rw [hi]
  have h1 := (smooth_word_compact_hasDerivAt u [(w,1)] w c x 0).differentiableAt
  have h2 := (smooth_word_compact_hasDerivAt u [(w,2)] w c x 0).differentiableAt
  have h3 := (smooth_word_compact_hasDerivAt u [(w,3)] w c x 0).differentiableAt
  have h4 := (smooth_word_compact_hasDerivAt u [(w,4)] w c x 0).differentiableAt
  have h5 := (smooth_word_compact_hasDerivAt u [(w,5)] w c x 0).differentiableAt
  fin_cases c
  · exact h1
  · exact h2.sub h4
  · exact h3.add h5

private theorem smooth_compact_curve_second_memLp
    (u : smoothSpace F ζ hζ U) (hu : MemLp u.val 2 R.quotientHaar)
    [FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range (fun k : KPMsGreenFlux.K F => u.val ∘ compactAction k)))]
    (w : NumberField.InfinitePlace F) (c : Fin 3) :
    MemLp (fun x => deriv (fun t => deriv (fun r => u.val
      (compactAction (compactDirectionCurve w c r)
        (compactAction (compactDirectionCurve w c t) x))) 0) 0) 2 R.quotientHaar := by
  exact compact_second_memLp R.quotientHaar compactAction
    (quotient_compact_measurePreserving R) compactAction_mul u.val hu
    (compactDirectionCurve w c) (compactDirectionCurve w c)
    (fun t x => (smooth_word_compact_hasDerivAt u [] w c
      (compactAction (compactDirectionCurve w c t) x) 0).differentiableAt)
    (smooth_compact_second_differentiable u w c)

open DedekindZetaZeroFree.FourierContinuation.ResidualCompactTensor (compactTensor_binding)
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.FullSixCoercivity renaming compactTensor → compactTensor

def compactForcing (u : X F ζ hζ → ℂ) : X F ζ hζ → ℂ :=
  fun x => (∑ w : NumberField.InfinitePlace F,
    compactTensor (fun i j => WD [(w,i),(w,j)] u x)) / 2

theorem smooth_compactForcing_memLp_of_finiteOrbit
    (u : smoothSpace F ζ hζ U) (hu : MemLp u.val 2 R.quotientHaar)
    [FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range (fun k : KPMsGreenFlux.K F => u.val ∘ compactAction k)))] :
    MemLp (compactForcing u.val) 2 R.quotientHaar := by
  have ht (w : NumberField.InfinitePlace F) :
      MemLp (fun x => compactTensor (fun i j => WD [(w,i),(w,j)] u.val x)) 2 R.quotientHaar := by
    have hh := (memLp_finset_sum Finset.univ (fun c _ =>
      smooth_compact_curve_second_memLp u hu w c)).neg
    have he : (fun x : X F ζ hζ => compactTensor (fun i j => WD [(w,i),(w,j)] u.val x)) =
        (fun x => -(∑ c : Fin 3, deriv (fun t => deriv (fun r => u.val
          (compactAction (compactDirectionCurve w c r)
            (compactAction (compactDirectionCurve w c t) x))) 0) 0)) := by
      funext x
      rw [compactTensor_binding]
      have hq (c : Fin 3) (t r : ℝ) : compactAction (compactDirectionCurve w c r)
          (compactAction (compactDirectionCurve w c t) x) =
          KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (x.out *
            KPMsGreenFlux.compactInsertion F ζ hζ (compactDirectionCurve w c t) *
            KPMsGreenFlux.compactInsertion F ζ hζ (compactDirectionCurve w c r)) := by
        have hx : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ x.out = x := Quotient.out_eq x
        conv_lhs => rw [← hx]
        rfl
      congr 1
      apply Finset.sum_congr rfl
      intro c hc
      congr 2
      funext t
      congr 2
      funext r
      exact congrArg u.val (hq c t r).symm
    exact MemLp.ae_eq (Filter.Eventually.of_forall (fun x => (congrFun he x).symm)) hh
  have hs : MemLp (fun x => ∑ w : NumberField.InfinitePlace F,
      compactTensor (fun i j => WD [(w,i),(w,j)] u.val x)) 2 R.quotientHaar :=
    memLp_finset_sum Finset.univ (fun w _ => ht w)
  change MemLp (fun x : X F ζ hζ =>
    (∑ w, compactTensor (fun i j => WD [(w,i),(w,j)] u.val x)) / (2 : ℂ)) 2 R.quotientHaar
  exact MemLp.ae_eq
    (Filter.Eventually.of_forall (fun x => (div_eq_mul_inv _ _).symm)) (hs.mul_const (2 : ℂ)⁻¹)

end DedekindZetaZeroFree.FourierContinuation.ResidualCompactSecondL2

end

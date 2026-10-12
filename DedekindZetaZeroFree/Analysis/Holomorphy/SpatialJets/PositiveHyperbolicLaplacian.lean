module

public import DedekindZetaZeroFree.Analysis.RightFrame.CauchyCoefficient
public import DedekindZetaZeroFree.Geometry.Hyperbolic.Laplacian.ChartGreenIdentities
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

noncomputable section

open scoped ContDiff
open Topology

namespace DedekindZetaZeroFree.KPContSpatialParameterPositiveLaplacian

open RightFrame.PullbackWords RightFrame.CauchyCoefficient
open scoped BigOperators

private theorem jet_word {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (u : E → ℂ) (W : Set E) (hW : IsOpen W)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u W) (x : E) (hx : x ∈ W) (m : Fin n → E) :
    iteratedFDerivWithin ℝ n u W x m = constantDirectionWord (List.ofFn m) u x := by
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (hW.uniqueDiffOn)
    ((hu.contDiffAt (hW.mem_nhds hx)).of_le (by simp)) hx]
  induction n generalizing x with
  | zero => simp [constantDirectionWord, directionalWord, iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [((hu x hx).contDiffAt (hW.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (m := n) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) |>.iteratedFDeriv_succ_apply_left']
    have heq : (fun y => iteratedFDeriv ℝ n u y (Fin.tail m)) =ᶠ[𝓝 x]
        constantDirectionWord (List.ofFn (Fin.tail m)) u :=
      Filter.eventually_of_mem (hW.mem_nhds hx) fun y hy => ih y hy _
    rw [heq.fderiv_eq]
    simp only [List.ofFn_succ, constantDirectionWord, directionalWord]
    rfl

private theorem coefficient_deriv (O : Set ℂ) (hO : IsOpen O) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f O) (s : ℂ) (hs : s ∈ O) (r : ℝ) (hr : 0 < r)
    (hd : Metric.closedBall s r ⊆ O) (k : ℕ) :
    iteratedDerivWithin k f O s = (k.factorial : ℂ) * cauchyCoefficient (fun z (_ : Unit) => f z) s r k () := by
  rw [iteratedDerivWithin_eq_iteratedDeriv hO.uniqueDiffOn
    (hf.analyticAt (hO.mem_nhds hs)).contDiffAt hs]
  have hc := (hf.mono hd).circleIntegral_one_div_sub_center_pow_smul hr k
  have he : (fun z => (z-s)^(-((k:ℤ)+1)) * f z) =
      (fun z => (1 / (z-s)^(k+1)) • f z) := by
    funext z
    rw [show -((k:ℤ)+1) = -((k+1:ℕ):ℤ) by omega, zpow_neg, zpow_natCast]
    simp [smul_eq_mul]
  rw [cauchyCoefficient, he, hc, smul_eq_mul]
  have hn : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hp : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := Complex.two_pi_I_ne_zero
  field_simp

private theorem fields_word {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Type*} (a : B → E) (w : List B) (f : E → ℂ) :
    directionalWord (fun b (_ : E) => a b) w f = constantDirectionWord (w.map a) f := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [directionalWord, constantDirectionWord, List.map_cons] at *; rw [ih]

private theorem compact_joint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) [CompactSpace K] (O : Set ℂ) (j : ℂ → ContinuousMap K ℂ)
    (hj : ContinuousOn j O) (F : ℂ → E → ℂ)
    (he : ∀ z ∈ O, ∀ x : K, F z x.val = j z x) :
    ContinuousOn (fun p : ℂ × E => F p.1 p.2) (O ×ˢ K) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hz : Continuous (fun p : O ×ˢ K => j p.val.1) :=
    hj.domRestrict.comp (continuous_subtype_val.fst.subtype_mk (fun p => p.property.1))
  have hx : Continuous (fun p : O ×ˢ K => (⟨p.val.2, p.property.2⟩ : K)) :=
    continuous_subtype_val.snd.subtype_mk _
  have hh := continuous_eval.comp (hz.prodMk hx)
  apply hh.congr
  intro p
  exact (he p.val.1 p.property.1 ⟨p.val.2, p.property.2⟩).symm

private theorem word_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Type*} (W : Set E) (hW : IsOpen W) (a : B → E) (f : E → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f W) (w : List B) :
    ContDiffOn ℝ (⊤ : ℕ∞) (directionalWord (fun b (_ : E) => a b) w f) W := by
  induction w with
  | nil => exact hf
  | cons b w ih => exact (ih.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const

private theorem word_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Type*} (W : Set E) (hW : IsOpen W) (a : B → E) (w : List B)
    (f g : E → ℂ) (hfg : Set.EqOn f g W) :
    Set.EqOn (directionalWord (fun b (_ : E) => a b) w f)
      (directionalWord (fun b (_ : E) => a b) w g) W := by
  induction w with
  | nil => exact hfg
  | cons b w ih =>
    intro x hx
    dsimp only [directionalWord]
    have he : directionalWord (fun b (_ : E) => a b) w f =ᶠ[𝓝 x]
        directionalWord (fun b (_ : E) => a b) w g :=
      Filter.eventually_of_mem (hW.mem_nhds hx) (fun y hy => ih hy)
    rw [he.fderiv_eq]

private theorem word_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Type*} (W : Set E) (hW : IsOpen W) (a : B → E) (w : List B)
    (c : ℂ) (f : E → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f W) :
    ∀ x ∈ W, directionalWord (fun b (_ : E) => a b) w (fun y => c * f y) x =
      c * directionalWord (fun b (_ : E) => a b) w f x := by
  induction w with
  | nil => intro x hx; rfl
  | cons b w ih =>
    intro x hx
    have he : directionalWord (fun b (_ : E) => a b) w (fun y => c * f y) =ᶠ[𝓝 x]
        (fun y => c * directionalWord (fun b (_ : E) => a b) w f y) :=
      Filter.eventually_of_mem (hW.mem_nhds hx) (fun y hy => ih y hy)
    dsimp only [directionalWord]
    rw [he.fderiv_eq, fderiv_const_mul]
    · rfl
    · exact ((word_smooth W hW a f hf w).contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)

theorem parameter_jets_positive_laplacian (d : ℕ) (W : Set (HyperbolicChart.Space d))
    (hW : IsOpen W) (O : Set ℂ) (hO : IsOpen O)
    (u : ℂ → HyperbolicChart.Space d → ℂ)
    (hu : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (u z) W)
    (hjets : ∀ (K : Set (HyperbolicChart.Space d)) (hK : IsCompact K), K ⊆ W →
      ∀ (n : ℕ) (v : Fin n → HyperbolicChart.Space d),
        letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
        ∃ j : ℂ → ContinuousMap K ℂ, DifferentiableOn ℂ j O ∧
          ∀ z ∈ O, ∀ x : K,
            j z x = iteratedFDerivWithin ℝ n (u z) W x.val v) :
    ∀ k s, s ∈ O →
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => iteratedDerivWithin k (fun z => u z y) O s) W ∧
      ∀ x ∈ W, HyperbolicChart.laplacian d
          (fun y => iteratedDerivWithin k (fun z => u z y) O s) x =
        iteratedDerivWithin k (fun z => HyperbolicChart.laplacian d (u z) x) O s := by
  classical
  let B := Fin d × Fin 3
  let a : B → HyperbolicChart.Space d := fun b => HyperbolicChart.coordinateVector d b.1 b.2
  let fields : B → HyperbolicChart.Space d → HyperbolicChart.Space d := fun b _ => a b
  have hjword (K : Set (HyperbolicChart.Space d)) (hK : IsCompact K) (hKW : K ⊆ W)
      (w : List B) :
      letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
      ∃ j : ℂ → ContinuousMap K ℂ, DifferentiableOn ℂ j O ∧
        ∀ z ∈ O, ∀ x : K, j z x = directionalWord fields w (u z) x.val := by
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    obtain ⟨j,hj,he⟩ := hjets K hK hKW (w.map a).length (w.map a).get
    refine ⟨j,hj,?_⟩
    intro z hz x
    rw [he z hz x, jet_word _ _ W hW (hu z hz) _ (hKW x.property), List.ofFn_get]
    exact (congrFun (fields_word a w (u z)) x.val).symm
  have hhol (w : List B) (x : HyperbolicChart.Space d) (hx : x ∈ W) :
      DifferentiableOn ℂ (fun z => directionalWord fields w (u z) x) O := by
    obtain ⟨j,hj,he⟩ := hjword {x} (isCompact_singleton) (Set.singleton_subset_iff.mpr hx) w
    letI : CompactSpace ({x} : Set (HyperbolicChart.Space d)) :=
      isCompact_iff_compactSpace.mp isCompact_singleton
    have hh := (ContinuousMap.evalCLM ℂ (⟨x,Set.mem_singleton x⟩ : ({x} : Set (HyperbolicChart.Space d)))).differentiable.comp_differentiableOn hj
    exact hh.congr (fun z hz => (he z hz ⟨x,Set.mem_singleton x⟩).symm)
  intro k s hs
  obtain ⟨r,hr,hd⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hs)
  have hjoint (w : List B) (K : Set (HyperbolicChart.Space d)) (hK : IsCompact K)
      (hKW : K ⊆ W) :
      ContinuousOn (fun p : ℂ × HyperbolicChart.Space d => directionalWord fields w (u p.1) p.2)
        (Metric.closedBall s r ×ˢ K) := by
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    obtain ⟨j,hj,he⟩ := hjword K hK hKW w
    exact (compact_joint K O j hj.continuousOn _ (fun z hz x => (he z hz x).symm)).mono
      (Set.prod_mono hd Set.Subset.rfl)
  have hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) W := fun b => contDiffOn_const
  have hframe : ∀ x ∈ W, ∃ e : Module.Basis B ℝ (HyperbolicChart.Space d),
      ∀ b, e b = fields b x := by
    intro x hx
    refine ⟨(EuclideanSpace.basisFun B ℝ).toBasis, ?_⟩
    intro b
    change EuclideanSpace.basisFun B ℝ b = HyperbolicChart.coordinateVector d b.1 b.2
    rw [EuclideanSpace.basisFun_apply]
    ext j
    simp [HyperbolicChart.coordinateVector, EuclideanSpace.single_apply]
  have hhol0 : ∀ x ∈ W, DifferentiableOn ℂ (fun z => u z x) O := hhol []
  let c := cauchyCoefficient u s r k
  let p := fun y => iteratedDerivWithin k (fun z => u z y) O s
  have he : Set.EqOn p (fun y => (k.factorial : ℂ) * c y) W := by
    intro x hx
    exact coefficient_deriv O hO _ (hhol0 x hx) s hs r hr hd k
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) c W :=
    coefficient_smooth W hW fields hfields hframe O hO u s r hr hd hu hjoint hhol0 k
  have hp : ContDiffOn ℝ (⊤ : ℕ∞) p W :=
    (contDiffOn_const.mul hc).congr (fun x hx => he hx)
  refine ⟨hp, ?_⟩
  have hcomm (w : List B) (x : HyperbolicChart.Space d) (hx : x ∈ W) :
      directionalWord fields w p x =
        iteratedDerivWithin k (fun z => directionalWord fields w (u z) x) O s := by
    rw [word_congr W hW a w p _ he hx, word_mul W hW a w _ c hc x hx]
    rw [word_commute W hW fields hfields hframe O hO u s r hr hd hu hjoint hhol0 k w x hx]
    exact (coefficient_deriv O hO _ (hhol w x hx) s hs r hr hd k).symm
  intro x hx
  have hreg (w : List B) : ContDiffWithinAt ℂ k
      (fun z => directionalWord fields w (u z) x) O s :=
    ((hhol w x hx).analyticAt (hO.mem_nhds hs)).contDiffAt.contDiffWithinAt
  have hcd (i : Fin d) (b : Fin 3) (f : HyperbolicChart.Space d → ℂ) :
      HyperbolicChart.coordinateDerivative d i b f = directionalWord fields [(i,b)] f := rfl
  have hcdd (i : Fin d) (b : Fin 3) (f : HyperbolicChart.Space d → ℂ) :
      HyperbolicChart.coordinateDerivative d i b (HyperbolicChart.coordinateDerivative d i b f) =
        directionalWord fields [(i,b),(i,b)] f := rfl
  have hsumreg (i : Fin d) : ContDiffWithinAt ℂ k
      (fun z => -directionalWord fields [(i,2),(i,2)] (u z) x +
        2 * directionalWord fields [(i,2)] (u z) x -
        (Real.exp (2 * x (i,2)) : ℂ) *
          (directionalWord fields [(i,0),(i,0)] (u z) x +
           directionalWord fields [(i,1),(i,1)] (u z) x)) O s :=
    ((hreg [(i,2),(i,2)]).neg.add (contDiffWithinAt_const.mul (hreg [(i,2)]))).sub
      (contDiffWithinAt_const.mul ((hreg [(i,0),(i,0)]).add (hreg [(i,1),(i,1)])))
  change HyperbolicChart.laplacian d p x = _
  simp only [HyperbolicChart.laplacian]
  simp only [hcdd]
  simp only [hcd]
  rw [iteratedDerivWithin_fun_sum hs hO.uniqueDiffOn (fun i hi => hsumreg i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcomm [(i,2),(i,2)] x hx, hcomm [(i,2)] x hx,
    hcomm [(i,0),(i,0)] x hx, hcomm [(i,1),(i,1)] x hx]
  simp only [sub_eq_add_neg]
  rw [iteratedDerivWithin_fun_add hs hO.uniqueDiffOn
      ((hreg [(i,2),(i,2)]).neg.add (contDiffWithinAt_const.mul (hreg [(i,2)])))
      ((contDiffWithinAt_const.mul ((hreg [(i,0),(i,0)]).add (hreg [(i,1),(i,1)]))).neg),
    iteratedDerivWithin_fun_add hs hO.uniqueDiffOn
      (hreg [(i,2),(i,2)]).neg (contDiffWithinAt_const.mul (hreg [(i,2)]))]
  simp only [iteratedDerivWithin_fun_neg, iteratedDerivWithin_const_mul_field]
  rw [iteratedDerivWithin_fun_add hs hO.uniqueDiffOn
    (hreg [(i,0),(i,0)]) (hreg [(i,1),(i,1)])]

end DedekindZetaZeroFree.KPContSpatialParameterPositiveLaplacian

end

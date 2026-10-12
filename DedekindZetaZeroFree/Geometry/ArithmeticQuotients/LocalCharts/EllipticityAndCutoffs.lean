module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.NormalChartsAndHyperbolicDensity
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.FiniteIsotropyQuotientMeasure
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.SmoothPartitions

@[expose] public section

section
noncomputable section
open scoped Classical ENNReal InnerProductSpace Matrix
open MeasureTheory Topology

namespace DedekindZetaZeroFree.CoreChartLocalizers.CutoffConstruction

open HyperbolicChart

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

 def scaleTFun (d : ℕ) (z : KPArch.Space d) (v : KPArch.Space d) :
    HyperbolicChart.Space d :=
  WithLp.toLp 2 (fun ik : Fin d × Fin 3 =>
    if ik.2 = 2 then (v ik.1).2
    else (KPArch.height (z ik.1))⁻¹ *
      (if ik.2 = 0 then (v ik.1).1.re else (v ik.1).1.im))

 def scaleTLin (d : ℕ) (z : KPArch.Space d) :
    KPArch.Space d →ₗ[ℝ] HyperbolicChart.Space d where
  toFun := scaleTFun d z
  map_add' := by
    intro a b
    ext ik
    simp only [scaleTFun, PiLp.toLp_apply, Pi.add_apply, Prod.fst_add, Prod.snd_add,
      Complex.add_re, Complex.add_im]
    by_cases h2 : ik.2 = 2
    · simp [h2]
    · by_cases h0 : ik.2 = 0
      · simp [h2, h0, mul_add]
      · simp [h2, h0, mul_add]
  map_smul' := by
    intro c a
    ext ik
    simp only [scaleTFun, PiLp.toLp_apply, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd,
      Complex.smul_re, Complex.smul_im]
    by_cases h2 : ik.2 = 2
    · simp [h2]
    · by_cases h0 : ik.2 = 0
      · simp [h2, h0, mul_comm, mul_left_comm, mul_assoc]
      · simp [h2, h0, mul_comm, mul_left_comm, mul_assoc]

 def scaleT (d : ℕ) (z : KPArch.Space d) :
    KPArch.Space d →L[ℝ] HyperbolicChart.Space d :=
  (scaleTLin d z).toContinuousLinearMap

private lemma scaleT_apply (d : ℕ) (z : KPArch.Space d) (v : KPArch.Space d) :
    scaleT d z v = scaleTFun d z v := rfl

private lemma scaleT_norm_sq (d : ℕ) (z : KPArch.Space d) (v : KPArch.Space d) :
    ‖scaleT d z v‖ ^ 2 = KPArch.metric d z v := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, KPArch.metric]
  simp only [scaleT_apply, scaleTFun, PiLp.toLp_apply, Fin.sum_univ_three]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  norm_num
  ring

private lemma gram_quadform {n d : ℕ}
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] HyperbolicChart.Space d)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    (∑ j, ∑ k, ((‖S (EuclideanSpace.single j 1 + EuclideanSpace.single k 1)‖ ^ 2 -
        ‖S (EuclideanSpace.single j 1)‖ ^ 2 - ‖S (EuclideanSpace.single k 1)‖ ^ 2) / 2)
        * ξ j * ξ k) = ‖S ξ‖ ^ 2 := by
  have hinner : ∀ j k, ((‖S (EuclideanSpace.single j 1 + EuclideanSpace.single k 1)‖ ^ 2 -
        ‖S (EuclideanSpace.single j 1)‖ ^ 2 - ‖S (EuclideanSpace.single k 1)‖ ^ 2) / 2)
        = ⟪S (EuclideanSpace.single j 1), S (EuclideanSpace.single k 1)⟫_ℝ := by
    intro j k
    rw [map_add, norm_add_sq_real]
    ring
  simp only [hinner]
  have hξ : ξ = ∑ j, ξ j • EuclideanSpace.single j 1 := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr ξ]
    simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
  have hS : S ξ = ∑ j, ξ j • S (EuclideanSpace.single j 1) := by
    conv_lhs => rw [hξ]
    rw [map_sum]
    simp only [map_smul]
  rw [hS, ← real_inner_self_eq_norm_sq]
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

private lemma inv_quadform_lower {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (Λ : ℝ) (hΛ : 0 < Λ)
    (hbound : ∀ v : Fin n → ℝ, v ⬝ᵥ (M *ᵥ v) ≤ Λ * (v ⬝ᵥ v)) :
    ∀ v : Fin n → ℝ, (v ⬝ᵥ v) / Λ ≤ v ⬝ᵥ (M⁻¹ *ᵥ v) := by
  intro v
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hMinv : M⁻¹.PosDef := hM.inv
  have hQ : 0 ≤ v ⬝ᵥ (M⁻¹ *ᵥ v) := hMinv.posSemidef.dotProduct_mulVec_nonneg v
  have hA : 0 < v ⬝ᵥ v := by
    have hne : v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_self_eq_zero.mp h)
    exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)) (Ne.symm hne)
  have hCS := hMinv.star_dotProduct_mulVec_mul_le v (M *ᵥ v)
  simp only [star_trivial] at hCS
  have hMM : M⁻¹ *ᵥ (M *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hM.isUnit),
      Matrix.one_mulVec]
  rw [hMM] at hCS
  have hBB : (M *ᵥ v) ⬝ᵥ v = v ⬝ᵥ (M *ᵥ v) := dotProduct_comm _ _
  rw [hBB] at hCS
  have hb := hbound v
  have hstep : (v ⬝ᵥ v) * (v ⬝ᵥ v) ≤ (v ⬝ᵥ (M⁻¹ *ᵥ v) * Λ) * (v ⬝ᵥ v) := by
    calc (v ⬝ᵥ v) * (v ⬝ᵥ v) ≤ (v ⬝ᵥ (M⁻¹ *ᵥ v)) * (Λ * (v ⬝ᵥ v)) :=
          le_trans hCS (mul_le_mul_of_nonneg_left hb hQ)
      _ = (v ⬝ᵥ (M⁻¹ *ᵥ v) * Λ) * (v ⬝ᵥ v) := by ring
  have hfin : v ⬝ᵥ v ≤ v ⬝ᵥ (M⁻¹ *ᵥ v) * Λ := le_of_mul_le_mul_right hstep hA
  rw [div_le_iff₀ hΛ]
  linarith [hfin]

theorem chart_uniform_ellipticity (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : Chart F ζ hζ hF U A) :
    ∃ e : ℝ, 0 < e ∧
      ∀ x, x ∈ closure (Metric.ball (0 : E C.n) C.radius) →
        ∀ ξ : E C.n,
          e * ‖ξ‖ ^ 2 ≤
            ∑ j, ∑ k, C.energyMatrix F ζ hζ hF U x j k * ξ j * ξ k := by
  let d := KPCuspLogShape.dimension F
  have hscale : ∀ z : KPArch.Space d, Function.Injective (scaleT d z) := by
    intro z v w h
    have heq : ∀ i k, scaleTFun d z v (i, k) = scaleTFun d z w (i, k) :=
      fun i k => congrArg (fun a : HyperbolicChart.Space d => a (i, k)) h
    ext i : 1
    apply Prod.ext
    · apply Complex.ext
      · have hh := heq i 0
        simpa [scaleTFun, KPArch.height, Real.exp_ne_zero] using hh
      · have hh := heq i 1
        simpa [scaleTFun, KPArch.height, Real.exp_ne_zero] using hh
    · have hh := heq i 2
      simpa [scaleTFun] using hh
  have hinj : ∀ x ∈ C.extendedDomain, Function.Injective (fderiv ℝ C.coordinates x) := by
    obtain ⟨g, hg, hleft⟩ := C.smooth_inverse
    intro x hx
    have hc := (C.smooth_coordinates.contDiffAt (C.open_extendedDomain.mem_nhds hx)).differentiableAt (by simp)
    have hg' := (hg.contDiffAt (C.coordinates_open.mem_nhds ⟨x, hx, rfl⟩)).differentiableAt (by simp)
    have heq : (g ∘ C.coordinates) =ᶠ[𝓝 x] id := by
      filter_upwards [C.open_extendedDomain.mem_nhds hx] with y hy
      exact hleft y hy
    have hder : (fderiv ℝ g (C.coordinates x)).comp (fderiv ℝ C.coordinates x) =
        ContinuousLinearMap.id ℝ (E C.n) := by
      rw [← fderiv_comp x hg' hc, heq.fderiv_eq]
      exact fderiv_id
    intro v w hvw
    have := congrArg (fun T : E C.n →L[ℝ] E C.n => T v) hder
    have := congrArg (fun T : E C.n →L[ℝ] E C.n => T w) hder
    have hv : fderiv ℝ g (C.coordinates x) (fderiv ℝ C.coordinates x v) = v :=
      congrArg (fun T : E C.n →L[ℝ] E C.n => T v) hder
    have hw : fderiv ℝ g (C.coordinates x) (fderiv ℝ C.coordinates x w) = w :=
      congrArg (fun T : E C.n →L[ℝ] E C.n => T w) hder
    rw [hvw, hw] at hv
    exact hv.symm
  let Sx : E C.n → (E C.n →L[ℝ] HyperbolicChart.Space d) :=
    fun x => (scaleT d (C.coordinates x)).comp (fderiv ℝ C.coordinates x)
  have hmetric : ∀ x w, KPArch.metric d (C.coordinates x) (fderiv ℝ C.coordinates x w) = ‖Sx x w‖ ^ 2 := by
    intro x w
    exact (scaleT_norm_sq d _ _).symm
  dsimp only [d] at hmetric
  have hMentry : ∀ x j k, C.metricMatrix F ζ hζ hF U x j k =
      ⟪Sx x (EuclideanSpace.single j 1), Sx x (EuclideanSpace.single k 1)⟫_ℝ := by
    intro x j k
    unfold Chart.metricMatrix
    rw [hmetric, hmetric, hmetric, map_add, norm_add_sq_real]
    ring
  have hquad : ∀ x (v : Fin C.n → ℝ),
      v ⬝ᵥ (C.metricMatrix F ζ hζ hF U x *ᵥ v) = ‖Sx x (WithLp.toLp 2 v)‖ ^ 2 := by
    intro x v
    rw [← gram_quadform (Sx x) (WithLp.toLp 2 v)]
    simp only [Chart.metricMatrix, hmetric, dotProduct, Matrix.mulVec, Finset.mul_sum,
      PiLp.toLp_apply]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hposdef : ∀ x ∈ C.extendedDomain, (C.metricMatrix F ζ hζ hF U x).PosDef := by
    intro x hx
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    constructor
    · ext j k
      simp only [Matrix.conjTranspose_apply, star_trivial, hMentry]
      exact real_inner_comm _ _
    · intro v hv
      simp only [star_trivial, hquad]
      apply sq_pos_of_pos
      apply norm_pos_iff.mpr
      intro heq
      have hh : Sx x (WithLp.toLp 2 v) = Sx x 0 := by simpa using heq
      have hz := hinj x hx ((hscale (C.coordinates x)) hh)
      apply hv
      exact congrArg WithLp.ofLp hz
  let B : E C.n → ℝ := fun x => ∑ i : Fin d, ((Real.exp (-(C.coordinates x i).2)) ^ 2 + 1)
  let L : E C.n → ℝ := fun x => B x * ‖fderiv ℝ C.coordinates x‖ ^ 2 + 1
  have hB : ∀ x, 0 ≤ B x := fun x => Finset.sum_nonneg (fun i _ => by positivity)
  have hL : ∀ x, 0 < L x := by
    intro x
    dsimp only [L]
    have := mul_nonneg (hB x) (sq_nonneg ‖fderiv ℝ C.coordinates x‖)
    linarith
  have hbound : ∀ x (v : Fin C.n → ℝ),
      v ⬝ᵥ (C.metricMatrix F ζ hζ hF U x *ᵥ v) ≤ L x * (v ⬝ᵥ v) := by
    intro x v
    let w : E C.n := WithLp.toLp 2 v
    have hnorm : ‖w‖ ^ 2 = v ⬝ᵥ v := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [w, PiLp.toLp_apply, dotProduct, pow_two]
    have hm : KPArch.metric d (C.coordinates x) (fderiv ℝ C.coordinates x w) ≤
        B x * ‖fderiv ℝ C.coordinates x w‖ ^ 2 := by
      unfold KPArch.metric
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      have hf : ‖(fderiv ℝ C.coordinates x w i).1‖ ≤ ‖fderiv ℝ C.coordinates x w‖ :=
        (norm_fst_le _).trans (norm_le_pi_norm _ i)
      have hs : ‖(fderiv ℝ C.coordinates x w i).2‖ ≤ ‖fderiv ℝ C.coordinates x w‖ :=
        (norm_snd_le _).trans (norm_le_pi_norm _ i)
      have hf2 : ‖(fderiv ℝ C.coordinates x w i).1‖ ^ 2 ≤ ‖fderiv ℝ C.coordinates x w‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hf 2
      have hs2 : (fderiv ℝ C.coordinates x w i).2 ^ 2 ≤ ‖fderiv ℝ C.coordinates x w‖ ^ 2 := by
        simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hs 2
      simp only [KPArch.height, ← Real.exp_neg]
      nlinarith [mul_le_mul_of_nonneg_left hf2 (sq_nonneg (Real.exp (-(C.coordinates x i).2)))]
    have hop := (fderiv ℝ C.coordinates x).le_opNorm w
    have hop2 := pow_le_pow_left₀ (norm_nonneg _) hop 2
    rw [hquad]
    change ‖Sx x w‖ ^ 2 ≤ L x * (v ⬝ᵥ v)
    rw [← hmetric]
    calc
      KPArch.metric d (C.coordinates x) (fderiv ℝ C.coordinates x w) ≤
          B x * ‖fderiv ℝ C.coordinates x w‖ ^ 2 := hm
      _ ≤ B x * (‖fderiv ℝ C.coordinates x‖ * ‖w‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hop2 (hB x)
      _ ≤ L x * (v ⬝ᵥ v) := by
        rw [← hnorm]
        dsimp only [L]
        nlinarith [sq_nonneg ‖w‖]
  have hLcont : ContinuousOn L C.extendedDomain := by
    have hc := C.smooth_coordinates.continuousOn
    have hD := C.smooth_coordinates.continuousOn_fderiv_of_isOpen C.open_extendedDomain (by simp)
    have hBc : ContinuousOn B C.extendedDomain := by
      apply continuousOn_finset_sum
      intro i _
      have hi : ContinuousOn (fun x => (C.coordinates x i).2) C.extendedDomain :=
        ((continuous_apply i : Continuous (fun z : KPArch.Space d => z i)).comp_continuousOn hc).snd
      exact ((Real.continuous_exp.comp_continuousOn hi.neg).pow 2).add continuousOn_const
    exact (hBc.mul (hD.norm.pow 2)).add continuousOn_const
  let K := closure (Metric.ball (0 : E C.n) C.radius)
  have hK : IsCompact K := by
    rw [show K = Metric.closedBall (0 : E C.n) C.radius from closure_ball _ (ne_of_gt C.positive_radius)]
    exact isCompact_closedBall _ _
  have h0 : (0 : E C.n) ∈ K := subset_closure (Metric.mem_ball_self C.positive_radius)
  obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn ⟨0, h0⟩ (hLcont.mono C.closed_ball_in_extension)
  refine ⟨1 / L x₀, by positivity, ?_⟩
  intro x hx ξ
  have hupper : ∀ v : Fin C.n → ℝ,
      v ⬝ᵥ (C.metricMatrix F ζ hζ hF U x *ᵥ v) ≤ L x₀ * (v ⬝ᵥ v) := by
    intro v
    exact (hbound x v).trans (mul_le_mul_of_nonneg_right (hmax hx)
      (Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))))
  have hfin := inv_quadform_lower (C.metricMatrix F ζ hζ hF U x)
    (hposdef x (C.closed_ball_in_extension hx)) (L x₀) (hL x₀) hupper (WithLp.ofLp ξ)
  have hnorm : (WithLp.ofLp ξ) ⬝ᵥ (WithLp.ofLp ξ) = ‖ξ‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, pow_two]
  rw [hnorm] at hfin
  convert hfin using 1
  · ring
  · simp only [Chart.energyMatrix, dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring

end DedekindZetaZeroFree.CoreChartLocalizers.CutoffConstruction

end

end

section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.CoreChartLocalizers.CutoffConstruction

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

private theorem toBase_continuousOn (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : Chart F ζ hζ hF U A) :
    ContinuousOn (C.toBase F ζ hζ hF U) C.extendedDomain := by
  have h1 : Continuous (fun z : KPFiniteCuspAtlas.SymmetricSpace F =>
      A.components ⟨C.component, KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component)) z⟩) :=
    A.components.continuous.comp (continuous_sigmaMk.comp continuous_quot_mk)
  have hfun : (fun z : KPFiniteCuspAtlas.SymmetricSpace F =>
      A.components ⟨C.component, KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component)) z⟩)
      ∘ C.coordinates = C.toBase F ζ hζ hF U := by
    funext y
    simp only [Function.comp_apply, A.components_formula, Chart.toBase]
  rw [← hfun]
  exact h1.comp_continuousOn C.smooth_coordinates.continuousOn

private theorem toBase_orthogonal (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : Chart F ζ hζ hF U A) (g : C.G F ζ hζ hF U) (x : E C.n)
    (hx : x ∈ C.extendedDomain) :
    C.toBase F ζ hζ hF U (C.orthogonal g x) = C.toBase F ζ hζ hF U x := by
  unfold Chart.toBase
  rw [C.equivariance g x hx]
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component))
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  exact MulAction.mem_orbit_iff.mpr ⟨g.val, rfl⟩

private theorem mem_ball_of_toBase_mem_O (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : Chart F ζ hζ hF U A) {x : E C.n} (hx : x ∈ C.extendedDomain)
    (hO : C.toBase F ζ hζ hF U x ∈ C.O F ζ hζ hF U) :
    x ∈ Metric.ball 0 C.radius := by
  obtain ⟨y, hy, hyx⟩ := hO
  have hy_ext : y ∈ C.extendedDomain := C.closed_ball_in_extension (subset_closure hy)
  have h : C.toBase F ζ hζ hF U x = C.toBase F ζ hζ hF U y := hyx.symm
  have hb : KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component))
        (C.coordinates x) =
      KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component))
        (C.coordinates y) := by
    have he := A.components.injective
      ((A.components_formula C.component (KPCuspSiegel.projection F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component))
          (C.coordinates x))).trans
        (h.trans (A.components_formula C.component (KPCuspSiegel.projection F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative C.component))
          (C.coordinates y))).symm))
    exact eq_of_heq (Sigma.mk.inj he).2
  have ho := MulAction.orbitRel_apply.mp (Quotient.exact hb)
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp ho
  have hγ' : ((γ⁻¹ : KPCuspGenuineMonodromy.Component F ζ hζ U
      (A.representative C.component)) : KPCuspArithmetic.PGL2 F) •
      C.coordinates x = C.coordinates y := by
    change γ⁻¹ • C.coordinates x = C.coordinates y
    rw [← hγ]
    simp
  have hstab : γ⁻¹ ∈ MulAction.stabilizer _ C.center :=
    C.separated γ⁻¹ x y hx hy_ext hγ'
  let g : C.G F ζ hζ hF U := ⟨γ⁻¹, hstab⟩
  have hgx : C.orthogonal g x ∈ C.extendedDomain := by
    rw [← C.invariant_extension g]
    exact ⟨x, hx, rfl⟩
  have hgy : C.orthogonal g x = y := by
    apply congrArg Subtype.val
      (C.coordinates_embedding.injective (a₁ := ⟨C.orthogonal g x, hgx⟩)
        (a₂ := ⟨y, hy_ext⟩) ?_)
    change C.coordinates (C.orthogonal g x) = C.coordinates y
    rw [C.equivariance g x hx]
    exact hγ'
  have hnorm : ‖x‖ = ‖y‖ := by
    rw [← hgy, LinearIsometryEquiv.norm_map]
  rw [Metric.mem_ball, dist_zero_right] at hy ⊢
  rw [hnorm]
  exact hy

theorem chart_lifted_cutoff (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (C : Chart F ζ hζ hF U A) (f : X F ζ hζ U → ℝ)
    (hcompact : HasCompactSupport f)
    (hsupport : tsupport f ⊆ C.O F ζ hζ hF U)
    (hsmooth : ∀ j, ContDiff ℝ (⊤ : ℕ∞)
      (fun z => f (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j)
        (KPCuspSiegel.projection F _ z)))) :
    let cutoff : E C.n → ℝ :=
      (Metric.ball 0 C.radius).indicator (fun x => f (C.toBase F ζ hζ hF U x))
    ContDiff ℝ (⊤ : ℕ∞) cutoff ∧ HasCompactSupport cutoff ∧
      tsupport cutoff ⊆ Metric.ball 0 C.radius ∧
      ∀ (g : C.G F ζ hζ hF U) x, cutoff (C.orthogonal g x) = cutoff x := by
  let cutoff : E C.n → ℝ :=
    (Metric.ball 0 C.radius).indicator (fun x => f (C.toBase F ζ hζ hF U x))
  change ContDiff ℝ (⊤ : ℕ∞) cutoff ∧ HasCompactSupport cutoff ∧
    tsupport cutoff ⊆ Metric.ball 0 C.radius ∧
    ∀ (g : C.G F ζ hζ hF U) x, cutoff (C.orthogonal g x) = cutoff x
  have hcontOn := toBase_continuousOn F ζ hζ hF U A C

  have hW_open : IsOpen
      {y : E C.n | y ∈ C.extendedDomain ∧ C.toBase F ζ hζ hF U y ∉ tsupport f} := by
    have h1 := hcontOn.isOpen_inter_preimage C.open_extendedDomain
      (isClosed_tsupport f).isOpen_compl
    convert h1 using 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]

  have hkey : ∀ y ∈ C.extendedDomain, C.toBase F ζ hζ hF U y ∈ C.O F ζ hζ hF U →
      y ∈ Metric.ball 0 C.radius :=
    fun y hy hyO => mem_ball_of_toBase_mem_O F ζ hζ hF U A C hy hyO

  have hcut_W : ∀ y, y ∈ C.extendedDomain → C.toBase F ζ hζ hF U y ∉ tsupport f →
      cutoff y = 0 := by
    intro y hyext hyts
    have hg0 : f (C.toBase F ζ hζ hF U y) = 0 := by
      by_contra hne
      exact hyts (subset_tsupport f (Function.mem_support.mpr hne))
    by_cases hyb : y ∈ Metric.ball 0 C.radius
    · simp only [cutoff, Set.indicator_of_mem hyb, hg0]
    · simp only [cutoff, Set.indicator_of_notMem hyb]

  have hU_open : IsOpen
      ({y : E C.n | y ∈ C.extendedDomain ∧ C.toBase F ζ hζ hF U y ∉ tsupport f}
        ∪ {y : E C.n | C.radius < ‖y‖}) :=
    hW_open.union (isOpen_lt continuous_const continuous_norm)
  have hcutU : ∀ y ∈
      ({y : E C.n | y ∈ C.extendedDomain ∧ C.toBase F ζ hζ hF U y ∉ tsupport f}
        ∪ {y : E C.n | C.radius < ‖y‖}), cutoff y = 0 := by
    intro y hy
    rcases hy with hy | hy
    · exact hcut_W y hy.1 hy.2
    · have hyb : y ∉ Metric.ball 0 C.radius := by
        rw [Metric.mem_ball, dist_zero_right]
        exact not_lt.mpr hy.le
      simp only [cutoff, Set.indicator_of_notMem hyb]

  have hsphere_notMem : ∀ x ∈ closure (Metric.ball 0 C.radius),
      x ∉ Metric.ball 0 C.radius → C.toBase F ζ hζ hF U x ∉ tsupport f := by
    intro x hxcl hxb hxts
    exact hxb (hkey x (C.closed_ball_in_extension hxcl) (hsupport hxts))

  have hcont : ContDiff ℝ (⊤ : ℕ∞) cutoff := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Metric.ball 0 C.radius
    · have hxext : x ∈ C.extendedDomain := C.closed_ball_in_extension (subset_closure hx)
      have hg_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun y => f (C.toBase F ζ hζ hF U y)) C.extendedDomain := by
        have houter : ContDiff ℝ (⊤ : ℕ∞)
            (fun z : KPFiniteCuspAtlas.SymmetricSpace F =>
              f (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative C.component)
                (KPCuspSiegel.projection F (KPCuspGenuineMonodromy.Component F ζ hζ U
                  (A.representative C.component)) z))) := hsmooth C.component
        have hcomp := houter.comp_contDiffOn C.smooth_coordinates
        convert hcomp using 1
        funext y
        simp only [Function.comp_apply, Chart.toBase]
      have hgat : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => f (C.toBase F ζ hζ hF U y)) x :=
        hg_smooth.contDiffAt (C.open_extendedDomain.mem_nhds hxext)
      refine hgat.congr_of_eventuallyEq ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
      simp only [cutoff, Set.indicator_of_mem hy]
    · rw [Metric.mem_ball, dist_zero_right] at hx
      have hxU : x ∈
          ({y : E C.n | y ∈ C.extendedDomain ∧ C.toBase F ζ hζ hF U y ∉ tsupport f}
            ∪ {y : E C.n | C.radius < ‖y‖}) := by
        rcases lt_or_eq_of_le (le_of_not_gt hx) with hlt | heq
        · exact Or.inr hlt
        · have hxcl : x ∈ closure (Metric.ball 0 C.radius) := by
            rw [closure_ball 0 (ne_of_gt C.positive_radius)]
            rw [Metric.mem_closedBall, dist_zero_right, heq]
          have hxb : x ∉ Metric.ball 0 C.radius := by
            rw [Metric.mem_ball, dist_zero_right, heq]
            exact lt_irrefl _
          exact Or.inl ⟨C.closed_ball_in_extension hxcl, hsphere_notMem x hxcl hxb⟩
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hU_open.mem_nhds hxU] with y hy
      exact hcutU y hy

  have hUc : ({y : E C.n | y ∈ C.extendedDomain ∧ C.toBase F ζ hζ hF U y ∉ tsupport f}
      ∪ {y : E C.n | C.radius < ‖y‖})ᶜ ⊆ Metric.ball 0 C.radius := by
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_union, not_or, Set.mem_setOf_eq] at hy
    rw [Metric.mem_ball, dist_zero_right]
    rcases lt_or_eq_of_le (not_lt.mp hy.2) with hlt | heq
    · exact hlt
    · exfalso
      have hxcl : y ∈ closure (Metric.ball 0 C.radius) := by
        rw [closure_ball 0 (ne_of_gt C.positive_radius)]
        rw [Metric.mem_closedBall, dist_zero_right, heq]
      have hyb : y ∉ Metric.ball 0 C.radius := by
        rw [Metric.mem_ball, dist_zero_right, heq]
        exact lt_irrefl _
      exact hy.1 ⟨C.closed_ball_in_extension hxcl, hsphere_notMem y hxcl hyb⟩
  have htsuppU : tsupport cutoff ⊆
      ({y : E C.n | y ∈ C.extendedDomain ∧ C.toBase F ζ hζ hF U y ∉ tsupport f}
        ∪ {y : E C.n | C.radius < ‖y‖})ᶜ := by
    rw [tsupport]
    exact closure_minimal (fun y hy hyU => hy (hcutU y hyU)) hU_open.isClosed_compl
  refine ⟨hcont, ?_, ?_, ?_⟩
  ·
    exact (isCompact_closedBall (0 : E C.n) C.radius).of_isClosed_subset
      (isClosed_tsupport cutoff)
      (htsuppU.trans (hUc.trans Metric.ball_subset_closedBall))
  ·
    exact htsuppU.trans hUc
  ·
    intro g x
    by_cases hx : x ∈ Metric.ball 0 C.radius
    · have hxext : x ∈ C.extendedDomain := C.closed_ball_in_extension (subset_closure hx)
      have hx' : C.orthogonal g x ∈ Metric.ball 0 C.radius := by
        rw [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
        rwa [Metric.mem_ball, dist_zero_right] at hx
      simp only [cutoff, Set.indicator_of_mem hx', Set.indicator_of_mem hx,
        toBase_orthogonal F ζ hζ hF U A C g x hxext]
    · have hx' : C.orthogonal g x ∉ Metric.ball 0 C.radius := fun h => hx (by
          rw [Metric.mem_ball, dist_zero_right] at h ⊢
          rwa [← LinearIsometryEquiv.norm_map (C.orthogonal g) x])
      simp only [cutoff, Set.indicator_of_notMem hx', Set.indicator_of_notMem hx]

end DedekindZetaZeroFree.CoreChartLocalizers.CutoffConstruction

end

end

section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.CoreChartLocalizers

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

theorem finite_cutoffs (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (K : Set (X F ζ hζ U)) (hK : IsCompact K) :
    Nonempty (FiniteCutoffs F ζ hζ hF U A K) := by
  obtain ⟨P⟩ := CutoffConstruction.finite_smooth_chart_partition F ζ hζ hF U A
    (CutoffConstruction.normal_charts_cover F ζ hζ hF U A) K hK
  choose ellipticity positive_ellipticity uniform_ellipticity using
    fun i => CutoffConstruction.chart_uniform_ellipticity F ζ hζ hF U A (P.chart i)
  let cutoff : ∀ i, E (P.chart i).n → ℝ := fun i =>
    (Metric.ball 0 (P.chart i).radius).indicator
      (fun x => P.phi i ((P.chart i).toBase F ζ hζ hF U x))
  have cutoff_properties : ∀ i,
      ContDiff ℝ (⊤ : ℕ∞) (cutoff i) ∧ HasCompactSupport (cutoff i) ∧
        tsupport (cutoff i) ⊆ Metric.ball 0 (P.chart i).radius ∧
        ∀ (g : (P.chart i).G F ζ hζ hF U) x,
          cutoff i ((P.chart i).orthogonal g x) = cutoff i x := by
    intro i
    exact CutoffConstruction.chart_lifted_cutoff F ζ hζ hF U A (P.chart i)
      (P.phi i) (P.compact_phi i) (P.support_phi i) (P.smooth_phi i)
  exact ⟨{
    count := P.count
    empty_case := P.empty_case
    chart := P.chart
    chart_measure := fun i =>
      CutoffConstruction.chart_quotient_measure F ζ hζ hF U A (P.chart i)
    ellipticity := ellipticity
    positive_ellipticity := positive_ellipticity
    uniform_ellipticity := uniform_ellipticity
    phi := P.phi
    nonnegative_phi := P.nonnegative_phi
    compact_phi := P.compact_phi
    support_phi := P.support_phi
    smooth_phi := P.smooth_phi
    neighborhood := P.neighborhood
    open_neighborhood := P.open_neighborhood
    covers_compact := P.covers_compact
    partition := P.partition
    cutoff := cutoff
    cutoff_formula := fun _ => rfl
    smooth_cutoff := fun i => (cutoff_properties i).1
    compact_cutoff := fun i => (cutoff_properties i).2.1
    support_cutoff := fun i => (cutoff_properties i).2.2.1
    invariant_cutoff := fun i => (cutoff_properties i).2.2.2
  }⟩

end DedekindZetaZeroFree.CoreChartLocalizers

end

end

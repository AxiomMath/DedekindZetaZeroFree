module

public import DedekindZetaZeroFree.Geometry.Hyperbolic.DivergenceIsometry
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LineBundles.CotangentPullbackIsometry

@[expose] public section

noncomputable section
open scoped Classical ContDiff BigOperators
open Filter Topology
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation
private theorem codifferential_smul_const (d : ℕ) (W : HyperbolicChart.Space d → HyperbolicChart.Cotangent d)
    (x : HyperbolicChart.Space d) (hW : DifferentiableAt ℝ W x) (c : ℂ) :
    HyperbolicChart.codifferential d (fun y => c • W y) x =
      c * HyperbolicChart.codifferential d W x := by
  unfold HyperbolicChart.codifferential HyperbolicChart.coordinateDerivative
  have hc (i : Fin d) (k : Fin 3) : DifferentiableAt ℝ (fun y => W y i k) x := by
    exact (differentiableAt_pi.mp ((differentiableAt_pi.mp hW) i)) k
  simp only [Pi.smul_apply, smul_eq_mul]
  change (∑ i : Fin d, (-(fderiv ℝ (fun y => c * W y i 0) x) (HyperbolicChart.coordinateVector d i 2) +
      2 * (c * W x i 0) - (Real.exp (x (i, 2)) : ℂ) * (fderiv ℝ (fun y => c * W y i 1) x) (HyperbolicChart.coordinateVector d i 0) -
      (Real.exp (x (i, 2)) : ℂ) * (fderiv ℝ (fun y => c * W y i 2) x) (HyperbolicChart.coordinateVector d i 1))) = _
  simp only [fderiv_const_mul (hc _ _) c, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
 def part (d : ℕ) (f : ℂ →L[ℝ] ℝ) (v : EuclideanSpace ℂ (Fin d × Fin 3)) :
    EuclideanSpace ℝ (Fin d × Fin 3) := WithLp.toLp 2 (fun k => f (v k))
private theorem part_contDiffAt (d : ℕ) (f : ℂ →L[ℝ] ℝ)
    (V : HyperbolicChart.Space d → EuclideanSpace ℂ (Fin d × Fin 3))
    (x : HyperbolicChart.Space d) (hV : ContDiffAt ℝ (⊤ : ℕ∞) V x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => part d f (V y)) x := by
  apply (contDiffAt_piLp 2).mpr
  intro k
  exact f.contDiff.contDiffAt.comp x (((EuclideanSpace.proj (𝕜 := ℂ) k).restrictScalars ℝ).contDiff.contDiffAt.comp x hV)
private theorem scalar_fderiv_map (d : ℕ) (f : ℂ →L[ℝ] ℝ)
    (g : HyperbolicChart.Space d → ℂ) (x v : HyperbolicChart.Space d)
    (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun y => f (g y)) x v = f (fderiv ℝ g x v) := by
  rw [show (fun y => f (g y)) = f ∘ g from rfl, fderiv_comp x f.differentiableAt hg,
    f.fderiv, ContinuousLinearMap.comp_apply]
private theorem part_codifferential (d : ℕ) (f : ℂ →L[ℝ] ℝ)
    (V : HyperbolicChart.Space d → EuclideanSpace ℂ (Fin d × Fin 3))
    (x : HyperbolicChart.Space d) (hV : ContDiffAt ℝ (⊤ : ℕ∞) V x) :
    f (HyperbolicChart.codifferential d ((CotangentLogCoframe.j d).symm ∘ V) x) =
      ∑ i : Fin d, (-(fderiv ℝ (fun y => (CotangentLogCoframe.H d y (part d f (V y))) (i, 2)) x
        (HyperbolicChart.coordinateVector d i 2)) + 2 * (CotangentLogCoframe.H d x (part d f (V x))) (i, 2) -
        fderiv ℝ (fun y => (CotangentLogCoframe.H d y (part d f (V y))) (i, 0)) x (HyperbolicChart.coordinateVector d i 0) -
        fderiv ℝ (fun y => (CotangentLogCoframe.H d y (part d f (V y))) (i, 1)) x (HyperbolicChart.coordinateVector d i 1)) := by
  have hv (k : Fin d × Fin 3) : DifferentiableAt ℝ (fun y => V y k) x :=
    (((EuclideanSpace.proj (𝕜 := ℂ) k).restrictScalars ℝ).differentiableAt.comp x (hV.differentiableAt (by simp)))
  have h_exp (i : Fin d) (k : Fin 3) (hk : k ≠ 2) :
      fderiv ℝ (fun y : HyperbolicChart.Space d => Real.exp (y (i,2))) x
        (HyperbolicChart.coordinateVector d i k) = 0 := by
    have hcoord : HasFDerivAt (fun y : HyperbolicChart.Space d => y (i,2)) (EuclideanSpace.proj (𝕜 := ℝ) (i,2)) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) (i,2)).hasFDerivAt
    rw [hcoord.exp.fderiv]
    simp [HyperbolicChart.coordinateVector, hk, Ne.symm hk]
  have hprod (i : Fin d) (k l : Fin 3) (hk : k ≠ 2) :
      fderiv ℝ (fun y : HyperbolicChart.Space d => Real.exp (y (i,2)) * f (V y (i,l))) x
        (HyperbolicChart.coordinateVector d i k) =
      Real.exp (x (i,2)) * f (fderiv ℝ (fun y => V y (i,l)) x (HyperbolicChart.coordinateVector d i k)) := by
    have hexp : DifferentiableAt ℝ (fun y : HyperbolicChart.Space d => Real.exp (y (i,2))) x := by fun_prop
    have hf : DifferentiableAt ℝ (fun y => f (V y (i,l))) x := f.differentiableAt.comp x (hv (i,l))
    rw [fderiv_fun_mul hexp hf]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      h_exp i k hk, mul_zero, add_zero, scalar_fderiv_map d f _ x _ (hv (i,l))]
  unfold HyperbolicChart.codifferential HyperbolicChart.coordinateDerivative
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply, CotangentLogCoframe.j, LinearEquiv.coe_mk, LinearEquiv.symm_mk,
    map_sub, map_add, map_neg]
  have h0 : (fun y => (CotangentLogCoframe.H d y (part d f (V y))) (i,0)) =
      fun y => Real.exp (y (i,2)) * f (V y (i,1)) := by funext y; rfl
  have h1 : (fun y => (CotangentLogCoframe.H d y (part d f (V y))) (i,1)) =
      fun y => Real.exp (y (i,2)) * f (V y (i,2)) := by funext y; rfl
  have h2 : (fun y => (CotangentLogCoframe.H d y (part d f (V y))) (i,2)) =
      fun y => f (V y (i,0)) := by funext y; rfl
  rw [h0, h1, h2, hprod i 0 1 (by decide), hprod i 1 2 (by decide),
    scalar_fderiv_map d f _ x _ (hv (i,0))]
  change -f ((fderiv ℝ (fun y => V y (i,0)) x) (HyperbolicChart.coordinateVector d i 2)) +
      f (2 * V x (i,0)) - f ((Real.exp (x (i,2)) : ℂ) * (fderiv ℝ (fun y => V y (i,1)) x) (HyperbolicChart.coordinateVector d i 0)) -
      f ((Real.exp (x (i,2)) : ℂ) * (fderiv ℝ (fun y => V y (i,2)) x) (HyperbolicChart.coordinateVector d i 1)) = _
  simp only [show 2 * V x (i,0) = (2 : ℝ) • V x (i,0) by simp [Complex.real_smul], map_smul, smul_eq_mul]
  have hmul (z : ℂ) : f ((Real.exp (x (i,2)) : ℂ) * z) = Real.exp (x (i,2)) * f z := by
    rw [show (Real.exp (x (i,2)) : ℂ) * z = Real.exp (x (i,2)) • z by simp [Complex.real_smul], map_smul]
    rfl
  rw [hmul, hmul]
  rfl

private theorem dual_push (d : ℕ) (ψ : HyperbolicChart.Space d → HyperbolicChart.Space d)
    (V W : EuclideanSpace ℂ (Fin d × Fin 3)) (y : HyperbolicChart.Space d)
    (hm : ∀ u v, HyperbolicChart.metric d (ψ y) (fderiv ℝ ψ y u) (fderiv ℝ ψ y v) =
      HyperbolicChart.metric d y u v)
    (hp : ∀ u, ∑ ik, W ik * ((CotangentLogCoframe.C d (ψ y) (fderiv ℝ ψ y u)) ik : ℂ) =
      ∑ ik, V ik * ((CotangentLogCoframe.C d y u) ik : ℂ)) (f : ℂ →L[ℝ] ℝ) :
    CotangentLogCoframe.H d (ψ y) (part d f W) =
      fderiv ℝ ψ y (CotangentLogCoframe.H d y (part d f V)) := by
  let Q : EuclideanSpace ℝ (Fin d × Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin d × Fin 3) :=
    (CotangentLogCoframe.C d (ψ y)).toContinuousLinearMap.comp
      ((fderiv ℝ ψ y).comp (CotangentLogCoframe.H d y).toContinuousLinearMap)
  have hinner (u v : EuclideanSpace ℝ (Fin d × Fin 3)) : inner ℝ (Q u) (Q v) = inner ℝ u v := by
    change inner ℝ (CotangentLogCoframe.C d (ψ y) _) (CotangentLogCoframe.C d (ψ y) _) = _
    rw [CotangentLogCoframe.inner_C]
    change HyperbolicChart.metric d (ψ y) (fderiv ℝ ψ y (CotangentLogCoframe.H d y u))
      (fderiv ℝ ψ y (CotangentLogCoframe.H d y v)) = _
    rw [hm, ← CotangentLogCoframe.inner_C]
    simp [CotangentLogCoframe.H]
  have hn (v : EuclideanSpace ℝ (Fin d × Fin 3)) : ‖Q v‖ = ‖v‖ := by
    have hh := hinner v v
    simp only [real_inner_self_eq_norm_sq] at hh
    nlinarith [norm_nonneg (Q v), norm_nonneg v]
  let li : EuclideanSpace ℝ (Fin d × Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d × Fin 3) :=
    { Q.toLinearMap with norm_map' := hn }
  let q := li.toLinearIsometryEquiv rfl
  have he : part d f W = Q (part d f V) := by
    apply ext_inner_left ℝ
    intro w
    obtain ⟨v,rfl⟩ := q.surjective w
    change inner ℝ (Q v) (part d f W) = inner ℝ (Q v) (Q (part d f V))
    rw [hinner]
    have hh := congrArg f (hp (CotangentLogCoframe.H d y v))
    have hmul (z : ℂ) (r : ℝ) : f (z * (r : ℂ)) = r * f z := by
      rw [show z * (r : ℂ) = r • z by simp [Complex.real_smul, mul_comm], map_smul]
      rfl
    simpa [PiLp.inner_apply, part, map_sum, hmul, CotangentLogCoframe.H,
      Q, ContinuousLinearMap.comp_apply, mul_comm] using hh
  rw [he]
  simp [Q, CotangentLogCoframe.H]

theorem coframe_codifferential_isometry (d : ℕ)
    (ψ : HyperbolicChart.Space d → HyperbolicChart.Space d)
    (V W : HyperbolicChart.Space d → EuclideanSpace ℂ (Fin d × Fin 3))
    (x : HyperbolicChart.Space d) (hψ : ContDiffAt ℝ 2 ψ x)
    (hV : ContDiffAt ℝ (⊤ : ℕ∞) V x) (hW : ContDiffAt ℝ (⊤ : ℕ∞) W (ψ x))
    (hm : ∀ᶠ y in nhds x, ∀ u v, HyperbolicChart.metric d (ψ y) (fderiv ℝ ψ y u)
      (fderiv ℝ ψ y v) = HyperbolicChart.metric d y u v)
    (hp : ∀ᶠ y in nhds x, ∀ u,
      ∑ ik, W (ψ y) ik * ((CotangentLogCoframe.C d (ψ y) (fderiv ℝ ψ y u)) ik : ℂ) =
        ∑ ik, V y ik * ((CotangentLogCoframe.C d y u) ik : ℂ)) :
    HyperbolicChart.codifferential d ((CotangentLogCoframe.j d).symm ∘ W) (ψ x) =
      HyperbolicChart.codifferential d ((CotangentLogCoframe.j d).symm ∘ V) x := by
  have hr (f : ℂ →L[ℝ] ℝ) :
      f (HyperbolicChart.codifferential d ((CotangentLogCoframe.j d).symm ∘ W) (ψ x)) =
        f (HyperbolicChart.codifferential d ((CotangentLogCoframe.j d).symm ∘ V) x) := by
    let A : HyperbolicChart.Space d → HyperbolicChart.Space d :=
      fun y => CotangentLogCoframe.H d y (part d f (V y))
    let B : HyperbolicChart.Space d → HyperbolicChart.Space d :=
      fun y => CotangentLogCoframe.H d y (part d f (W y))
    have ha : ContDiffAt ℝ 1 A x :=
      ((CotangentLogCoframe.contDiff_H d).contDiffAt.clm_apply
        (part_contDiffAt d f V x hV)).of_le (by simp)
    have hb : ContDiffAt ℝ 1 B (ψ x) :=
      ((CotangentLogCoframe.contDiff_H d).contDiffAt.clm_apply
        (part_contDiffAt d f W (ψ x) hW)).of_le (by simp)
    have hpush : (B ∘ ψ) =ᶠ[nhds x] fun y => fderiv ℝ ψ y (A y) := by
      filter_upwards [hm, hp] with y hy hpy
      exact dual_push d ψ (V y) (W (ψ y)) y hy hpy f
    rw [part_codifferential d f W (ψ x) hW, part_codifferential d f V x hV]
    exact HyperbolicChart.real_divergence_isometry d ψ A B x hψ ha hb hm hpush
  exact Complex.ext (hr Complex.reCLM) (hr Complex.imCLM)

private theorem metric_polarization (d : ℕ) (x u v : HyperbolicChart.Space d) :
    HyperbolicChart.metric d x (u+v) (u+v) =
      HyperbolicChart.metric d x u u + 2 * HyperbolicChart.metric d x u v +
        HyperbolicChart.metric d x v v := by
  simp only [HyperbolicChart.metric, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [PiLp.add_apply]
  ring

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

private theorem arch_coordinates (p : Coordinates F) :
    CotangentLogCoframe.A _ p = toArch F p := by
  funext i
  apply Prod.ext
  · apply Complex.ext <;> simp [CotangentLogCoframe.A, toArch]
  · rfl

private theorem evaluation_coordinates (Z : Cotangent F ζ hζ U) (p u : Coordinates F) :
    coframeEvaluation F ζ hζ U Z (toArch F p) (toArch F u) =
      ∑ ik, (Z ik : ℂ) * ((CotangentLogCoframe.C _ p u) ik : ℂ) := by
  rw [Fintype.sum_prod_type]
  unfold coframeEvaluation
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_three]
  obtain ⟨h0,h1,h2⟩ := CotangentLogCoframe.C_apply _ p u i
  rw [h0,h1,h2]
  simp [toArch, Complex.ofReal_mul]
  ring

theorem arithmetic_codifferential_covariant (W : Arch F → Cotangent F ζ hζ U)
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (γ : KPCuspArithmetic.PGL2 F) (c : ℂ)
    (hp : ∀ x v, coframeEvaluation F ζ hζ U (W (γ • x)) (γ • x)
      (fderiv ℝ (fun y : Arch F => γ • y) x v) =
        c * coframeEvaluation F ζ hζ U (W x) x v) (x : Arch F) :
    HyperbolicChart.codifferential _
        (fun p j k => (W (toArch F p) (j,k) : ℂ)) (fromArch F (γ • x)) =
      c * HyperbolicChart.codifferential _
        (fun p j k => (W (toArch F p) (j,k) : ℂ)) (fromArch F x) := by
  let d := KPCuspLogShape.dimension F
  let A := CotangentLogCoframe.A d
  let action : Arch F → Arch F := fun y => γ • y
  obtain ⟨B,hB⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  let g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
    fun j => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F j).embedding B
  have he : action = KPArch.productAction d g := by
    funext y
    change KPCuspSiegel.action F _ y = _
    rw [← hB, KPCuspSiegel.action_mk]; rfl
  have hact : ContDiff ℝ (⊤ : ℕ∞) action := (he ▸ KPArch.productAction_contDiff d g).of_le le_top
  let ψ : Coordinates F → Coordinates F := fun p => A.symm (action (A p))
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := A.symm.contDiff.comp (hact.comp A.contDiff)
  have hd (p : Coordinates F) : HasFDerivAt ψ
      (A.symm.toContinuousLinearMap.comp ((fderiv ℝ action (A p)).comp A.toContinuousLinearMap)) p :=
    A.symm.hasFDerivAt.comp p
      (((hact.differentiable (by simp) (A p)).hasFDerivAt).comp p A.hasFDerivAt)
  have hm0 (p u : Coordinates F) : HyperbolicChart.metric d (ψ p)
      (fderiv ℝ ψ p u) (fderiv ℝ ψ p u) = HyperbolicChart.metric d p u u := by
    rw [← CotangentLogCoframe.metric_A, (hd p).fderiv]
    change KPArch.metric d (A (A.symm _)) (A (A.symm _)) = _
    rw [A.apply_symm_apply, A.apply_symm_apply, he]
    change KPArch.metric d (KPArch.productAction d g (A p))
      (fderiv ℝ (KPArch.productAction d g) (A p) (A u)) = _
    rw [KPArch.metric_invariant, CotangentLogCoframe.metric_A]
  have hm (p u v : Coordinates F) : HyperbolicChart.metric d (ψ p)
      (fderiv ℝ ψ p u) (fderiv ℝ ψ p v) = HyperbolicChart.metric d p u v := by
    have hh := hm0 p (u+v)
    rw [map_add, metric_polarization, metric_polarization, hm0, hm0] at hh
    linarith
  let Z : Coordinates F → EuclideanSpace ℂ (Fin d × Fin 3) :=
    fun p => WithLp.toLp 2 (fun ik => (W (A p) ik : ℂ))
  have hZ : ContDiff ℝ (⊤ : ℕ∞) Z := by
    apply (contDiff_piLp 2).mpr
    intro ik
    exact ((Fiber F ζ hζ U).subtypeL.restrictScalars ℝ).contDiff.comp
      ((contDiff_piLp 2).mp (hW.comp A.contDiff) ik)
  have hpc (p u : Coordinates F) :
      ∑ ik, Z (ψ p) ik * ((CotangentLogCoframe.C d (ψ p) (fderiv ℝ ψ p u)) ik : ℂ) =
        ∑ ik, (c • Z p) ik * ((CotangentLogCoframe.C d p u) ik : ℂ) := by
    have hh := hp (A p) (A u)
    have he1 : A (ψ p) = action (A p) := A.apply_symm_apply _
    have he2 : A (fderiv ℝ ψ p u) = fderiv ℝ action (A p) (A u) := by
      rw [(hd p).fderiv]; exact A.apply_symm_apply _
    change coframeEvaluation F ζ hζ U (W (action (A p))) (action (A p))
      (fderiv ℝ action (A p) (A u)) = _ at hh
    rw [← he1, ← he2] at hh
    simp_rw [show ∀ p, A p = toArch F p from arch_coordinates F] at hh
    rw [evaluation_coordinates, evaluation_coordinates, Finset.mul_sum] at hh
    simpa only [Z, show ∀ p, A p = toArch F p from arch_coordinates F,
      WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul, mul_assoc] using hh
  have ht := coframe_codifferential_isometry d ψ (fun p => c • Z p) Z (fromArch F x)
    (hψ.contDiffAt.of_le (by simp)) ((hZ.const_smul c).contDiffAt) hZ.contDiffAt
    (Eventually.of_forall hm) (Eventually.of_forall hpc)
  have hcx : A (fromArch F x) = x := A.apply_symm_apply x
  have harg : ((CotangentLogCoframe.j d).symm ∘ Z) =
      fun p j k => (W (toArch F p) (j,k) : ℂ) := by
    funext p j k
    change (W (A p) (j,k) : ℂ) = _
    rw [show A p = toArch F p from arch_coordinates F p]
  have harg' : ((CotangentLogCoframe.j d).symm ∘ (fun p => c • Z p)) =
      fun p => c • (((CotangentLogCoframe.j d).symm ∘ Z) p) := by
    funext p; exact map_smul _ _ _
  rw [harg', codifferential_smul_const d _ _ (by
    exact ((CotangentLogCoframe.j d).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).differentiableAt.comp _
      (hZ.contDiffAt.differentiableAt (by simp))) c, harg] at ht
  change HyperbolicChart.codifferential d _ (A.symm (action (A (fromArch F x)))) = _ at ht
  rw [hcx] at ht
  exact ht

end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

end

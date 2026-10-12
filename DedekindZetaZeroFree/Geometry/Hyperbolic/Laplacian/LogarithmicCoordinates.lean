module

public import DedekindZetaZeroFree.Eisenstein.Induction.Cubic.SphericalFlatFamilies
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Cusps.CutoffGraphApproximation

@[expose] public section

noncomputable section
open scoped ContDiff

namespace DedekindZetaZeroFree.KPContArchLaplacianCoordinateBridge

variable (F : Type) [Field F] [NumberField F]

 def archCLM :
    KPCuspCutoffGraph.Coordinates F →L[ℝ] KPCuspCutoffGraph.Arch F :=
  LinearMap.toContinuousLinearMap {
    toFun := KPCuspCutoffGraph.toArch F
    map_add' := by intro x y; ext i <;> simp [KPCuspCutoffGraph.toArch]; rfl
    map_smul' := by
      intro c x
      ext i : 1
      apply Prod.ext <;> simp [KPCuspCutoffGraph.toArch, Complex.real_smul]
      apply Complex.ext <;> simp }

private lemma toArch_coordinateVector (i : Fin (KPCuspLogShape.dimension F)) (k : Fin 3) :
    KPCuspCutoffGraph.toArch F (HyperbolicChart.coordinateVector (KPCuspLogShape.dimension F) i k)
      = KPContFlatCuspCasimirSpecialization.coordinateDirection
          (KPCuspLogShape.dimension F) i k := by
  funext j
  simp only [KPCuspCutoffGraph.toArch, KPContFlatCuspCasimirSpecialization.coordinateDirection,
    HyperbolicChart.coordinateVector, WithLp.toLp]
  by_cases hj : j = i
  · subst hj
    fin_cases k <;>
      simp [Pi.single_eq_same, Prod.ext_iff, Complex.ext_iff, Prod.mk.injEq]
  · rw [Pi.single_eq_of_ne hj]
    simp [hj, Prod.ext_iff, Complex.ext_iff, Prod.mk.injEq]

private lemma archCLM_coordinateVector (i : Fin (KPCuspLogShape.dimension F)) (k : Fin 3) :
    archCLM F (HyperbolicChart.coordinateVector (KPCuspLogShape.dimension F) i k)
      = KPContFlatCuspCasimirSpecialization.coordinateDirection
          (KPCuspLogShape.dimension F) i k :=
  toArch_coordinateVector F i k

private lemma toArch_fromArch (x : KPCuspCutoffGraph.Arch F) :
    KPCuspCutoffGraph.toArch F (KPCuspCutoffGraph.fromArch F x) = x := by
  funext j; simp [KPCuspCutoffGraph.fromArch, KPCuspCutoffGraph.toArch]

private lemma first_deriv (f : KPCuspCutoffGraph.Arch F → ℂ) (hf : ContDiff ℝ 2 f)
    (i : Fin (KPCuspLogShape.dimension F)) (k : Fin 3)
    (p : KPCuspCutoffGraph.Coordinates F) :
    fderiv ℝ (f ∘ KPCuspCutoffGraph.toArch F) p
        (HyperbolicChart.coordinateVector (KPCuspLogShape.dimension F) i k)
      = fderiv ℝ f (KPCuspCutoffGraph.toArch F p)
          (KPContFlatCuspCasimirSpecialization.coordinateDirection
            (KPCuspLogShape.dimension F) i k) := by
  have hT : HasFDerivAt (KPCuspCutoffGraph.toArch F) (archCLM F) p :=
    (archCLM F).hasFDerivAt
  have hd : DifferentiableAt ℝ f (KPCuspCutoffGraph.toArch F p) :=
    hf.differentiable (by simp) _
  have h := (hd.hasFDerivAt.comp p hT).fderiv
  rw [h]
  simp only [ContinuousLinearMap.comp_apply]
  rw [archCLM_coordinateVector]

private lemma differentiableAt_fderiv_apply (f : KPCuspCutoffGraph.Arch F → ℂ)
    (hf : ContDiff ℝ 2 f) (z : KPCuspCutoffGraph.Arch F)
    (v : KPCuspCutoffGraph.Arch F) :
    DifferentiableAt ℝ (fun y => fderiv ℝ f y v) z := by
  fun_prop

private lemma second_deriv (f : KPCuspCutoffGraph.Arch F → ℂ) (hf : ContDiff ℝ 2 f)
    (i : Fin (KPCuspLogShape.dimension F)) (k : Fin 3) (x : KPCuspCutoffGraph.Arch F) :
    fderiv ℝ (fun q => fderiv ℝ (f ∘ KPCuspCutoffGraph.toArch F) q
        (HyperbolicChart.coordinateVector (KPCuspLogShape.dimension F) i k))
      (KPCuspCutoffGraph.fromArch F x)
      (HyperbolicChart.coordinateVector (KPCuspLogShape.dimension F) i k)
      = fderiv ℝ (fun y => fderiv ℝ f y
          (KPContFlatCuspCasimirSpecialization.coordinateDirection
            (KPCuspLogShape.dimension F) i k)) x
          (KPContFlatCuspCasimirSpecialization.coordinateDirection
            (KPCuspLogShape.dimension F) i k) := by
  have hfun : (fun q => fderiv ℝ (f ∘ KPCuspCutoffGraph.toArch F) q
        (HyperbolicChart.coordinateVector (KPCuspLogShape.dimension F) i k))
      = (fun y => fderiv ℝ f y
          (KPContFlatCuspCasimirSpecialization.coordinateDirection
            (KPCuspLogShape.dimension F) i k)) ∘ KPCuspCutoffGraph.toArch F := by
    funext q
    exact first_deriv F f hf i k q
  rw [hfun]
  have hT : HasFDerivAt (KPCuspCutoffGraph.toArch F) (archCLM F)
      (KPCuspCutoffGraph.fromArch F x) := (archCLM F).hasFDerivAt
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ f y
      (KPContFlatCuspCasimirSpecialization.coordinateDirection
        (KPCuspLogShape.dimension F) i k))
      (KPCuspCutoffGraph.toArch F (KPCuspCutoffGraph.fromArch F x)) :=
    differentiableAt_fderiv_apply F f hf _ _
  have h := (hd.hasFDerivAt.comp _ hT).fderiv
  rw [h]
  simp only [ContinuousLinearMap.comp_apply]
  rw [toArch_fromArch, archCLM_coordinateVector]

private lemma fromArch_apply_two (i : Fin (KPCuspLogShape.dimension F))
    (x : KPCuspCutoffGraph.Arch F) :
    (KPCuspCutoffGraph.fromArch F x) (i, 2) = (x i).2 := by
  simp [KPCuspCutoffGraph.fromArch]

private lemma heightCoeff (i : Fin (KPCuspLogShape.dimension F))
    (x : KPCuspCutoffGraph.Arch F) :
    ((KPArch.height (x i) ^ 2 : ℝ) : ℂ)
      = (Real.exp (2 * (KPCuspCutoffGraph.fromArch F x) (i, 2)) : ℂ) := by
  rw [fromArch_apply_two]
  rw [KPArch.height]
  congr 1
  rw [show (2 : ℝ) * (x i).2 = (x i).2 + (x i).2 by ring, Real.exp_add, pow_two]

private lemma first_deriv_cd (f : KPCuspCutoffGraph.Arch F → ℂ) (hf : ContDiff ℝ 2 f)
    (i : Fin (KPCuspLogShape.dimension F)) (k : Fin 3)
    (p : KPCuspCutoffGraph.Coordinates F) :
    HyperbolicChart.coordinateDerivative (KPCuspLogShape.dimension F) i k
        (f ∘ KPCuspCutoffGraph.toArch F) p
      = fderiv ℝ f (KPCuspCutoffGraph.toArch F p)
          (KPContFlatCuspCasimirSpecialization.coordinateDirection
            (KPCuspLogShape.dimension F) i k) :=
  first_deriv F f hf i k p

private lemma second_deriv_cd (f : KPCuspCutoffGraph.Arch F → ℂ) (hf : ContDiff ℝ 2 f)
    (i : Fin (KPCuspLogShape.dimension F)) (k : Fin 3) (x : KPCuspCutoffGraph.Arch F) :
    HyperbolicChart.coordinateDerivative (KPCuspLogShape.dimension F) i k
        (HyperbolicChart.coordinateDerivative (KPCuspLogShape.dimension F) i k
          (f ∘ KPCuspCutoffGraph.toArch F)) (KPCuspCutoffGraph.fromArch F x)
      = fderiv ℝ (fun y => fderiv ℝ f y
          (KPContFlatCuspCasimirSpecialization.coordinateDirection
            (KPCuspLogShape.dimension F) i k)) x
          (KPContFlatCuspCasimirSpecialization.coordinateDirection
            (KPCuspLogShape.dimension F) i k) :=
  second_deriv F f hf i k x

theorem bridge (F : Type) [Field F] [NumberField F]
    (f : KPArch.Space (KPCuspLogShape.dimension F) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F) f x =
      HyperbolicChart.laplacian (KPCuspLogShape.dimension F)
        (f ∘ KPCuspCutoffGraph.toArch F) (KPCuspCutoffGraph.fromArch F x) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  rw [show KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F) f x
      = KPContFlatCuspCasimirSpecialization.Δloc (KPCuspLogShape.dimension F) f x from rfl]
  rw [KPContFlatCuspCasimirSpecialization.Δloc_coordinate_expression _ f hf2 x]
  rw [HyperbolicChart.laplacian]
  apply Finset.sum_congr rfl
  intro i _
  rw [first_deriv_cd F f hf2 i 2 (KPCuspCutoffGraph.fromArch F x),
      second_deriv_cd F f hf2 i 2 x, second_deriv_cd F f hf2 i 0 x,
      second_deriv_cd F f hf2 i 1 x,
      toArch_fromArch, heightCoeff F i x]
  simp only [smul_eq_mul]

 def labeled (d n : ℕ) (places : Fin d ≃ Fin n) :
    HyperbolicChart.Space d ≃L[ℝ] KPArch.Space n :=
  (CotangentLogCoframe.A d).trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => KPArch.H3) places)
private lemma labeled_apply (d n : ℕ) (places : Fin d ≃ Fin n)
    (x : HyperbolicChart.Space d) (k : Fin n) :
    labeled d n places x k = CotangentLogCoframe.A d x (places.symm k) := by
  simp [labeled, ContinuousLinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft,
    Equiv.piCongrLeft, Equiv.piCongrLeft', Equiv.piCongrLeft'_apply]
private lemma labeled_vector (d n : ℕ) (places : Fin d ≃ Fin n) (i : Fin d) (k : Fin 3) :
    labeled d n places (HyperbolicChart.coordinateVector d i k) =
      KPContFlatCuspCasimirSpecialization.coordinateDirection n (places i) k := by
  funext j
  simp only [labeled_apply, CotangentLogCoframe.A_apply,
    HyperbolicChart.coordinateVector, WithLp.toLp,
    KPContFlatCuspCasimirSpecialization.coordinateDirection]
  by_cases h : places.symm j = i
  · have hj : j = places i := by simpa using congrArg places h
    subst j
    fin_cases k <;> simp [Pi.single_eq_same]
  · have hj : j ≠ places i := by
      intro he
      exact h (by simp [he])
    simp [h, hj]
private lemma labeled_first (d n : ℕ) (places : Fin d ≃ Fin n)
    (f : KPArch.Space n → ℂ) (hf : ContDiff ℝ 2 f) (i : Fin d) (k : Fin 3)
    (x : HyperbolicChart.Space d) :
    HyperbolicChart.coordinateDerivative d i k (f ∘ labeled d n places) x =
      fderiv ℝ f (labeled d n places x)
        (KPContFlatCuspCasimirSpecialization.coordinateDirection n (places i) k) := by
  have hh := ((hf.differentiable (by simp) _).hasFDerivAt.comp x
    (labeled d n places).hasFDerivAt).fderiv
  change fderiv ℝ (f ∘ labeled d n places) x _ = _
  rw [hh, ContinuousLinearMap.comp_apply]
  exact congrArg (fderiv ℝ f (labeled d n places x)) (labeled_vector d n places i k)
private lemma labeled_second (d n : ℕ) (places : Fin d ≃ Fin n)
    (f : KPArch.Space n → ℂ) (hf : ContDiff ℝ 2 f) (i : Fin d) (k : Fin 3)
    (x : HyperbolicChart.Space d) :
    HyperbolicChart.coordinateDerivative d i k
      (HyperbolicChart.coordinateDerivative d i k (f ∘ labeled d n places)) x =
      fderiv ℝ (fun y => fderiv ℝ f y
        (KPContFlatCuspCasimirSpecialization.coordinateDirection n (places i) k))
        (labeled d n places x)
        (KPContFlatCuspCasimirSpecialization.coordinateDirection n (places i) k) := by
  have hfun : HyperbolicChart.coordinateDerivative d i k (f ∘ labeled d n places) =
      (fun y => fderiv ℝ f y
        (KPContFlatCuspCasimirSpecialization.coordinateDirection n (places i) k)) ∘ labeled d n places := by
    funext y
    exact labeled_first d n places f hf i k y
  rw [hfun]
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ f y
      (KPContFlatCuspCasimirSpecialization.coordinateDirection n (places i) k))
      (labeled d n places x) := by fun_prop
  have hh := (hd.hasFDerivAt.comp x (labeled d n places).hasFDerivAt).fderiv
  change fderiv ℝ _ x _ = _
  rw [hh, ContinuousLinearMap.comp_apply]
  exact congrArg _ (labeled_vector d n places i k)

theorem bridge_equiv (d n : ℕ) (places : Fin d ≃ Fin n)
    (f : KPArch.Space n → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : HyperbolicChart.Space d) :
    KPContActualSphericalFlatStage.localLaplacian n f
        (fun k => CotangentLogCoframe.A d x (places.symm k)) =
      HyperbolicChart.laplacian d
        (fun y => f (fun k => CotangentLogCoframe.A d y (places.symm k))) x := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hm : (fun y => (fun k => CotangentLogCoframe.A d y (places.symm k))) =
      labeled d n places := by
    funext y k
    exact (labeled_apply d n places y k).symm
  rw [show (fun k => CotangentLogCoframe.A d x (places.symm k)) = labeled d n places x by
    exact congrFun hm x]
  conv_rhs => rw [show (fun y => f (fun k => CotangentLogCoframe.A d y (places.symm k))) =
      f ∘ labeled d n places by rw [← hm]; rfl]
  change KPContFlatCuspCasimirSpecialization.Δloc n f (labeled d n places x) =
    HyperbolicChart.laplacian d (f ∘ labeled d n places) x
  rw [KPContFlatCuspCasimirSpecialization.Δloc_coordinate_expression n f hf2,
    HyperbolicChart.laplacian]
  rw [← Equiv.sum_comp places]
  apply Finset.sum_congr rfl
  intro i _
  rw [labeled_first d n places f hf2 i 2 x,
    labeled_second d n places f hf2 i 2 x,
    labeled_second d n places f hf2 i 0 x,
    labeled_second d n places f hf2 i 1 x]
  have hheight : ((KPArch.height (labeled d n places x (places i)) ^ 2 : ℝ) : ℂ) =
      (Real.exp (2 * x (i,2)) : ℂ) := by
    simp only [labeled_apply, Equiv.symm_apply_apply, CotangentLogCoframe.A_apply, KPArch.height]
    congr 1
    rw [show (2 : ℝ) * x (i,2) = x (i,2) + x (i,2) by ring, Real.exp_add, pow_two]
  rw [hheight]
  simp only [smul_eq_mul]

end DedekindZetaZeroFree.KPContArchLaplacianCoordinateBridge

end

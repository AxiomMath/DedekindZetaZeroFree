module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.GradientDensityInvariance
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.LaplacianPairingInvariance
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.WeightedGreenDensity

@[expose] public section

section

noncomputable section
open MeasureTheory Filter
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPCompactGreenRadialIntegrability
open KPMeanZeroWeightedEnergy HyperbolicChart

private theorem arch_real (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  ext i <;> simp [arch, real]

private theorem smooth_arch (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (arch d) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.prodMk
  · exact Complex.equivRealProdCLM.symm.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (0 : Fin 3))).contDiff.prodMk
       (EuclideanSpace.proj (𝕜 := ℝ) (i, (1 : Fin 3))).contDiff)
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff

private theorem smooth_real (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (real d) := by
  apply (contDiff_piLp 2).mpr
  intro j
  rcases j with ⟨i, k⟩
  fin_cases k
  · simpa [real, Function.comp_def] using Complex.reCLM.contDiff.comp (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
  · simpa [real, Function.comp_def] using Complex.imCLM.contDiff.comp (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
  · simpa [real, Function.comp_def] using contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)

private theorem smooth_mean (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (KPCuspLogShape.meanHeight d) := by
  unfold KPCuspLogShape.meanHeight
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i hi
  exact contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)

private theorem derivative_smoothAt (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coordinateDerivative d i k g) x := by
  exact (hg.fderiv_right (by simp)).clm_apply contDiffAt_const

private theorem differential_smoothAt (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => differential d g q i k) x := by
  have he : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Space d => (Real.exp (q (i,2)) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.contDiffAt.exp)
  fin_cases k
  · simpa [differential] using derivative_smoothAt d g x hg i 2
  · simpa [differential] using he.mul (derivative_smoothAt d g x hg i 0)
  · simpa [differential] using he.mul (derivative_smoothAt d g x hg i 1)

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ} {T : ℝ}

private theorem representative_smoothAt (v : Representative ζ hζ S ρ V T)
    (x : Space (KPCuspLogShape.dimension F))
    (hx : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (v.val ∘ arch (KPCuspLogShape.dimension F)) x := by
  have hopen : IsOpen {z : KPArch.Space (KPCuspLogShape.dimension F) |
      T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z} :=
    isOpen_lt continuous_const (smooth_mean _).continuous
  exact (v.smooth.contDiffAt (hopen.mem_nhds hx)).comp x (smooth_arch _).contDiffAt

private theorem chart_smooth : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : KPCuspCharts.Coordinates F =>
      real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p)) :=
  (smooth_real _).comp ((KPCuspCharts.toArch_contDiff F).of_le (by simp))

private theorem chart_height (G : KPCuspCharts.ChartOutput F hF S D)
    (p : KPCuspCharts.Coordinates F) :
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F)
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))) = p.2 := by
  rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]

private theorem cutoff_smoothAt (v : Representative ζ hζ S ρ V T)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (x : Space (KPCuspLogShape.dimension F))
    (hx : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (rawCutoffUpstairs v η) x := by
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
    (hη.contDiffAt.comp x ((smooth_mean _).comp (smooth_arch _)).contDiffAt)).mul
      (representative_smoothAt v x hx)

private theorem cutoff_eventually_zero (v : Representative ζ hζ S ρ V T)
    (η : ℝ → ℝ) (x : Space (KPCuspLogShape.dimension F))
    (hx : KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x) ∉ tsupport η) :
    rawCutoffUpstairs v η =ᶠ[nhds x] 0 := by
  have hh := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto
    (((smooth_mean _).comp (smooth_arch _)).continuous.continuousAt)
  filter_upwards [hh] with q hq
  change η (KPCuspLogShape.meanHeight _ (arch _ q)) = 0 at hq
  simp [rawCutoffUpstairs, hq]

private theorem differential_zero_of_eventually_zero (d : ℕ)
    (f : Space d → ℂ) (x : Space d) (hf : f =ᶠ[nhds x] 0) :
    differential d f x = 0 := by
  have hh := hf.fderiv_eq (𝕜 := ℝ)
  have hz : fderiv ℝ (0 : Space d → ℂ) x = 0 := congrFun fderiv_zero x
  rw [hz] at hh
  funext i k
  fin_cases k <;> simp [differential, coordinateDerivative, hh]

private theorem cutoffGradientSq_continuousOn (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ContinuousOn (rawCutoffGradientSq v η) {p | T < p.2} := by
  apply continuousOn_of_forall_continuousAt
  intro p hp
  have hv := cutoff_smoothAt v η hη _ (by rwa [chart_height G p])
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro k hk
  exact (((differential_smoothAt _ _ _ hv i k).continuousAt.comp
    (f := fun p : KPCuspCharts.Coordinates F =>
      real _ (KPCuspCharts.toArch F p)) chart_smooth.continuous.continuousAt).norm.pow 2)

private theorem cutoffGradientSq_support (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ) :
    Function.support (rawCutoffGradientSq v η) ⊆ {p | p.2 ∈ tsupport η} := by
  intro p hp
  by_contra hn
  have hx : KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F)
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))) ∉ tsupport η := by
    rwa [chart_height G p]
  have hz := differential_zero_of_eventually_zero _ _ _ (cutoff_eventually_zero v η _ hx)
  exact hp (by simp [rawCutoffGradientSq, hz])

namespace CutoffAffine

 def linear (d : ℕ) (a : Fin d → ℂ) : Space d →L[ℝ] Space d :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => WithLp.toLp 2 (fun j =>
      ![(a j.1).re * x (j.1,0) - (a j.1).im * x (j.1,1),
        (a j.1).im * x (j.1,0) + (a j.1).re * x (j.1,1), x (j.1,2)] j.2)
    map_add' := by
      intro x y
      ext ⟨i,k⟩
      fin_cases k <;> simp <;> ring
    map_smul' := by
      intro r x
      ext ⟨i,k⟩
      fin_cases k <;> simp <;> ring }
 def translation (d : ℕ) (a b : Fin d → ℂ) : Space d :=
  WithLp.toLp 2 (fun j => ![(b j.1).re, (b j.1).im, Real.log ‖a j.1‖] j.2)
 def affine (d : ℕ) (a b : Fin d → ℂ) (x : Space d) : Space d :=
  linear d a x + translation d a b
private theorem affine_deriv (d : ℕ) (a b : Fin d → ℂ) (x : Space d) :
    HasFDerivAt (affine d a b) (linear d a) x := by
  change HasFDerivAt (fun x => linear d a x + translation d a b) (linear d a) x
  exact (linear d a).hasFDerivAt.add_const (translation d a b)
private theorem linear_basis (d : ℕ) (a : Fin d → ℂ) (i : Fin d) :
    linear d a (coordinateVector d i 0) =
      (a i).re • coordinateVector d i 0 + (a i).im • coordinateVector d i 1 := by
  ext ⟨j,k⟩
  fin_cases k <;> simp [linear, coordinateVector] <;> split_ifs <;> simp_all
private theorem linear_basis1 (d : ℕ) (a : Fin d → ℂ) (i : Fin d) :
    linear d a (coordinateVector d i 1) =
      -(a i).im • coordinateVector d i 0 + (a i).re • coordinateVector d i 1 := by
  ext ⟨j,k⟩
  fin_cases k <;> simp [linear, coordinateVector] <;> split_ifs <;> simp_all
private theorem linear_basis2 (d : ℕ) (a : Fin d → ℂ) (i : Fin d) :
    linear d a (coordinateVector d i 2) = coordinateVector d i 2 := by
  ext ⟨j,k⟩
  fin_cases k <;> simp [linear, coordinateVector]
private theorem norm_rotation (r s : ℝ) (u w : ℂ) :
    ‖(r : ℂ) * u + (s : ℂ) * w‖ ^ 2 +
      ‖-(s : ℂ) * u + (r : ℂ) * w‖ ^ 2 =
      (r ^ 2 + s ^ 2) * (‖u‖ ^ 2 + ‖w‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
  ring
private theorem gradient_affine (d : ℕ) (a b : Fin d → ℂ) (ha : ∀ i, a i ≠ 0)
    (f : Space d → ℂ) (x : Space d) (c : ℂ) (hc : ‖c‖ = 1)
    (hf : DifferentiableAt ℝ f x) (hfa : DifferentiableAt ℝ f (affine d a b x))
    (he : (fun y => f (affine d a b y)) =ᶠ[nhds x] (fun y => c * f y)) :
    (∑ i, ∑ k, ‖differential d f (affine d a b x) i k‖ ^ 2) =
      ∑ i, ∑ k, ‖differential d f x i k‖ ^ 2 := by
  have hd := he.fderiv_eq (𝕜 := ℝ)
  have hleft := (hfa.hasFDerivAt.comp x (affine_deriv d a b x)).fderiv
  have hright := (hf.hasFDerivAt.const_mul c).fderiv
  change fderiv ℝ (f ∘ affine d a b) x = _ at hd
  rw [hleft, hright] at hd
  apply Finset.sum_congr rfl
  intro i hi
  have h0 := congrArg (fun L : Space d →L[ℝ] ℂ => L (coordinateVector d i 0)) hd
  have h1 := congrArg (fun L : Space d →L[ℝ] ℂ => L (coordinateVector d i 1)) hd
  have h2 := congrArg (fun L : Space d →L[ℝ] ℂ => L (coordinateVector d i 2)) hd
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply, linear_basis, linear_basis1, linear_basis2,
    map_add, map_smul, smul_eq_mul] at h0 h1 h2
  have hz : (affine d a b x) (i,2) = x (i,2) + Real.log ‖a i‖ := rfl
  have hn : (a i).re ^ 2 + (a i).im ^ 2 = ‖a i‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hrot := norm_rotation (a i).re (a i).im
    (coordinateDerivative d i 0 f (affine d a b x))
    (coordinateDerivative d i 1 f (affine d a b x))
  simp only [coordinateDerivative] at hrot
  simp only [Complex.real_smul, Complex.ofReal_neg] at h0 h1
  rw [h0, h1, norm_mul, norm_mul, hc, one_mul, one_mul] at hrot
  simp only [Fin.sum_univ_three, differential, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val, Fin.reduceFinMk,
    Matrix.head_cons, Matrix.tail_cons, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hz,
    Real.exp_add, Real.exp_log (norm_pos_iff.mpr (ha i))]
  simp only [coordinateDerivative, abs_norm]
  rw [h2, norm_mul, hc, one_mul]
  rw [hn] at hrot
  nlinarith [congrArg (fun t : ℝ => Real.exp (x (i,2)) ^ 2 * t) hrot]
variable {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
private theorem affine_chart (u : D.E) (v : F) (p : KPCuspCharts.Coordinates F) :
    arch (KPCuspLogShape.dimension F)
      (affine (KPCuspLogShape.dimension F) (KPCuspCharts.embedding F (u : Fˣ))
        (KPCuspCharts.embedding F v)
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))) =
      KPCuspCharts.toArch F (KPCuspCharts.affine F hF D.E D.integralUnits u v p) := by
  funext i
  apply Prod.ext
  · apply Complex.ext <;> simp [arch, affine, linear, translation, real, KPCuspCharts.toArch,
      KPCuspCharts.affine, Complex.mul_re, Complex.mul_im] <;> ring
  · change p.2 + (p.1.2 : Fin _ → ℝ) i + Real.log ‖KPCuspCharts.embedding F (u : Fˣ) i‖ = _
    rw [show ‖KPCuspCharts.embedding F (u : Fˣ) i‖ =
      (KPCusp.complexPlace F i) (u : Fˣ) from NumberField.InfinitePlace.norm_embedding_eq _ _]
    change p.2 + (p.1.2 : Fin _ → ℝ) i + Real.log ((KPCusp.complexPlace F i) (u : Fˣ)) =
      p.2 + ((p.1.2 : Fin _ → ℝ) i + Real.log ((KPCusp.complexPlace F i) (u : Fˣ)))
    ring
private theorem real_arch (d : ℕ) (x : Space d) : real d (arch d x) = x := by
  ext ⟨i,k⟩
  fin_cases k <;> simp [real, arch]
private theorem action_affine (G : KPCuspCharts.ChartOutput F hF S D) (g : S)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F)) (hc : A 1 0 = 0)
    (x : Space (KPCuspLogShape.dimension F)) :
    KPCuspSiegel.action F (g : KPCuspArithmetic.PGL2 F) (arch _ x) =
      arch _ (affine _ (KPCuspCharts.embedding F (D.ratio g : Fˣ))
        (KPCuspCharts.embedding F (A 0 1 / A 1 1)) x) := by
  obtain ⟨p,hp⟩ := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).surjective (arch _ x)
  change KPCuspCharts.toArch F p = arch _ x at hp
  have hr : real _ (KPCuspCharts.toArch F p) = x := by rw [hp, real_arch]
  rw [← hp, G.actual_action g A hA hc p, ← affine_chart (D.ratio g) (A 0 1 / A 1 1) p, hr]
private theorem height_affine (G : KPCuspCharts.ChartOutput F hF S D) (u : D.E)
    (v : F) (x : Space (KPCuspLogShape.dimension F)) :
    KPCuspLogShape.meanHeight _
      (arch _ (affine _ (KPCuspCharts.embedding F (u : Fˣ)) (KPCuspCharts.embedding F v) x)) =
      KPCuspLogShape.meanHeight _ (arch _ x) := by
  obtain ⟨p,hp⟩ := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).surjective (arch _ x)
  change KPCuspCharts.toArch F p = arch _ x at hp
  have hr : real _ (KPCuspCharts.toArch F p) = x := by rw [hp, real_arch]
  rw [← hr, affine_chart (hF := hF),
    show arch _ (real _ (KPCuspCharts.toArch F p)) = KPCuspCharts.toArch F p by rw [hp, real_arch],
    KPCuspCharts.toArch_meanHeight F G.positive_dimension,
    KPCuspCharts.toArch_meanHeight F G.positive_dimension]
  rfl
end CutoffAffine

theorem cutoffGradientSq_geometry
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ContinuousOn (rawCutoffGradientSq v η) {p | T < p.2} ∧
      Function.support (rawCutoffGradientSq v η) ⊆ {p | p.2 ∈ tsupport η} ∧
      ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
        KPCuspCharts.highRelation F S T p q →
          rawCutoffGradientSq v η p.val = rawCutoffGradientSq v η q.val := by
  refine ⟨cutoffGradientSq_continuousOn G v η hη, cutoffGradientSq_support G v η, ?_⟩
  intro p q hrel
  obtain ⟨s, hs⟩ := hrel
  obtain ⟨A, hA, hc⟩ := D.upper s s.property
  let d := KPCuspLogShape.dimension F
  let a := KPCuspCharts.embedding F (D.ratio s : Fˣ)
  let b := KPCuspCharts.embedding F (A 0 1 / A 1 1)
  let x := real d (KPCuspCharts.toArch F q.val)
  let c : ℂ := KPCuspGenuineMonodromy.chi F ζ hζ (ρ s)
  have hx : T < KPCuspLogShape.meanHeight d (arch d x) := by
    change T < KPCuspLogShape.meanHeight _ (arch _ (real _ (KPCuspCharts.toArch F q.val)))
    rw [chart_height G q.val]
    exact q.property
  have hp : CutoffAffine.affine d a b x = real d (KPCuspCharts.toArch F p.val) := by
    have he := CutoffAffine.action_affine G s A hA hc x
    have harch : arch d x = KPCuspCharts.toArch F q.val := arch_real _ _
    rw [harch] at he
    change KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F)
      (KPCuspCharts.toArch F q.val) = KPCuspCharts.toArch F p.val at hs
    have h := congrArg (real d) (he.symm.trans hs)
    change real d (arch d (CutoffAffine.affine d a b x)) = _ at h
    simpa only [CutoffAffine.real_arch] using h
  have ha : ∀ i, a i ≠ 0 := by
    intro i
    exact (map_ne_zero (KPCusp.complexPlace F i).embedding).mpr (Units.ne_zero _)
  have hunit : ‖c‖ = 1 := by
    apply IsOfFinOrder.norm_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨3, by decide, ?_⟩
    have hr : (ρ s) ^ 3 = 1 := by
      apply Subtype.ext
      exact (mem_rootsOfUnity 3 _).mp (ρ s).property
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun e => (KPCuspGenuineMonodromy.chi F ζ hζ e : ℂ)) hr
  have hf := (cutoff_smoothAt v η hη x hx).differentiableAt (by simp)
  have hfa : DifferentiableAt ℝ (rawCutoffUpstairs v η) (CutoffAffine.affine d a b x) := by
    rw [hp]
    exact (cutoff_smoothAt v η hη _ (by rw [chart_height G p.val]; exact p.property)).differentiableAt (by simp)
  have he : (fun y => rawCutoffUpstairs v η (CutoffAffine.affine d a b y)) =ᶠ[nhds x]
      (fun y => c * rawCutoffUpstairs v η y) := by
    have hopen : IsOpen {y : Space d | T < KPCuspLogShape.meanHeight d (arch d y)} :=
      isOpen_lt continuous_const (((smooth_mean _).comp (smooth_arch _)).continuous)
    filter_upwards [hopen.mem_nhds hx] with y hy
    have hheight := CutoffAffine.height_affine G (D.ratio s) (A 0 1 / A 1 1) y
    have haction := CutoffAffine.action_affine G s A hA hc y
    dsimp only [rawCutoffUpstairs]
    change (η (KPCuspLogShape.meanHeight d (arch d (CutoffAffine.affine d a b y))) : ℂ) *
      v.val (arch d (CutoffAffine.affine d a b y)) =
        c * ((η (KPCuspLogShape.meanHeight d (arch d y)) : ℂ) * v.val (arch d y))
    rw [hheight, ← haction, v.equivariant s (arch d y) hy]
    ring
  have hh := CutoffAffine.gradient_affine d a b ha (rawCutoffUpstairs v η) x c hunit hf hfa he
  rw [hp] at hh
  exact hh

end DedekindZetaZeroFree.KPCompactGreenRadialIntegrability

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPCompactGreen
open KPMeanZeroWeightedEnergy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ} {T : ℝ}

def cutoffUpstairs (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (x : HyperbolicChart.Space (KPCuspLogShape.dimension F)) : ℂ :=
  (η (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
    (arch (KPCuspLogShape.dimension F) x)) : ℂ) *
      v.val (arch (KPCuspLogShape.dimension F) x)

def cutoffGradientSq (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (p : KPCuspCharts.Coordinates F) : ℝ :=
  let w := HyperbolicChart.differential (KPCuspLogShape.dimension F)
    (cutoffUpstairs v η)
    (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))
  ∑ i, ∑ k, ‖w i k‖ ^ 2

def weightedGreenDensity (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (p : KPCuspCharts.Coordinates F) : ℝ :=
  let x := real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p)
  (HyperbolicChart.pairing (KPCuspLogShape.dimension F)
    (HyperbolicChart.differential (KPCuspLogShape.dimension F)
      (cutoffUpstairs v (fun t => η t ^ 2)) x)
    (HyperbolicChart.differential (KPCuspLogShape.dimension F)
      (v.val ∘ arch (KPCuspLogShape.dimension F)) x)).re

theorem radialMeasure_locallyFinite (d : ℕ) : IsLocallyFiniteMeasure (KPCuspCharts.radialMeasure d) := by
  apply IsLocallyFiniteMeasure.withDensity_ofReal
  fun_prop

theorem fundamentalDomain_finiteMeasure (G : KPCuspCharts.ChartOutput F hF S D) :
    IsFiniteMeasure ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain) := by
  letI := G.finite_sectionMeasure
  constructor
  have h := measure_lt_top G.sectionMeasure Set.univ
  rw [G.sectionMeasure_formula,
    Measure.map_apply measurable_quotient_mk'' MeasurableSet.univ] at h
  simpa using h

theorem compact_radial_slab_finiteMeasure (G : KPCuspCharts.ChartOutput F hF S D)
    {K : Set ℝ} (hK : IsCompact K) :
    IsFiniteMeasure ((chartMeasure G).restrict {p | p.2 ∈ K}) := by
  letI := G.haar_shapeMeasure
  letI := radialMeasure_locallyFinite (KPCuspLogShape.dimension F)
  letI := fundamentalDomain_finiteMeasure G
  have hrad : IsFiniteMeasure ((KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)).restrict K) :=
    ⟨by simpa using hK.measure_lt_top (μ := KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))⟩
  letI := hrad
  have hm : ((chartMeasure G).restrict {p | p.2 ∈ K}) =
      ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain).prod
        ((KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)).restrict K) := by
    rw [chartMeasure, Measure.restrict_restrict
      (show MeasurableSet {p : KPCuspCharts.Coordinates F | p.2 ∈ K} from
        measurable_snd hK.measurableSet), Measure.prod_restrict]
    congr 1
    ext p
    simp [and_comm]
  rw [hm]
  infer_instance

theorem integrable_of_radial_bound (G : KPCuspCharts.ChartOutput F hF S D)
    {E : Type*} [NormedAddCommGroup E]
    {K : Set ℝ} (hK : IsCompact K) {f : KPCuspCharts.Coordinates F → E}
    (hf : AEStronglyMeasurable f (chartMeasure G))
    (hsupport : Function.support f ⊆ {p | p.2 ∈ K})
    (C : ℝ) (hbound : ∀ p : KPCuspCharts.Coordinates F, p.2 ∈ K → ‖f p‖ ≤ C) :
    Integrable f (chartMeasure G) := by
  apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
  letI := compact_radial_slab_finiteMeasure G hK
  refine ⟨hf.restrict, HasFiniteIntegral.of_bounded (C := C) ?_⟩
  filter_upwards [ae_restrict_mem (measurable_snd hK.measurableSet)] with p hp
  exact hbound p hp

theorem integrable_of_radial_descent (G : KPCuspCharts.ChartOutput F hF S D)
    {E : Type*} [NormedAddCommGroup E]
    {K : Set ℝ} (hK : IsCompact K) {f : KPCuspCharts.Coordinates F → E}
    (hf : AEStronglyMeasurable f (chartMeasure G))
    (hsupport : Function.support f ⊆ {p | p.2 ∈ K})
    (d : KPCuspCharts.CrossQuotient F S × ℝ → E)
    (hd : ContinuousOn d (Set.univ ×ˢ K))
    (heq : ∀ p : KPCuspCharts.Coordinates F, p.2 ∈ K →
      f p = d (Quotient.mk _ p.1, p.2)) :
    Integrable f (chartMeasure G) := by
  letI := G.compact_cross
  obtain ⟨C, hC⟩ := (isCompact_univ.prod hK).exists_bound_of_continuousOn hd
  apply integrable_of_radial_bound G hK hf hsupport C
  intro p hp
  rw [heq p hp]
  exact hC _ ⟨Set.mem_univ _, hp⟩

theorem integrable_of_continuous_radial_descent (G : KPCuspCharts.ChartOutput F hF S D)
    {K : Set ℝ} (hK : IsCompact K) {f : KPCuspCharts.Coordinates F → ℝ}
    (hf : Continuous f)
    (hsupport : Function.support f ⊆ {p | p.2 ∈ K})
    (d : KPCuspCharts.CrossQuotient F S × ℝ → ℝ)
    (hd : ContinuousOn d (Set.univ ×ˢ K))
    (heq : ∀ p : KPCuspCharts.Coordinates F, p.2 ∈ K →
      f p = d (Quotient.mk _ p.1, p.2)) :
    Integrable f (chartMeasure G) := by
  exact integrable_of_radial_descent G hK hf.aestronglyMeasurable hsupport d hd heq

theorem integrable_of_high_orbit_invariant
    (G : KPCuspCharts.ChartOutput F hF S D)
    {E : Type*} [NormedAddCommGroup E]
    {T : ℝ} {K : Set ℝ} (hK : IsCompact K) (hKT : K ⊆ Set.Ioi T)
    {f : KPCuspCharts.Coordinates F → E}
    (hf : AEStronglyMeasurable f (chartMeasure G))
    (hcont : ContinuousOn f {p | T < p.2})
    (hsupport : Function.support f ⊆ {p | p.2 ∈ K})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q → f p.val = f q.val) :
    Integrable f (chartMeasure G) := by
  let d : KPCuspCharts.HighQuotient F S T → E :=
    Quotient.lift (fun p => f p.val) hinv
  have hd : Continuous d := by
    apply Continuous.quotient_lift
    exact hcont.restrict
  let j : K → Set.Ioi T := fun t => ⟨t.val, hKT t.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let g : KPCuspCharts.CrossQuotient F S × K → E :=
    fun p => d (G.highPresentation T (p.1, j p.2))
  have hg : Continuous g := hd.comp ((G.highPresentation T).continuous.comp
    (continuous_fst.prodMk (hj.comp continuous_snd)))
  letI := G.compact_cross
  letI := isCompact_iff_compactSpace.mp hK
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  apply integrable_of_radial_bound G hK hf hsupport C
  intro p hp
  have hx := hC (Quotient.mk _ p.1, ⟨p.2, hp⟩) (Set.mem_univ _)
  simpa [g, j, G.highPresentation_formula, d] using hx

theorem continuous_of_high_radial_support
    {E : Type*} [NormedAddCommGroup E]
    {T : ℝ} {K : Set ℝ} (hK : IsClosed K) (hKT : K ⊆ Set.Ioi T)
    {f : KPCuspCharts.Coordinates F → E}
    (hcont : ContinuousOn f {p | T < p.2})
    (hsupport : Function.support f ⊆ {p | p.2 ∈ K}) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : T < p.2
  · exact hcont.continuousAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  · have hpK : p ∉ {p : KPCuspCharts.Coordinates F | p.2 ∈ K} :=
      fun h => hp (hKT h)
    have hn : {p : KPCuspCharts.Coordinates F | p.2 ∉ K} ∈ nhds p :=
      ((hK.preimage continuous_snd).isOpen_compl).mem_nhds hpK
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    have hzero : f q = 0 := by
      by_contra hh
      exact hq (hsupport hh)
    exact hzero

theorem integrable_of_continuous_high_orbit_invariant
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} {K : Set ℝ} (hK : IsCompact K) (hKT : K ⊆ Set.Ioi T)
    {f : KPCuspCharts.Coordinates F → ℝ}
    (hcont : ContinuousOn f {p | T < p.2})
    (hsupport : Function.support f ⊆ {p | p.2 ∈ K})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q → f p.val = f q.val) :
    Integrable f (chartMeasure G) := by
  apply integrable_of_high_orbit_invariant G hK hKT
    (continuous_of_high_radial_support hK.isClosed hKT hcont hsupport).aestronglyMeasurable
    hcont hsupport hinv

private theorem character_norm (ε : rootsOfUnity 3 F) :
    ‖(KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)‖ = 1 := by
  apply IsOfFinOrder.norm_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨3, by decide, ?_⟩
  have hp : ε ^ 3 = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity 3 _).mp ε.property
  simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
    congrArg (fun x => (KPCuspGenuineMonodromy.chi F ζ hζ x : ℂ)) hp

theorem scalar_continuousOn (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) :
    ContinuousOn v.scalar {p | T < p.2} := by
  apply v.smooth.continuousOn.comp (KPCuspCharts.toArch_contDiff F).continuous.continuousOn
  intro p hp
  change T < KPCuspLogShape.meanHeight _ (KPCuspCharts.toArch F p)
  rwa [KPCuspCharts.toArch_meanHeight F G.positive_dimension]

theorem highRelation_radial_eq (G : KPCuspCharts.ChartOutput F hF S D)
    {p q : {p : KPCuspCharts.Coordinates F // T < p.2}}
    (hrel : KPCuspCharts.highRelation F S T p q) : p.val.2 = q.val.2 := by
  have h : (G.highPresentation T) (Quotient.mk _ p.val.1, ⟨p.val.2, p.property⟩) =
      (G.highPresentation T) (Quotient.mk _ q.val.1, ⟨q.val.2, q.property⟩) := by
    rw [G.highPresentation_formula, G.highPresentation_formula]
    exact Quotient.sound hrel
  exact congrArg (fun x => (x.2 : ℝ)) ((G.highPresentation T).injective h)

theorem scalar_norm_high_orbit_invariant (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T)
    {p q : {p : KPCuspCharts.Coordinates F // T < p.2}}
    (hrel : KPCuspCharts.highRelation F S T p q) : ‖v.scalar p.val‖ = ‖v.scalar q.val‖ := by
  change MulAction.orbitRel S (KPArch.Space _) (KPCuspCharts.toArch F p.val)
    (KPCuspCharts.toArch F q.val) at hrel
  obtain ⟨s, hs⟩ := hrel
  change KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) (KPCuspCharts.toArch F q.val) =
    KPCuspCharts.toArch F p.val at hs
  have heq := v.equivariant s (KPCuspCharts.toArch F q.val) (by
    rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
    exact q.property)
  rw [hs] at heq
  simpa only [Representative.scalar, norm_mul, character_norm, one_mul] using congrArg norm heq

theorem compact_scalar_density_integrable
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T)
    {K : Set ℝ} (hK : IsCompact K) (hKT : K ⊆ Set.Ioi T)
    (a : ℝ → ℝ) (ha : Continuous a) (hs : Function.support a ⊆ K) :
    Integrable (fun p => a p.2 * ‖v.scalar p‖ ^ 2) (chartMeasure G) := by
  apply integrable_of_continuous_high_orbit_invariant G hK hKT
  · exact (ha.comp continuous_snd).continuousOn.mul ((scalar_continuousOn G v).norm.pow 2)
  · intro p hp
    apply hs
    intro hzero
    exact hp (by simp [hzero])
  · intro p q hrel
    rw [highRelation_radial_eq G hrel, scalar_norm_high_orbit_invariant G v hrel]

theorem compact_radial_scalar_densities_integrable
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : CompactRadialTest T η) :
    Integrable (fun p => deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2) (chartMeasure G) ∧
    Integrable (fun p => Real.exp (2 * p.2) * η p.2 ^ 2 * ‖v.scalar p‖ ^ 2)
      (chartMeasure G) := by
  constructor
  · apply compact_scalar_density_integrable G v hη.2.1 hη.2.2
      (fun t => deriv η t ^ 2) ((hη.1.continuous_deriv (by simp)).pow 2)
    intro t ht
    apply support_deriv_subset
    intro hz
    exact ht (by simp [hz])
  · apply compact_scalar_density_integrable G v hη.2.1 hη.2.2
      (fun t => Real.exp (2 * t) * η t ^ 2)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (hη.1.continuous.pow 2))
    intro t ht
    apply subset_tsupport η
    intro hz
    exact ht (by simp [hz])
namespace DensityContinuity
open HyperbolicChart

private theorem smooth_arch (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (arch d) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.prodMk
  · exact Complex.equivRealProdCLM.symm.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (0 : Fin 3))).contDiff.prodMk
       (EuclideanSpace.proj (𝕜 := ℝ) (i, (1 : Fin 3))).contDiff)
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff
private theorem smooth_real (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (real d) := by
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  rintro ⟨i,k⟩
  fin_cases k <;> simp only [real, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Complex.reCLM.contDiff.comp (contDiff_fst.comp (contDiff_apply ℝ _ i))
  · exact Complex.imCLM.contDiff.comp (contDiff_fst.comp (contDiff_apply ℝ _ i))
  · exact contDiff_snd.comp (contDiff_apply ℝ _ i)
private theorem continuous_height (d : ℕ) : Continuous (KPCuspLogShape.meanHeight d) := by
  unfold KPCuspLogShape.meanHeight
  exact (continuous_finset_sum _ (fun i _ => (continuous_apply i).snd)).div_const _
private theorem derivative_smoothAt (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coordinateDerivative d i k g) x :=
  (hg.fderiv_right (by simp)).clm_apply contDiffAt_const
private theorem differential_smoothAt (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => differential d g q i k) x := by
  have he : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Space d => (Real.exp (q (i, 2)) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.contDiffAt.exp)
  fin_cases k
  · simpa [differential] using derivative_smoothAt d g x hg i 2
  · simpa [differential] using he.mul (derivative_smoothAt d g x hg i 0)
  · simpa [differential] using he.mul (derivative_smoothAt d g x hg i 1)
private theorem laplacian_smoothAt (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (laplacian d g) x := by
  unfold laplacian
  apply ContDiffAt.sum
  intro i hi
  have h (k : Fin 3) := derivative_smoothAt d g x hg i k
  have hh (k : Fin 3) := derivative_smoothAt d _ x (h k) i k
  have he : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Space d => (Real.exp (2 * q (i, 2)) : ℂ)) x := by
    apply Complex.ofRealCLM.contDiff.contDiffAt.comp
    exact (contDiffAt_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.contDiffAt).exp
  exact ((hh 2).neg.add (contDiffAt_const.mul (h 2))).sub (he.mul ((hh 0).add (hh 1)))
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ} {T : ℝ}
private theorem representative_smoothAt (v : Representative ζ hζ S ρ V T)
    (x : Space (KPCuspLogShape.dimension F))
    (hx : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (v.val ∘ arch (KPCuspLogShape.dimension F)) x := by
  have hopen : IsOpen {z : KPArch.Space (KPCuspLogShape.dimension F) |
      T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z} :=
    isOpen_lt continuous_const (continuous_height _)
  exact (v.smooth.contDiffAt (hopen.mem_nhds hx)).comp x (smooth_arch _).contDiffAt
private theorem arch_real (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  ext i <;> simp [arch, real]
theorem gradientSq_continuousOn_high (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) :
    ContinuousOn v.gradientSq {p : KPCuspCharts.Coordinates F | T < p.2} := by
  intro p hp
  have hv := representative_smoothAt v (real _ (KPCuspCharts.toArch F p)) (by
    rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
    exact hp)
  apply ContinuousAt.continuousWithinAt
  apply tendsto_finset_sum
  intro i hi
  apply tendsto_finset_sum
  intro k hk
  have hc := ((differential_smoothAt _ _ _ hv i k).continuousAt.comp
    (smooth_real _).continuous.continuousAt).comp (KPCuspCharts.toArch_contDiff F).continuous.continuousAt
  exact hc.norm.pow 2
theorem laplacian_continuousOn_high (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) :
    ContinuousOn v.laplacian {p : KPCuspCharts.Coordinates F | T < p.2} := by
  intro p hp
  have hv := representative_smoothAt v (real _ (KPCuspCharts.toArch F p)) (by
    rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
    exact hp)
  have hc := ((laplacian_smoothAt _ _ _ hv).continuousAt.comp
    (smooth_real _).continuous.continuousAt).comp (KPCuspCharts.toArch_contDiff F).continuous.continuousAt
  exact hc.continuousWithinAt
private theorem smooth_height (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞)
    (fun x : Space d => KPCuspLogShape.meanHeight d (arch d x)) := by
  unfold KPCuspLogShape.meanHeight arch
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i hi
  exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff
private theorem cutoff_smoothAt (v : Representative ζ hζ S ρ V T)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (x : Space (KPCuspLogShape.dimension F))
    (hx : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (cutoffUpstairs v η) x := by
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
    (hη.contDiffAt.comp x (smooth_height _).contDiffAt)).mul
    (representative_smoothAt v x hx)
theorem cutoffGradientSq_continuousOn_high (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ContinuousOn (cutoffGradientSq v η) {p : KPCuspCharts.Coordinates F | T < p.2} := by
  intro p hp
  have hv := cutoff_smoothAt v η hη (real _ (KPCuspCharts.toArch F p)) (by
    rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
    exact hp)
  apply ContinuousAt.continuousWithinAt
  apply tendsto_finset_sum
  intro i hi
  apply tendsto_finset_sum
  intro k hk
  have hc := ((differential_smoothAt _ _ _ hv i k).continuousAt.comp
    (smooth_real _).continuous.continuousAt).comp (KPCuspCharts.toArch_contDiff F).continuous.continuousAt
  exact hc.norm.pow 2
theorem weightedGreenDensity_continuousOn_high (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ContinuousOn (weightedGreenDensity v η) {p : KPCuspCharts.Coordinates F | T < p.2} := by
  intro p hp
  have hx : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch _ (real _ (KPCuspCharts.toArch F p))) := by
    rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
    exact hp
  have hv := representative_smoothAt v _ hx
  have hcut := cutoff_smoothAt v (fun t => η t ^ 2) (hη.pow 2) _ hx
  apply ContinuousAt.continuousWithinAt
  apply Complex.continuous_re.continuousAt.comp
  unfold pairing
  apply tendsto_finset_sum
  intro i hi
  apply tendsto_finset_sum
  intro k hk
  have hc := ((differential_smoothAt _ _ _ hcut i k).continuousAt.comp
    (smooth_real _).continuous.continuousAt).comp (KPCuspCharts.toArch_contDiff F).continuous.continuousAt
  have hv' := ((differential_smoothAt _ _ _ hv i k).continuousAt.comp
    (smooth_real _).continuous.continuousAt).comp (KPCuspCharts.toArch_contDiff F).continuous.continuousAt
  exact hc.star.mul hv'

private theorem cutoff_eventually_zero (v : Representative ζ hζ S ρ V T)
    (η : ℝ → ℝ) (x : Space (KPCuspLogShape.dimension F))
    (hx : KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x) ∉ tsupport η) :
    cutoffUpstairs v η =ᶠ[nhds x] 0 := by
  have hh := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto
    (smooth_height _).continuous.continuousAt
  filter_upwards [hh] with q hq
  change η (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
    (arch (KPCuspLogShape.dimension F) q)) = 0 at hq
  simp [cutoffUpstairs, hq]
private theorem cutoff_differential_zero (v : Representative ζ hζ S ρ V T)
    (η : ℝ → ℝ) (x : Space (KPCuspLogShape.dimension F))
    (hx : KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x) ∉ tsupport η) :
    differential (KPCuspLogShape.dimension F) (cutoffUpstairs v η) x = 0 := by
  have hh := (cutoff_eventually_zero v η x hx).fderiv_eq (𝕜 := ℝ)
  have hz : fderiv ℝ (0 : Space (KPCuspLogShape.dimension F) → ℂ) x = 0 := congrFun fderiv_zero x
  rw [hz] at hh
  funext i k
  fin_cases k <;> simp [differential, coordinateDerivative, hh]
theorem cutoffGradientSq_support_radial (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ) :
    Function.support (cutoffGradientSq v η) ⊆ {p : KPCuspCharts.Coordinates F | p.2 ∈ tsupport η} := by
  intro p hp
  by_contra hh
  have hx : KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch _ (real _ (KPCuspCharts.toArch F p))) ∉ tsupport η := by
    simpa only [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension, Set.mem_setOf_eq] using hh
  exact hp (by simp [cutoffGradientSq, cutoff_differential_zero v η _ hx])
theorem weightedGreenDensity_support_radial (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ) :
    Function.support (weightedGreenDensity v η) ⊆ {p : KPCuspCharts.Coordinates F | p.2 ∈ tsupport η} := by
  intro p hp
  by_contra hh
  have hx : KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch _ (real _ (KPCuspCharts.toArch F p))) ∉ tsupport (fun t => η t ^ 2) := by
    intro hmem
    apply hh
    have hh' := tsupport_comp_subset (g := fun x : ℝ => x ^ 2) (by simp) η hmem
    simpa only [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension, Set.mem_setOf_eq] using hh'
  exact hp (by simp [weightedGreenDensity, cutoff_differential_zero v (fun t => η t ^ 2) _ hx, pairing])
theorem weighted_gradient_support_radial (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ) :
    Function.support (fun p : KPCuspCharts.Coordinates F => η p.2 ^ 2 * v.gradientSq p) ⊆
      {p : KPCuspCharts.Coordinates F | p.2 ∈ tsupport η} := by
  intro p hp
  apply subset_tsupport η
  intro hz
  exact hp (by simp [hz])
theorem weighted_laplacian_support_radial (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ) :
    Function.support (fun p : KPCuspCharts.Coordinates F => η p.2 ^ 2 * (star (v.scalar p) * v.laplacian p).re) ⊆
      {p : KPCuspCharts.Coordinates F | p.2 ∈ tsupport η} := by
  intro p hp
  apply subset_tsupport η
  intro hz
  exact hp (by simp [hz])

end DensityContinuity

theorem compact_radial_densities_integrable
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : CompactRadialTest T η) :
    Integrable (fun p => η p.2 ^ 2 * v.gradientSq p) (chartMeasure G) ∧
    Integrable (fun p => deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2) (chartMeasure G) ∧
    Integrable (fun p => Real.exp (2 * p.2) * η p.2 ^ 2 * ‖v.scalar p‖ ^ 2)
      (chartMeasure G) ∧
    Integrable (fun p => η p.2 ^ 2 * (star (v.scalar p) * v.laplacian p).re)
      (chartMeasure G) ∧
    Integrable (cutoffGradientSq v η) (chartMeasure G) ∧
    Integrable (weightedGreenDensity v η) (chartMeasure G) := by
  obtain ⟨hscalar, hpotential⟩ := compact_radial_scalar_densities_integrable G v η hη
  obtain ⟨hgradCont, hgradInv⟩ :=
    KPCompactGreenRadialIntegrability.gradientSq_continuousOn_and_invariant G v
  obtain ⟨hlapCont, hlapInv⟩ :=
    KPCompactGreenRadialIntegrability.scalar_laplacian_continuousOn_and_invariant G v
  obtain ⟨hcutCont, hcutSupport, hcutInv⟩ :=
    KPCompactGreenRadialIntegrability.cutoffGradientSq_geometry G v η hη.1
  obtain ⟨hgreenCont, hgreenSupport, hgreenInv⟩ :=
    KPCompactGreenRadialIntegrability.weightedGreenDensity_geometry G v η hη.1
  refine ⟨?_, hscalar, hpotential, ?_, ?_, ?_⟩
  · apply integrable_of_continuous_high_orbit_invariant G hη.2.1 hη.2.2
    · exact ((hη.1.continuous.comp continuous_snd).pow 2).continuousOn.mul hgradCont
    · intro p hp
      apply subset_tsupport η
      intro hz
      exact hp (by simp [hz])
    · intro p q hrel
      rw [highRelation_radial_eq G hrel, hgradInv p q hrel]
  · apply integrable_of_continuous_high_orbit_invariant G hη.2.1 hη.2.2
    · exact ((hη.1.continuous.comp continuous_snd).pow 2).continuousOn.mul hlapCont
    · intro p hp
      apply subset_tsupport η
      intro hz
      exact hp (by simp [hz])
    · intro p q hrel
      rw [highRelation_radial_eq G hrel, hlapInv p q hrel]
  · exact integrable_of_continuous_high_orbit_invariant G hη.2.1 hη.2.2
      hcutCont hcutSupport hcutInv
  · exact integrable_of_continuous_high_orbit_invariant G hη.2.1 hη.2.2
      hgreenCont hgreenSupport hgreenInv

end DedekindZetaZeroFree.KPCompactGreen

end

end

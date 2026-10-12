module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.GreenPairing

@[expose] public section

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

theorem rawWeightedGreenDensity_continuousOn (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ContinuousOn (rawWeightedGreenDensity v η) {p | T < p.2} := by
  apply continuousOn_of_forall_continuousAt
  intro p hp
  have hx : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch _ (real _ (KPCuspCharts.toArch F p))) := by
    rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
    exact hp
  have hv := representative_smoothAt v _ hx
  have hcut := cutoff_smoothAt v (fun t => η t ^ 2) (hη.pow 2) _ hx
  apply Complex.continuous_re.continuousAt.comp
  unfold pairing
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro k hk
  have hc := ((differential_smoothAt _ _ _ hcut i k).continuousAt.comp
    (f := fun p : KPCuspCharts.Coordinates F => real _ (KPCuspCharts.toArch F p))
    chart_smooth.continuous.continuousAt)
  have hv' := ((differential_smoothAt _ _ _ hv i k).continuousAt.comp
    (f := fun p : KPCuspCharts.Coordinates F => real _ (KPCuspCharts.toArch F p))
    chart_smooth.continuous.continuousAt)
  exact hc.star.mul hv'

private theorem cutoff_eventually_zero (v : Representative ζ hζ S ρ V T)
    (η : ℝ → ℝ) (x : Space (KPCuspLogShape.dimension F))
    (hx : KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x) ∉ tsupport η) :
    rawCutoffUpstairs v η =ᶠ[nhds x] 0 := by
  have hh := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto
    (((smooth_mean _).comp (smooth_arch _)).continuous.continuousAt)
  filter_upwards [hh] with q hq
  change η (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
    (arch (KPCuspLogShape.dimension F) q)) = 0 at hq
  simp [rawCutoffUpstairs, hq]

private theorem differential_zero_of_eventually_zero (d : ℕ)
    (f : Space d → ℂ) (x : Space d) (hf : f =ᶠ[nhds x] 0) :
    differential d f x = 0 := by
  have hh := hf.fderiv_eq (𝕜 := ℝ)
  have hz : fderiv ℝ (0 : Space d → ℂ) x = 0 := congrFun fderiv_zero x
  rw [hz] at hh
  funext i k
  fin_cases k <;> simp [differential, coordinateDerivative, hh]

theorem rawWeightedGreenDensity_support (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ) :
    Function.support (rawWeightedGreenDensity v η) ⊆ {p | p.2 ∈ tsupport η} := by
  intro p hp
  by_contra hh
  have hx : KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F)
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))) ∉
        tsupport (fun t => η t ^ 2) := by
    intro hmem
    apply hh
    have hh' := tsupport_comp_subset (g := fun x : ℝ => x ^ 2) (by simp) η hmem
    rwa [chart_height G p] at hh'
  have hz := differential_zero_of_eventually_zero _ _ _ (cutoff_eventually_zero v (fun t => η t ^ 2) _ hx)
  exact hp (by simp [rawWeightedGreenDensity, hz, pairing])

namespace GreenTransport

 def lin (d : ℕ) (a : Fin d → ℂ) : Space d →L[ℝ] Space d :=
  (WithLp.linearEquiv 2 ℝ (Fin d × Fin 3 → ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => ![
      (a j.1).re • EuclideanSpace.proj (j.1,0) - (a j.1).im • EuclideanSpace.proj (j.1,1),
      (a j.1).im • EuclideanSpace.proj (j.1,0) + (a j.1).re • EuclideanSpace.proj (j.1,1),
      EuclideanSpace.proj (j.1,2)] j.2)
private theorem lin_apply (d : ℕ) (a : Fin d → ℂ) (x : Space d) (i : Fin d) :
    arch d (lin d a x) i = (a i * (arch d x i).1, (arch d x i).2) := by
  apply Prod.ext
  · apply Complex.ext <;> simp [arch, lin, Complex.mul_re, Complex.mul_im, add_comm]
  · simp [arch, lin]
private theorem real_arch (d : ℕ) (x : Space d) : real d (arch d x) = x := by
  ext j
  rcases j with ⟨i,k⟩
  fin_cases k <;> simp [real, arch]
 theorem lin_one (d : ℕ) (x : Space d) : lin d (fun _ => 1) x = x := by
  apply (show Function.Injective (arch d) from fun x y h => by rw [← real_arch d x, ← real_arch d y, h])
  funext i
  simp [lin_apply]
 theorem lin_mul (d : ℕ) (a b : Fin d → ℂ) (x : Space d) :
    lin d a (lin d b x) = lin d (fun i => a i * b i) x := by
  apply (show Function.Injective (arch d) from fun x y h => by rw [← real_arch d x, ← real_arch d y, h])
  funext i
  simp [lin_apply, mul_assoc]
 def equiv (d : ℕ) (a : Fin d → ℂ) (ha : ∀ i, a i ≠ 0) : Space d ≃L[ℝ] Space d :=
  ({ (lin d a).toLinearMap with
      invFun := lin d (fun i => (a i)⁻¹)
      left_inv := by
        intro x
        change lin d (fun i => (a i)⁻¹) (lin d a x) = x
        rw [lin_mul]; simpa [ha] using lin_one d x
      right_inv := by
        intro x
        change lin d a (lin d (fun i => (a i)⁻¹) x) = x
        rw [lin_mul]; simpa [ha] using lin_one d x
    } : Space d ≃ₗ[ℝ] Space d).toContinuousLinearEquiv
private theorem lin_vector (d : ℕ) (a : Fin d → ℂ) (i : Fin d) (k : Fin 3) :
    lin d a (coordinateVector d i k) = ![
      (a i).re • coordinateVector d i 0 + (a i).im • coordinateVector d i 1,
      -(a i).im • coordinateVector d i 0 + (a i).re • coordinateVector d i 1,
      coordinateVector d i 2] k := by
  ext j
  rcases j with ⟨j,l⟩
  fin_cases k <;> fin_cases l <;>
    simp [lin, coordinateVector, and_comm] <;>
    split_ifs <;> simp_all
private theorem transform_deriv (d : ℕ) (a : Fin d → ℂ) (ha : ∀ i, a i ≠ 0)
    (b x : Space d) (f : Space d → ℂ) (c : ℂ)
    (he : (fun z => f (lin d a z + b)) =ᶠ[nhds x] (fun z => c * f z)) :
    (fderiv ℝ f (lin d a x + b)).comp (lin d a) = c • fderiv ℝ f x := by
  have h := he.fderiv_eq (𝕜 := ℝ)
  have hL : (fun z => f (lin d a z + b)) = (fun z => f (z + b)) ∘ equiv d a ha := rfl
  rw [hL, (equiv d a ha).comp_right_fderiv, fderiv_comp_add_right] at h
  have hR : (fun z => c * f z) = c • f := rfl
  rw [hR, fderiv_const_smul_field] at h
  exact h
private theorem cd_transform (d : ℕ) (a : Fin d → ℂ) (ha : ∀ i, a i ≠ 0)
    (b x : Space d) (f : Space d → ℂ) (c : ℂ)
    (he : (fun z => f (lin d a z + b)) =ᶠ[nhds x] (fun z => c * f z)) (i : Fin d) :
    ![(a i).re • coordinateDerivative d i 0 f (lin d a x + b) +
       (a i).im • coordinateDerivative d i 1 f (lin d a x + b),
      -(a i).im • coordinateDerivative d i 0 f (lin d a x + b) +
       (a i).re • coordinateDerivative d i 1 f (lin d a x + b),
      coordinateDerivative d i 2 f (lin d a x + b)] =
      fun k => c * coordinateDerivative d i k f x := by
  funext k
  have h := congrArg (fun L : Space d →L[ℝ] ℂ => L (coordinateVector d i k))
    (transform_deriv d a ha b x f c he)
  rw [ContinuousLinearMap.comp_apply, lin_vector] at h
  fin_cases k <;> simpa [coordinateDerivative] using h
private theorem pair_rotation (a u v u' v' : ℂ) :
    star (a.re • u + a.im • v) * (a.re • u' + a.im • v') +
      star (-a.im • u + a.re • v) * (-a.im • u' + a.re • v') =
      (‖a‖ ^ 2 : ℝ) • (star u * u' + star v * v') := by
  simp only [Complex.real_smul, star_add, star_mul, Complex.star_def,
    map_neg, Complex.conj_ofReal, Complex.ofReal_neg]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  push_cast
  ring
private theorem unit_pair (c u v : ℂ) (hc : ‖c‖ = 1) :
    star (c * u) * (c * v) = star u * v := by
  have h : star c * c = 1 := by
    change (starRingEnd ℂ) c * c = 1
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  rw [star_mul]
  calc
    star u * star c * (c * v) = (star c * c) * (star u * v) := by ring
    _ = _ := by rw [h, one_mul]
private theorem pairing_transform (d : ℕ) (a : Fin d → ℂ) (ha : ∀ i, a i ≠ 0)
    (b x : Space d) (hb : ∀ i, b (i,2) = Real.log ‖a i‖)
    (f g : Space d → ℂ) (c : ℂ) (hc : ‖c‖ = 1)
    (hf : (fun z => f (lin d a z + b)) =ᶠ[nhds x] (fun z => c * f z))
    (hg : (fun z => g (lin d a z + b)) =ᶠ[nhds x] (fun z => c * g z)) :
    pairing d (differential d f (lin d a x + b)) (differential d g (lin d a x + b)) =
      pairing d (differential d f x) (differential d g x) := by
  unfold pairing
  apply Finset.sum_congr rfl
  intro i hi
  have hf' := cd_transform d a ha b x f c hf i
  have hg' := cd_transform d a ha b x g c hg i
  have hf0 := congrFun hf' 0
  have hf1 := congrFun hf' 1
  have hf2 := congrFun hf' 2
  have hg0 := congrFun hg' 0
  have hg1 := congrFun hg' 1
  have hg2 := congrFun hg' 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at *
  have hp := pair_rotation (a i)
    (coordinateDerivative d i 0 f (lin d a x + b))
    (coordinateDerivative d i 1 f (lin d a x + b))
    (coordinateDerivative d i 0 g (lin d a x + b))
    (coordinateDerivative d i 1 g (lin d a x + b))
  rw [hf0, hf1, hg0, hg1, unit_pair c _ _ hc, unit_pair c _ _ hc] at hp
  have hheight : (lin d a x + b) (i,2) = x (i,2) + Real.log ‖a i‖ := by
    simp [lin, hb]
  have hexp : Real.exp ((lin d a x + b) (i,2)) = Real.exp (x (i,2)) * ‖a i‖ := by
    rw [hheight, Real.exp_add, Real.exp_log (norm_pos_iff.mpr (ha i))]
  simp only [Fin.sum_univ_three, differential, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [hf2, hg2, unit_pair c _ _ hc, hexp]
  have hp' :
      (‖a i‖ : ℂ) ^ 2 * (star (coordinateDerivative d i 0 f (lin d a x + b)) *
          coordinateDerivative d i 0 g (lin d a x + b) +
        star (coordinateDerivative d i 1 f (lin d a x + b)) *
          coordinateDerivative d i 1 g (lin d a x + b)) =
        star (coordinateDerivative d i 0 f x) * coordinateDerivative d i 0 g x +
        star (coordinateDerivative d i 1 f x) * coordinateDerivative d i 1 g x := by
    simpa [Complex.real_smul, mul_add] using hp.symm
  simp only [Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
  simp only [Complex.star_def] at hp'
  linear_combination (Real.exp (x (i,2)) : ℂ) ^ 2 * hp'
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ} {T : ℝ}
 def shift (s : S) (v : F) : Space (KPCuspLogShape.dimension F) :=
  real _ (fun i => (KPCuspCharts.embedding F v i,
    Real.log ‖KPCuspCharts.embedding F ((D.ratio s : Fˣ) : F) i‖))
private theorem real_affine (s : S) (v : F) (p : KPCuspCharts.Coordinates F) :
    real _ (KPCuspCharts.toArch F
      (KPCuspCharts.affine F hF D.E D.integralUnits (D.ratio s) v p)) =
      lin _ (KPCuspCharts.embedding F ((D.ratio s : Fˣ) : F))
        (real _ (KPCuspCharts.toArch F p)) + shift (D := D) s v := by
  ext j
  rcases j with ⟨i,k⟩
  fin_cases k
  · simp [real, KPCuspCharts.toArch, KPCuspCharts.affine, lin, shift, Complex.mul_re]
  · simp [real, KPCuspCharts.toArch, KPCuspCharts.affine, lin, shift, Complex.mul_im, add_comm]
  · simp [real, KPCuspCharts.toArch, KPCuspCharts.affine, lin, shift,
      KPCuspLogShape.logarithm, KPCuspLogShape.logRatio, KPCuspCharts.embedding,
      NumberField.InfinitePlace.norm_embedding_eq, add_assoc]
private theorem action_lin (G : KPCuspCharts.ChartOutput F hF S D)
    (s : S) (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : Matrix.ProjGenLinGroup.mk A = s.val) (hup : A 1 0 = 0)
    (x : Space (KPCuspLogShape.dimension F)) :
    KPCuspSiegel.action F s.val (arch _ x) =
      arch _ (lin _ (KPCuspCharts.embedding F ((D.ratio s : Fˣ) : F)) x +
        shift (D := D) s (A 0 1 / A 1 1)) := by
  obtain ⟨p, hp⟩ := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).surjective (arch _ x)
  change KPCuspCharts.toArch F p = arch _ x at hp
  rw [← hp, G.actual_action s A hA hup, ← real_arch _ x, ← hp, ← real_affine, arch_real]
private theorem mean_lin (G : KPCuspCharts.ChartOutput F hF S D)
    (s : S) (v : F) (x : Space (KPCuspLogShape.dimension F)) :
    KPCuspLogShape.meanHeight _
      (arch _ (lin _ (KPCuspCharts.embedding F ((D.ratio s : Fˣ) : F)) x + shift (D := D) s v)) =
      KPCuspLogShape.meanHeight _ (arch _ x) := by
  obtain ⟨p, hp⟩ := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).surjective (arch _ x)
  change KPCuspCharts.toArch F p = arch _ x at hp
  rw [← real_arch _ x, ← hp, ← real_affine, arch_real,
    KPCuspCharts.toArch_meanHeight F G.positive_dimension]
  simp only [KPCuspCharts.affine]
  rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
  exact hF

end GreenTransport

theorem rawWeightedGreenDensity_high_orbit_invariant
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (p q : {p : KPCuspCharts.Coordinates F // T < p.2})
    (hrel : KPCuspCharts.highRelation F S T p q) :
    rawWeightedGreenDensity v η p.val = rawWeightedGreenDensity v η q.val := by
  open GreenTransport in
  change MulAction.orbitRel S (KPArch.Space _) (KPCuspCharts.toArch F p.val)
    (KPCuspCharts.toArch F q.val) at hrel
  obtain ⟨s, hs⟩ := hrel
  change KPCuspSiegel.action F s.val (KPCuspCharts.toArch F q.val) =
    KPCuspCharts.toArch F p.val at hs
  obtain ⟨A, hA, hup⟩ := D.upper s.val s.property
  let d := KPCuspLogShape.dimension F
  let a := KPCuspCharts.embedding F ((D.ratio s : Fˣ) : F)
  let b := GreenTransport.shift (D := D) s (A 0 1 / A 1 1)
  let x := real d (KPCuspCharts.toArch F q.val)
  let c : ℂ := KPCuspGenuineMonodromy.chi F ζ hζ (ρ s)
  have ha : ∀ i, a i ≠ 0 := fun i =>
    (map_ne_zero (KPCusp.complexPlace F i).embedding).mpr (Units.ne_zero _)
  have hc : ‖c‖ = 1 := by
    apply IsOfFinOrder.norm_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨3, by decide, ?_⟩
    have hp : (ρ s) ^ 3 = 1 := by
      apply Subtype.ext
      exact (mem_rootsOfUnity 3 _).mp (ρ s).property
    simpa only [c, map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun u => (KPCuspGenuineMonodromy.chi F ζ hζ u : ℂ)) hp
  have hb : ∀ i, b (i,2) = Real.log ‖a i‖ := by
    intro i
    simp [b, GreenTransport.shift, real, a]
  have hmean : Continuous (fun z : Space d => KPCuspLogShape.meanHeight d (arch d z)) :=
    ((smooth_mean d).comp (smooth_arch d)).continuous
  have hx : T < KPCuspLogShape.meanHeight d (arch d x) := by
    rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
    exact q.property
  have hh : ∀ᶠ z in nhds x, T < KPCuspLogShape.meanHeight d (arch d z) :=
    (isOpen_lt continuous_const hmean).mem_nhds hx
  have he : (fun z => v.val (arch d (GreenTransport.lin d a z + b))) =ᶠ[nhds x]
      (fun z => c * v.val (arch d z)) := by
    filter_upwards [hh] with z hz
    rw [← GreenTransport.action_lin G s A hA hup]
    exact v.equivariant s (arch d z) hz
  have hcut : (fun z => rawCutoffUpstairs v (fun t => η t ^ 2)
      (GreenTransport.lin d a z + b)) =ᶠ[nhds x]
      (fun z => c * rawCutoffUpstairs v (fun t => η t ^ 2) z) := by
    filter_upwards [he] with z hz
    change (η (KPCuspLogShape.meanHeight d (arch d (GreenTransport.lin d a z + b))) ^ 2 : ℝ) *
      v.val (arch d (GreenTransport.lin d a z + b)) =
      c * ((η (KPCuspLogShape.meanHeight d (arch d z)) ^ 2 : ℝ) * v.val (arch d z))
    rw [GreenTransport.mean_lin G s (A 0 1 / A 1 1) z, hz]
    ring
  have hp : real d (KPCuspCharts.toArch F p.val) = GreenTransport.lin d a x + b := by
    rw [← hs, G.actual_action s A hA hup]
    exact GreenTransport.real_affine s (A 0 1 / A 1 1) q.val
  unfold rawWeightedGreenDensity
  rw [hp]
  exact congrArg Complex.re
    (GreenTransport.pairing_transform d a ha b x hb
      (rawCutoffUpstairs v (fun t => η t ^ 2)) (v.val ∘ arch d) c hc hcut he)

theorem weightedGreenDensity_geometry
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (η : ℝ → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ContinuousOn (rawWeightedGreenDensity v η) {p | T < p.2} ∧
      Function.support (rawWeightedGreenDensity v η) ⊆ {p | p.2 ∈ tsupport η} ∧
      ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
        KPCuspCharts.highRelation F S T p q →
          rawWeightedGreenDensity v η p.val = rawWeightedGreenDensity v η q.val :=
  ⟨rawWeightedGreenDensity_continuousOn G v η hη,
   rawWeightedGreenDensity_support G v η,
   fun p q hrel => rawWeightedGreenDensity_high_orbit_invariant G v η p q hrel⟩

end DedekindZetaZeroFree.KPCompactGreenRadialIntegrability

end

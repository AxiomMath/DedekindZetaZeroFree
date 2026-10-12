module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.HeightExhaustion

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff
open MeasureTheory Filter
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

theorem coordinateDerivative_mul (d : ℕ) (i : Fin d) (k : Fin 3)
    (f g : HyperbolicChart.Space d → ℂ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (p : HyperbolicChart.Space d) :
    HyperbolicChart.coordinateDerivative d i k (fun q => f q * g q) p =
      f p * HyperbolicChart.coordinateDerivative d i k g p +
        g p * HyperbolicChart.coordinateDerivative d i k f p := by
  simpa [HyperbolicChart.coordinateDerivative, Pi.mul_def] using congrArg
    (fun A : HyperbolicChart.Space d →L[ℝ] ℂ => A (HyperbolicChart.coordinateVector d i k))
    ((hf p).hasFDerivAt.mul (hg p).hasFDerivAt).fderiv

theorem coordinateDerivative_add (d : ℕ) (i : Fin d) (k : Fin 3)
    (f g : HyperbolicChart.Space d → ℂ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    HyperbolicChart.coordinateDerivative d i k (fun q => f q + g q) =
      fun q => HyperbolicChart.coordinateDerivative d i k f q +
        HyperbolicChart.coordinateDerivative d i k g q := by
  funext p
  simp only [HyperbolicChart.coordinateDerivative]
  change (fderiv ℝ (f + g) p) (HyperbolicChart.coordinateVector d i k) =
    (fderiv ℝ f p) (HyperbolicChart.coordinateVector d i k) +
      (fderiv ℝ g p) (HyperbolicChart.coordinateVector d i k)
  rw [((hf p).hasFDerivAt.add (hg p).hasFDerivAt).fderiv]
  rfl

theorem differentiable_coordinateDerivative (d : ℕ) (i : Fin d) (k : Fin 3)
    (f : HyperbolicChart.Space d → ℂ) (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ (HyperbolicChart.coordinateDerivative d i k f) := by
  have : ContDiff ℝ ∞ (HyperbolicChart.coordinateDerivative d i k f) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  exact this.differentiable (by simp)

theorem coordinateDerivative_mul2 (d : ℕ) (i : Fin d) (k : Fin 3)
    (f g : HyperbolicChart.Space d → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (p : HyperbolicChart.Space d) :
    HyperbolicChart.coordinateDerivative d i k
        (HyperbolicChart.coordinateDerivative d i k (fun q => f q * g q)) p =
      f p * HyperbolicChart.coordinateDerivative d i k
          (HyperbolicChart.coordinateDerivative d i k g) p +
      g p * HyperbolicChart.coordinateDerivative d i k
          (HyperbolicChart.coordinateDerivative d i k f) p +
      2 * HyperbolicChart.coordinateDerivative d i k f p *
        HyperbolicChart.coordinateDerivative d i k g p := by
  have hfm : Differentiable ℝ f := hf.differentiable (by simp)
  have hgm : Differentiable ℝ g := hg.differentiable (by simp)
  have hdf : Differentiable ℝ (HyperbolicChart.coordinateDerivative d i k f) :=
    differentiable_coordinateDerivative d i k f hf
  have hdg : Differentiable ℝ (HyperbolicChart.coordinateDerivative d i k g) :=
    differentiable_coordinateDerivative d i k g hg
  rw [show HyperbolicChart.coordinateDerivative d i k
        (HyperbolicChart.coordinateDerivative d i k (fun q => f q * g q)) p
      = HyperbolicChart.coordinateDerivative d i k
          (fun q => f q * HyperbolicChart.coordinateDerivative d i k g q +
            g q * HyperbolicChart.coordinateDerivative d i k f q) p from by
    congr 1
    funext q
    exact coordinateDerivative_mul d i k f g hfm hgm q]
  rw [coordinateDerivative_add d i k
      (fun q => f q * HyperbolicChart.coordinateDerivative d i k g q)
      (fun q => g q * HyperbolicChart.coordinateDerivative d i k f q)
      (hfm.mul hdg) (hgm.mul hdf)]
  simp only [Pi.add_apply]
  rw [coordinateDerivative_mul d i k f (HyperbolicChart.coordinateDerivative d i k g) hfm hdg p,
    coordinateDerivative_mul d i k g (HyperbolicChart.coordinateDerivative d i k f) hgm hdf p]
  ring

def rawPairing (d : ℕ) (U W : HyperbolicChart.Cotangent d) : ℂ :=
  ∑ i, ∑ k, U i k * W i k

theorem laplacian_mul (d : ℕ) (f g : HyperbolicChart.Space d → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (p : HyperbolicChart.Space d) :
    HyperbolicChart.laplacian d (fun q => f q * g q) p =
      f p * HyperbolicChart.laplacian d g p + g p * HyperbolicChart.laplacian d f p -
      2 * rawPairing d (HyperbolicChart.differential d f p)
        (HyperbolicChart.differential d g p) := by
  have hfm : Differentiable ℝ f := hf.differentiable (by simp)
  have hgm : Differentiable ℝ g := hg.differentiable (by simp)
  simp only [HyperbolicChart.laplacian, HyperbolicChart.differential, rawPairing,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Matrix.empty_eq, Fin.zero_eta]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordinateDerivative_mul2 d i 2 f g hf hg p,
      coordinateDerivative_mul d i 2 f g hfm hgm p,
      coordinateDerivative_mul2 d i 0 f g hf hg p,
      coordinateDerivative_mul2 d i 1 f g hf hg p]
  have hexp : (↑(Real.exp (2 * p.ofLp (i, 2))) : ℂ) =
      (↑(Real.exp (p.ofLp (i, 2))) : ℂ) ^ 2 := by
    rw [show (2 : ℝ) * p.ofLp (i, 2) = p.ofLp (i, 2) + p.ofLp (i, 2) by ring, Real.exp_add]
    push_cast; ring
  rw [hexp]
  simp only [Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.head_cons]
  ring

theorem cutoff_hyperbolic_laplacian_error_bound (d : ℕ)
    (f g : HyperbolicChart.Space d → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (p : HyperbolicChart.Space d) :
    ‖HyperbolicChart.laplacian d (fun q => f q * g q) p -
        f p * HyperbolicChart.laplacian d g p‖ ≤
      ‖g p‖ * ‖HyperbolicChart.laplacian d f p‖ +
      2 * Real.sqrt (∑ i : Fin d, ∑ k : Fin 3, ‖HyperbolicChart.differential d f p i k‖ ^ 2) *
        Real.sqrt (∑ i : Fin d, ∑ k : Fin 3, ‖HyperbolicChart.differential d g p i k‖ ^ 2) := by
  rw [laplacian_mul d f g hf hg p]
  unfold rawPairing
  rw [show f p * HyperbolicChart.laplacian d g p +
      g p * HyperbolicChart.laplacian d f p -
      2 * (∑ i : Fin d, ∑ k : Fin 3,
        HyperbolicChart.differential d f p i k * HyperbolicChart.differential d g p i k) -
      f p * HyperbolicChart.laplacian d g p =
      g p * HyperbolicChart.laplacian d f p -
      2 * (∑ i : Fin d, ∑ k : Fin 3,
        HyperbolicChart.differential d f p i k * HyperbolicChart.differential d g p i k) by ring]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin d × Fin 3))
    (fun ik => ‖HyperbolicChart.differential d f p ik.1 ik.2‖)
    (fun ik => ‖HyperbolicChart.differential d g p ik.1 ik.2‖)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at hcs
  have hn : ‖∑ i : Fin d, ∑ k : Fin 3,
      HyperbolicChart.differential d f p i k * HyperbolicChart.differential d g p i k‖ ≤
      ∑ i : Fin d, ∑ k : Fin 3,
        ‖HyperbolicChart.differential d f p i k‖ * ‖HyperbolicChart.differential d g p i k‖ := by
    calc
      _ ≤ ∑ i : Fin d, ‖∑ k : Fin 3,
        HyperbolicChart.differential d f p i k * HyperbolicChart.differential d g p i k‖ :=
        norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun i hi => by
        simpa only [norm_mul] using norm_sum_le Finset.univ
          (fun k : Fin 3 => HyperbolicChart.differential d f p i k * HyperbolicChart.differential d g p i k)
  calc
    _ ≤ ‖g p * HyperbolicChart.laplacian d f p‖ +
      ‖2 * (∑ i : Fin d, ∑ k : Fin 3,
        HyperbolicChart.differential d f p i k * HyperbolicChart.differential d g p i k)‖ := norm_sub_le _ _
    _ = ‖g p‖ * ‖HyperbolicChart.laplacian d f p‖ +
      2 * ‖∑ i : Fin d, ∑ k : Fin 3,
        HyperbolicChart.differential d f p i k * HyperbolicChart.differential d g p i k‖ := by
      simp [norm_mul]
    _ ≤ _ := by nlinarith [hn.trans hcs]

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
  (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
  (a : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

 theorem cutoff_toArch_contDiff : ContDiff ℝ (⊤ : ℕ∞) (toArch F) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.prodMk
  · have h : (fun p : Coordinates F => (⟨p (i,0), p (i,1)⟩ : ℂ)) =
        fun p => Complex.ofRealCLM (p (i,0)) + Complex.ofRealCLM (p (i,1)) * Complex.I := by
      funext p
      rw [Complex.mk_eq_add_mul_I, Complex.ofRealCLM_apply, Complex.ofRealCLM_apply]
    rw [h]; fun_prop
  · fun_prop
 theorem cutoff_toArch_fromArch (x : Arch F) : toArch F (fromArch F x) = x := by
  funext i
  apply Prod.ext
  · apply Complex.ext <;> simp [fromArch, toArch]
  · simp [fromArch, toArch]

end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

end

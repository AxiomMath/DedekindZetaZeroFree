module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspDivergence.RadialAndTangentialComponents

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical Topology
namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice
open KPMeanZeroWeightedEnergy HyperbolicChart

private theorem smooth_real (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (real d) := by
  apply (contDiff_piLp 2).mpr
  intro ⟨i,k⟩
  fin_cases k
  · simpa [real, Function.comp_def] using Complex.reCLM.contDiff.comp
      (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
  · simpa [real, Function.comp_def] using Complex.imCLM.contDiff.comp
      (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
  · simpa [real, Function.comp_def] using contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)

private theorem smooth_arch (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (arch d) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.prodMk
  · exact Complex.equivRealProdCLM.symm.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (0 : Fin 3))).contDiff.prodMk
       (EuclideanSpace.proj (𝕜 := ℝ) (i, (1 : Fin 3))).contDiff)
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff
private theorem smooth_mean (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (KPCuspLogShape.meanHeight d) := by
  unfold KPCuspLogShape.meanHeight
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i hi
  exact contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)
private theorem differential_smoothAt (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => differential d g q i k) x := by
  have hd (k : Fin 3) : ContDiffAt ℝ (⊤ : ℕ∞) (coordinateDerivative d i k g) x :=
    (hg.fderiv_right (by simp)).clm_apply contDiffAt_const
  have he : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Space d => (Real.exp (q (i,2)) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.contDiffAt.exp)
  fin_cases k
  · simpa [differential] using hd 2
  · simpa [differential] using he.mul (hd 0)
  · simpa [differential] using he.mul (hd 1)

private theorem flux_component_contDiff
    (d : ℕ) {T : ℝ} (u : KPArch.Space d → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {z | T < KPCuspLogShape.meanHeight d z})
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) (i : Fin d) (k : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Space d =>
      (a (KPCuspLogShape.meanHeight d (arch d x)) : ℂ) *
        differential d (fun q => (u (arch d q) : ℂ)) x i k) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  let h : Space d → ℝ := fun x => KPCuspLogShape.meanHeight d (arch d x)
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := (smooth_mean d).comp (smooth_arch d)
  by_cases hx : h x ∈ tsupport a
  · have hopen : IsOpen {z : KPArch.Space d | T < KPCuspLogShape.meanHeight d z} :=
      isOpen_lt continuous_const (smooth_mean d).continuous
    have hxT : T < h x := ha.2.2 hx
    have hu' : ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (u (arch d q) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x
        ((hu.contDiffAt (hopen.mem_nhds hxT)).comp x (smooth_arch d).contDiffAt)
    exact (Complex.ofRealCLM.contDiff.comp (ha.1.comp hh)).contDiffAt.mul
      (differential_smoothAt d _ x hu' i k)
  · have hn : (tsupport a)ᶜ ∈ 𝓝 (h x) := (isClosed_tsupport a).isOpen_compl.mem_nhds hx
    have he : (fun q : Space d => (a (h q) : ℂ) *
        differential d (fun q => (u (arch d q) : ℂ)) q i k) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hh.continuous.continuousAt.preimage_mem_nhds hn] with q hq
      simp [image_eq_zero_of_notMem_tsupport hq]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem cutoff_flux_component_contDiff
    (d : ℕ) {T : ℝ} (u : KPArch.Space d → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {z | T < KPCuspLogShape.meanHeight d z})
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) (i : Fin d) (k : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => cutoffScalarFlux d u a x i k) :=
  flux_component_contDiff d u hu a ha i k

theorem cutoff_tangentialDivergence_contDiff
    {F : Type} [Field F] [NumberField F]
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : KPCuspCharts.Coordinates F =>
      tangentialDivergence F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) p.1 p.2) := by
  let d := KPCuspLogShape.dimension F
  let W := cutoffScalarFlux d u a
  have hw (i : Fin d) (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => W x i k) :=
    flux_component_contDiff d u hu a ha i k
  have hc (i j : Fin d) (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (coordinateDerivative d j k (fun x => W x i 0)) :=
    ((hw i 0).fderiv_right (by simp)).clm_apply contDiff_const
  have hc' (i : Fin d) (j k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (coordinateDerivative d i j (fun x => W x i k)) :=
    ((hw i k).fderiv_right (by simp)).clm_apply contDiff_const
  have he (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space d => (Real.exp (x (i,2)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.exp)
  have hx : ContDiff ℝ (⊤ : ℕ∞) (fun p : KPCuspCharts.Coordinates F =>
      real d (KPCuspCharts.toArch F p)) :=
    (smooth_real d).comp ((KPCuspCharts.toArch_contDiff F).of_le (by simp))
  unfold tangentialDivergence
  apply ContDiff.sum
  intro i hi
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space d =>
      ∑ j : Fin d, (coordinateDerivative d j 2 (fun q => W q i 0) x).re) := by
    apply ContDiff.sum
    intro j hj
    exact Complex.reCLM.contDiff.comp (hc i j 2)
  exact (((Complex.reCLM.contDiff.comp (hc i i 2)).sub (hs.div_const _)).add
    (Complex.reCLM.contDiff.comp ((he i).mul (hc' i 0 1)))).add
      (Complex.reCLM.contDiff.comp ((he i).mul (hc' i 1 2))) |>.comp hx

private theorem arch_real (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  ext i <;> simp [arch, real]

theorem cutoff_tangentialDivergence_eq_zero_of_notMem_tsupport
    {F : Type} [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (a : ℝ → ℝ) (c : KPCuspCharts.Cross F) (t : ℝ)
    (ht : t ∉ tsupport a) :
    tangentialDivergence F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c t = 0 := by
  let d := KPCuspLogShape.dimension F
  let x := real d (KPCuspCharts.toArch F (c,t))
  have hmean : KPCuspLogShape.meanHeight d (arch d x) = t := by
    rw [arch_real]
    exact KPCuspCharts.toArch_meanHeight F hd (c,t)
  have hh : Continuous (fun q : Space d => KPCuspLogShape.meanHeight d (arch d q)) := by
    unfold KPCuspLogShape.meanHeight
    apply Continuous.div_const
    apply continuous_finset_sum
    intro i hi
    exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).continuous
  have he : (fun q : Space d => a (KPCuspLogShape.meanHeight d (arch d q)))
      =ᶠ[nhds x] (fun _ => 0) := by
    have hat := notMem_tsupport_iff_eventuallyEq.mp ht
    apply hat.comp_tendsto
    rw [← hmean]
    exact hh.continuousAt
  have hw (i : Fin d) (k : Fin 3) :
      (fun q => cutoffScalarFlux d u a q i k) =ᶠ[nhds x] (fun _ => 0) := by
    filter_upwards [he] with q hq
    simp only [cutoffScalarFlux, hq, Complex.ofReal_zero, zero_mul]
  have hder (i j : Fin d) (k l : Fin 3) :
      coordinateDerivative d j l (fun q => cutoffScalarFlux d u a q i k) x = 0 := by
    unfold coordinateDerivative
    rw [(hw i k).fderiv_eq]
    simp
  simp [tangentialDivergence, hder, d, x]

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice

end

module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspDivergence.CodifferentialInvariance
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspDivergence.PeriodicShapeCancellation
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspCrossSections.FiberIntegralComparison
public import DedekindZetaZeroFree.Geometry.Cusps.AffineTorusBundles.RadialProductPresentation

@[expose] public section

section
noncomputable section
open MeasureTheory
open scoped Classical Topology

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice
open KPMeanZeroWeightedEnergy HyperbolicChart

private theorem arch_real (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  ext i <;> simp [arch, real]

 def realL (d : ℕ) : KPArch.Space d →L[ℝ] Space d :=
  LinearMap.toContinuousLinearMap {
    toFun := real d
    map_add' := by
      intro x y; ext ⟨i,k⟩; fin_cases k <;> simp [real]
    map_smul' := by
      intro a x; ext ⟨i,k⟩; fin_cases k <;> simp [real, Complex.real_smul] }

 def tauVec (d : ℕ) : KPArch.Space d := fun _ => (0, 1)

private theorem hasDerivAt_toArch {F : Type} [Field F] [NumberField F]
    (c : KPCuspCharts.Cross F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => KPCuspCharts.toArch F (c, s)) (tauVec (KPCuspLogShape.dimension F)) t := by
  rw [hasDerivAt_pi]
  intro i
  have h1 : HasDerivAt (fun s : ℝ => s + (c.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i) 1 t :=
    (hasDerivAt_id t).add_const _
  have h2 := (hasDerivAt_const (x := t) (c := (c.1 i))).prodMk h1
  simpa [KPCuspCharts.toArch, tauVec] using h2

private theorem realL_tauVec (d : ℕ) :
    realL d (tauVec d) = ∑ j : Fin d, coordinateVector d j 2 := by
  ext ⟨i,k⟩
  fin_cases k <;> simp [realL, real, tauVec, coordinateVector, PiLp.toLp_apply,
    Finset.sum_apply, Finset.sum_ite, Finset.mem_univ, PiLp.proj_apply]

private theorem hasDerivAt_gamma {F : Type} [Field F] [NumberField F]
    (c : KPCuspCharts.Cross F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, s)))
      (∑ j : Fin (KPCuspLogShape.dimension F), coordinateVector (KPCuspLogShape.dimension F) j 2) t := by
  have h := (realL (KPCuspLogShape.dimension F)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_toArch (F := F) c t)
  rwa [realL_tauVec] at h

private theorem re_sum' {n : ℕ} (z : Fin n → ℂ) : (∑ i, z i).re = ∑ i, (z i).re := by
  rw [← Complex.reCLM_apply, map_sum]
  simp

private theorem codiff_add_tang {F : Type} [Field F] [NumberField F]
    (W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F))
    (c : KPCuspCharts.Cross F) (t : ℝ) :
    (codifferential (KPCuspLogShape.dimension F) W
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, t)))).re +
      tangentialDivergence F W c t =
    ∑ i : Fin (KPCuspLogShape.dimension F),
      (2 * (W (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, t))) i 0).re -
        (∑ j : Fin (KPCuspLogShape.dimension F),
          (coordinateDerivative (KPCuspLogShape.dimension F) j 2 (fun q => W q i 0)
            (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, t)))).re) /
          (KPCuspLogShape.dimension F : ℝ)) := by
  rw [codifferential, tangentialDivergence]
  dsimp only
  rw [re_sum', ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  ring

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

private theorem u_arch_smoothAt {F : Type} [Field F] [NumberField F] {T : ℝ}
    (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (x : Space (KPCuspLogShape.dimension F))
    (hx : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Space (KPCuspLogShape.dimension F) =>
      (u (arch (KPCuspLogShape.dimension F) q) : ℂ)) x := by
  have hopen : IsOpen {z : KPArch.Space (KPCuspLogShape.dimension F) |
      T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z} :=
    isOpen_lt continuous_const (smooth_mean _).continuous
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp x
    ((hu.contDiffAt (hopen.mem_nhds hx)).comp x (smooth_arch _).contDiffAt)

private theorem cutoffScalarFlux_component_smoothAt {F : Type} [Field F] [NumberField F] {T : ℝ}
    (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (a : ℝ → ℝ) (ha : CompactRadialTest T a)
    (x : Space (KPCuspLogShape.dimension F))
    (hx : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x))
    (i : Fin (KPCuspLogShape.dimension F)) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => cutoffScalarFlux (KPCuspLogShape.dimension F) u a q i k) x := by
  have hg := u_arch_smoothAt u hu x hx
  have hd1 := differential_smoothAt _ _ x hg i k
  have haa : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Space (KPCuspLogShape.dimension F) =>
      (a (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (arch (KPCuspLogShape.dimension F) q)) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (ha.1.contDiffAt.comp x ((smooth_mean _).comp (smooth_arch _)).contDiffAt)
  simpa [cutoffScalarFlux, scalarDifferential] using haa.mul hd1

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice
open KPMeanZeroWeightedEnergy HyperbolicChart

theorem cutoff_scalar_codifferential_pointwise
    {F : Type} [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (a : ℝ → ℝ) (ha : CompactRadialTest T a)
    (c : KPCuspCharts.Cross F) (t : ℝ) :
    (codifferential (KPCuspLogShape.dimension F)
      (cutoffScalarFlux (KPCuspLogShape.dimension F) u a)
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, t)))).re =
    -deriv (radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c) t +
      2 * (KPCuspLogShape.dimension F : ℝ) *
        radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c t -
      tangentialDivergence F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c t := by
  set W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F) :=
    cutoffScalarFlux (KPCuspLogShape.dimension F) u a with hWdef
  set x : Space (KPCuspLogShape.dimension F) :=
    real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, t)) with hxdef
  have hD : (KPCuspLogShape.dimension F : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)

  have hxmean : KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x) = t := by
    rw [hxdef, arch_real]
    exact KPCuspCharts.toArch_meanHeight F hd (c, t)
  have hmean_cont : Filter.Tendsto
      (fun q : Space (KPCuspLogShape.dimension F) =>
        KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
          (arch (KPCuspLogShape.dimension F) q)) (nhds x) (nhds t) := by
    rw [← hxmean]
    exact ((smooth_mean _).comp (smooth_arch _)).continuous.continuousAt

  have hterm (i : Fin (KPCuspLogShape.dimension F)) :
      HasDerivAt (fun s : ℝ =>
          (W (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, s))) i 0).re)
        (∑ j : Fin (KPCuspLogShape.dimension F),
          (coordinateDerivative (KPCuspLogShape.dimension F) j 2 (fun q => W q i 0) x).re) t := by
    by_cases hT : T < t
    · have hxT : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
          (arch (KPCuspLogShape.dimension F) x) := by rw [hxmean]; exact hT
      have hsm := cutoffScalarFlux_component_smoothAt u hu a ha x hxT i 0
      have hF : HasFDerivAt (fun q : Space (KPCuspLogShape.dimension F) => W q i 0)
          (fderiv ℝ (fun q : Space (KPCuspLogShape.dimension F) => W q i 0) x) x :=
        (hsm.differentiableAt (by simp)).hasFDerivAt
      have hγ := hasDerivAt_gamma (F := F) c t
      have hcomp := hF.comp_hasDerivAt t hγ
      have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomp
      have hgoal : Complex.reCLM ((fderiv ℝ
            (fun q : Space (KPCuspLogShape.dimension F) => W q i 0) x)
            (∑ j : Fin (KPCuspLogShape.dimension F),
              coordinateVector (KPCuspLogShape.dimension F) j 2)) =
          ∑ j : Fin (KPCuspLogShape.dimension F),
            (coordinateDerivative (KPCuspLogShape.dimension F) j 2 (fun q => W q i 0) x).re := by
        simp only [map_sum, Complex.reCLM_apply, coordinateDerivative]
      rw [hgoal] at hreal
      simpa [Function.comp_def, Complex.reCLM_apply] using hreal
    ·
      have ht_not : t ∉ tsupport a := fun h => hT (ha.2.2 h)
      have ha_ev : a =ᶠ[nhds t] 0 := notMem_tsupport_iff_eventuallyEq.mp ht_not
      have hcomp : (fun q : Space (KPCuspLogShape.dimension F) =>
          a (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
            (arch (KPCuspLogShape.dimension F) q))) =ᶠ[nhds x] 0 :=
        ha_ev.comp_tendsto hmean_cont
      have hWev : (fun q : Space (KPCuspLogShape.dimension F) => W q i 0) =ᶠ[nhds x] 0 := by
        filter_upwards [hcomp] with q hq
        rw [hWdef]; simp [cutoffScalarFlux, hq]
      have hfderiv : fderiv ℝ (fun q : Space (KPCuspLogShape.dimension F) => W q i 0) x = 0 := by
        rw [hWev.fderiv_eq]
        exact congrFun fderiv_zero x
      have hzero : ∀ j : Fin (KPCuspLogShape.dimension F),
          (coordinateDerivative (KPCuspLogShape.dimension F) j 2 (fun q => W q i 0) x).re = 0 := by
        intro j; simp [coordinateDerivative, hfderiv]
      have hsum : (∑ j : Fin (KPCuspLogShape.dimension F),
          (coordinateDerivative (KPCuspLogShape.dimension F) j 2 (fun q => W q i 0) x).re) = 0 := by
        simp [hzero]
      have hγcont : ContinuousAt
          (fun s : ℝ => real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, s))) t :=
        (hasDerivAt_gamma (F := F) c t).continuousAt
      have hWev' : (fun s : ℝ =>
          W (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, s))) i 0)
          =ᶠ[nhds t] 0 := hWev.comp_tendsto hγcont
      have hz : (fun s : ℝ =>
          (W (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, s))) i 0).re)
          =ᶠ[nhds t] 0 := by
        filter_upwards [hWev'] with s hs
        simp [hs]
      rw [hsum]
      exact hz.hasDerivAt_iff.mpr (hasDerivAt_const t 0)

  have hsumderiv : HasDerivAt (fun s : ℝ =>
        ∑ i : Fin (KPCuspLogShape.dimension F),
          (W (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, s))) i 0).re)
      (∑ i : Fin (KPCuspLogShape.dimension F), ∑ j : Fin (KPCuspLogShape.dimension F),
        (coordinateDerivative (KPCuspLogShape.dimension F) j 2 (fun q => W q i 0) x).re) t := by
    have h := HasDerivAt.sum (u := Finset.univ) (fun i _ => hterm i)
    have hfun : (fun s : ℝ => ∑ i : Fin (KPCuspLogShape.dimension F),
          (W (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, s))) i 0).re)
        = (∑ i : Fin (KPCuspLogShape.dimension F), fun s : ℝ =>
          (W (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, s))) i 0).re) := by
      funext s
      simp [Finset.sum_apply]
    rw [hfun]
    exact h
  have hderiv : deriv (radialCoefficient F W c) t =
      (∑ i : Fin (KPCuspLogShape.dimension F), ∑ j : Fin (KPCuspLogShape.dimension F),
        (coordinateDerivative (KPCuspLogShape.dimension F) j 2 (fun q => W q i 0) x).re) /
        (KPCuspLogShape.dimension F : ℝ) := by
    have hrad : HasDerivAt (radialCoefficient F W c)
        ((∑ i : Fin (KPCuspLogShape.dimension F), ∑ j : Fin (KPCuspLogShape.dimension F),
          (coordinateDerivative (KPCuspLogShape.dimension F) j 2 (fun q => W q i 0) x).re) /
          (KPCuspLogShape.dimension F : ℝ)) t := by
      unfold radialCoefficient
      exact hsumderiv.div_const _
    exact hrad.deriv

  have hmain : (codifferential (KPCuspLogShape.dimension F) W x).re +
      tangentialDivergence F W c t =
      -deriv (radialCoefficient F W c) t +
        2 * (KPCuspLogShape.dimension F : ℝ) * radialCoefficient F W c t := by
    rw [hderiv, codiff_add_tang W c t]
    rw [radialCoefficient]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_div]
    field_simp
    ring
  linarith [hmain]

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical Topology
namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice
open KPMeanZeroWeightedEnergy HyperbolicChart

private theorem arch_real_for_radialCoefficient (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  ext i <;> simp [arch, real]

 def radialCoefficientRealification (d : ℕ) : KPArch.Space d →L[ℝ] Space d :=
  LinearMap.toContinuousLinearMap {
    toFun := real d
    map_add' := by
      intro x y; ext ⟨i,k⟩; fin_cases k <;> simp [real]
    map_smul' := by
      intro a x; ext ⟨i,k⟩; fin_cases k <;> simp [real, Complex.real_smul] }

 def radialCoefficientHeightVector (d : ℕ) : KPArch.Space d := fun _ => (0, 1)

private theorem hasDerivAt_toArch_for_radialCoefficient {F : Type} [Field F] [NumberField F]
    (c : KPCuspCharts.Cross F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => KPCuspCharts.toArch F (c, s)) (radialCoefficientHeightVector (KPCuspLogShape.dimension F)) t := by
  rw [hasDerivAt_pi]
  intro i
  have h1 : HasDerivAt (fun s : ℝ => s + (c.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i) 1 t :=
    (hasDerivAt_id t).add_const _
  have h2 := (hasDerivAt_const (x := t) (c := (c.1 i))).prodMk h1
  simpa [KPCuspCharts.toArch, radialCoefficientHeightVector] using h2

private theorem radialCoefficientRealification_heightVector (d : ℕ) :
    radialCoefficientRealification d (radialCoefficientHeightVector d) = ∑ j : Fin d, coordinateVector d j 2 := by
  ext ⟨i,k⟩
  fin_cases k <;> simp [radialCoefficientRealification, real, radialCoefficientHeightVector, coordinateVector, PiLp.toLp_apply,
    Finset.sum_apply, Finset.sum_ite, Finset.mem_univ, PiLp.proj_apply]

private theorem hasDerivAt_realChart_for_radialCoefficient {F : Type} [Field F] [NumberField F]
    (c : KPCuspCharts.Cross F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, s)))
      (∑ j : Fin (KPCuspLogShape.dimension F), coordinateVector (KPCuspLogShape.dimension F) j 2) t := by
  have h := (radialCoefficientRealification (KPCuspLogShape.dimension F)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_toArch_for_radialCoefficient (F := F) c t)
  rwa [radialCoefficientRealification_heightVector] at h

private theorem contDiff_arch_for_radialCoefficient (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (arch d) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.prodMk
  · exact Complex.equivRealProdCLM.symm.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (0 : Fin 3))).contDiff.prodMk
       (EuclideanSpace.proj (𝕜 := ℝ) (i, (1 : Fin 3))).contDiff)
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff

private theorem contDiff_meanHeight_for_radialCoefficient (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (KPCuspLogShape.meanHeight d) := by
  unfold KPCuspLogShape.meanHeight
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i hi
  exact contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)

private theorem radial_eq_slice_deriv
    {F : Type} [Field F] [NumberField F] {T : ℝ}
    (hd : 0 < KPCuspLogShape.dimension F)
    (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (a : ℝ → ℝ) (c : KPCuspCharts.Cross F) (t : ℝ) (ht : T < t) :
    radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c t =
      a t * deriv (fun v => u (KPCuspCharts.toArch F (c,v))) t /
        (KPCuspLogShape.dimension F : ℝ) := by
  let d := KPCuspLogShape.dimension F
  let x := real d (KPCuspCharts.toArch F (c,t))
  let g : Space d → ℂ := fun q => (u (arch d q) : ℂ)
  have hx : T < KPCuspLogShape.meanHeight d (arch d x) := by
    rw [arch_real_for_radialCoefficient, KPCuspCharts.toArch_meanHeight F hd]; exact ht
  have hu' : ContDiffAt ℝ (⊤ : ℕ∞) g x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((hu.contDiffAt ((isOpen_lt continuous_const (contDiff_meanHeight_for_radialCoefficient d).continuous).mem_nhds hx)).comp x
        (contDiff_arch_for_radialCoefficient d).contDiffAt)
  have hγ := hasDerivAt_realChart_for_radialCoefficient (F := F) c t
  have hcomp := (hu'.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hγ
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomp
  have hr' : HasDerivAt (fun v => u (KPCuspCharts.toArch F (c,v)))
      (∑ i : Fin d, (coordinateDerivative d i 2 g x).re) t := by
    simpa [Function.comp_def, g, d, arch_real_for_radialCoefficient, Complex.reCLM_apply, map_sum,
      coordinateDerivative] using hr
  unfold radialCoefficient
  simp only [cutoffScalarFlux, scalarDifferential, differential, Fin.isValue,
    arch_real_for_radialCoefficient, KPCuspCharts.toArch_meanHeight F hd, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hr'.deriv, Finset.mul_sum]
  simp [d, x, g]

theorem cutoff_tangentialDivergence_crossAction_invariant
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) (t : ℝ)
    (s : S) (c : KPCuspCharts.Cross F) :
    tangentialDivergence F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a)
        (G.crossAction s c) t =
      tangentialDivergence F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c t := by
  by_cases ht : T < t
  · have hact (v : ℝ) : KPCuspSiegel.action F s.val (KPCuspCharts.toArch F (c,v)) =
        KPCuspCharts.toArch F (G.crossAction s c,v) := by
      obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
      rw [G.actual_action s A hA hc, G.crossAction_formula s A hA hc]
      rfl
    have huEq (v : ℝ) (hv : T < v) :
        u (KPCuspCharts.toArch F (G.crossAction s c,v)) =
          u (KPCuspCharts.toArch F (c,v)) := by
      apply hinv ⟨(G.crossAction s c,v), hv⟩ ⟨(c,v), hv⟩
      exact ⟨s, hact v⟩
    have huEv : (fun v => u (KPCuspCharts.toArch F (G.crossAction s c,v))) =ᶠ[nhds t]
        (fun v => u (KPCuspCharts.toArch F (c,v))) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with v hv
      exact huEq v hv
    have hrEv : radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a)
        (G.crossAction s c) =ᶠ[nhds t]
        radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with v hv
      rw [radial_eq_slice_deriv G.positive_dimension u hu a _ v hv,
        radial_eq_slice_deriv G.positive_dimension u hu a _ v hv]
      have he : (fun w => u (KPCuspCharts.toArch F (G.crossAction s c,w))) =ᶠ[nhds v]
          (fun w => u (KPCuspCharts.toArch F (c,w))) := by
        filter_upwards [isOpen_Ioi.mem_nhds hv] with w hw
        exact huEq w hw
      rw [he.deriv_eq]
    have hd := cutoff_scalar_codifferential_high_orbit_invariant G u hu hinv a ha
      ⟨(G.crossAction s c,t), ht⟩ ⟨(c,t), ht⟩ ⟨s, hact t⟩
    rw [cutoff_scalar_codifferential_pointwise G.positive_dimension u hu a ha,
      cutoff_scalar_codifferential_pointwise G.positive_dimension u hu a ha,
      hrEv.deriv_eq, hrEv.eq_of_nhds] at hd
    linarith
  · have hnot : t ∉ tsupport a := fun hm => ht (ha.2.2 hm)
    rw [cutoff_tangentialDivergence_eq_zero_of_notMem_tsupport G.positive_dimension u a _ t hnot,
      cutoff_tangentialDivergence_eq_zero_of_notMem_tsupport G.positive_dimension u a _ t hnot]

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical Topology ENNReal

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice
open KPMeanZeroWeightedEnergy HyperbolicChart
open KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

theorem cutoff_tangentialDivergence_integrable_integral_zero
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) (t : ℝ) :
    Integrable (fun c =>
      tangentialDivergence F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c t)
      ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain) ∧
    (∫ c : KPCuspCharts.Cross F,
      tangentialDivergence F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c t
      ∂((volume.prod G.shapeMeasure).restrict G.fundamentalDomain)) = 0 := by
  let W := cutoffScalarFlux (KPCuspLogShape.dimension F) u a
  let f : KPCuspCharts.Cross F → ℝ := fun c => tangentialDivergence F W c t
  have hg := cutoff_tangentialDivergence_contDiff (F := F) u hu a ha
  have hf : Continuous f := by
    have hp : Continuous (fun c : KPCuspCharts.Cross F => (c,t)) :=
      continuous_id.prodMk continuous_const
    have hh := hg.continuous.comp hp
    exact hh
  have hfi : ∀ (s : S) (c : KPCuspCharts.Cross F), f (G.crossAction s c) = f c :=
    cutoff_tangentialDivergence_crossAction_invariant G u hu hinv a ha t
  have hi := continuous_invariant_cross_integrable G f hf hfi
  refine ⟨hi, ?_⟩
  obtain ⟨A, B, hAm, hAb, hBm, hBb, hA, hB⟩ := actual_exact_comparison_rectangle G
  letI := G.haar_shapeMeasure
  have hr : ContDiff ℝ (⊤ : ℕ∞) (real (KPCuspLogShape.dimension F)) := by
    apply (contDiff_piLp 2).mpr
    intro ⟨i,k⟩
    fin_cases k
    · simpa [real, Function.comp_def] using Complex.reCLM.contDiff.comp
        (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
    · simpa [real, Function.comp_def] using Complex.imCLM.contDiff.comp
        (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
    · simpa [real, Function.comp_def] using contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)
  have hp : Continuous (fun c : KPCuspCharts.Cross F => (c,t)) :=
    continuous_id.prodMk continuous_const
  have harch := (KPCuspCharts.toArch_contDiff F).continuous.comp hp
  have hx := hr.continuous.comp harch
  have hw (i : Fin (KPCuspLogShape.dimension F)) (k : Fin 3) :=
    cutoff_flux_component_contDiff (KPCuspLogShape.dimension F) u hu a ha i k
  have hc (i j : Fin (KPCuspLogShape.dimension F)) : ContDiff ℝ (⊤ : ℕ∞)
      (coordinateDerivative (KPCuspLogShape.dimension F) j 2 (fun x => W x i 0)) :=
    ((hw i 0).fderiv_right (by simp)).clm_apply contDiff_const
  have hshape : Continuous (fun c => shapeDivergence F W c t) := by
    unfold shapeDivergence
    apply continuous_finset_sum
    intro i hi
    exact ((Complex.reCLM.contDiff.comp (hc i i)).sub
      ((ContDiff.sum fun j _ => Complex.reCLM.contDiff.comp (hc i j)).div_const _)).continuous.comp hx
  have hhor : Continuous (fun c => horizontalDivergence F W c t) := by
    have he : (fun c => horizontalDivergence F W c t) =
        fun c => f c - shapeDivergence F W c t := by
      funext c
      dsimp [f]
      rw [tangentialDivergence_eq_horizontal_add_shape]
      ring
    rw [he]
    exact hf.sub hshape
  have hrectBound := hAb.prod hBb
  have hshapeInt : IntegrableOn (fun c => shapeDivergence F W c t)
      (A ×ˢ B) (volume.prod G.shapeMeasure) :=
    (hshape.continuousOn.integrableOn_compact hrectBound.isCompact_closure).mono_set
      subset_closure
  have hhorInt : IntegrableOn (fun c => horizontalDivergence F W c t)
      (A ×ˢ B) (volume.prod G.shapeMeasure) :=
    (hhor.continuousOn.integrableOn_compact hrectBound.isCompact_closure).mono_set
      subset_closure
  have hhorZero : (∫ c in A ×ˢ B, horizontalDivergence F W c t
      ∂volume.prod G.shapeMeasure) = 0 := by
    have hhi := hhorInt
    unfold IntegrableOn at hhi
    rw [← Measure.prod_restrict] at hhi ⊢
    rw [integral_prod_symm _ hhi]
    simp only [W, cutoff_horizontalDivergence_integral_zero G u hu hinv a ha t A hAm hAb hA,
      integral_zero]
  have hshapeZero := cutoff_shapeDivergence_rectangle_integral_zero G u hu hinv a ha t
    A B hAm hAb hBm hBb hA hB
  have hz : (∫ c in A ×ˢ B, f c ∂volume.prod G.shapeMeasure) = 0 := by
    simp only [f, tangentialDivergence_eq_horizontal_add_shape]
    rw [integral_add hhorInt hshapeInt, hhorZero, hshapeZero, add_zero]
  letI : Countable F := (Module.finBasis ℚ F).repr.injective.countable
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  letI : Countable (KPCuspArithmetic.PGL2 F) := Matrix.ProjGenLinGroup.mk_surjective.countable
  letI : Countable S := inferInstance
  letI := KPCuspCharts.homeomorphAction G.crossAction
  letI : MeasurableConstSMul S (KPCuspCharts.Cross F) :=
    ⟨fun s => (G.crossAction s).measurable⟩
  letI : SMulInvariantMeasure S (KPCuspCharts.Cross F) (volume.prod G.shapeMeasure) := by
    constructor
    intro s Z hZ
    change (volume.prod G.shapeMeasure) ((G.crossAction s) ⁻¹' Z) = _
    rw [← Measure.map_apply (G.crossAction s).measurable hZ, G.measure_invariant s]
  letI := G.finite_isotropy
  apply OrbitMultiplicity.integral_eq_zero (volume.prod G.shapeMeasure)
    G.isFundamentalDomain (hAm.prod hBm)
    (ENat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits) : ℝ≥0∞)
    _ _ (Filter.Eventually.of_forall (rectangle_orbit_multiplicity G A hA B hB))
    f hfi hi ((hhorInt.add hshapeInt).congr_fun (fun c _ => by
      exact (tangentialDivergence_eq_horizontal_add_shape W c t).symm) (hAm.prod hBm)) hz
  · simp only [ENat.card_eq_coe_natCard, ENNReal.coe_natCast]
    exact_mod_cast Nat.card_pos.ne'
  · rw [ENat.card_eq_coe_natCard]
    exact ENNReal.coe_ne_top

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical Topology

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice
open KPMeanZeroWeightedEnergy HyperbolicChart

private theorem contDiff_arch_for_cutoffFlux (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (arch d) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.prodMk
  · exact Complex.equivRealProdCLM.symm.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (0 : Fin 3))).contDiff.prodMk
       (EuclideanSpace.proj (𝕜 := ℝ) (i, (1 : Fin 3))).contDiff)
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff

private theorem contDiff_meanHeight_for_cutoffFlux (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (KPCuspLogShape.meanHeight d) := by
  unfold KPCuspLogShape.meanHeight
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i hi
  exact contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)

private theorem smooth_real (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (real d) := by
  apply (contDiff_piLp 2).mpr
  intro j
  rcases j with ⟨i, k⟩
  fin_cases k
  · simpa [real, Function.comp_def] using
      Complex.reCLM.contDiff.comp (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
  · simpa [real, Function.comp_def] using
      Complex.imCLM.contDiff.comp (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
  · simpa [real, Function.comp_def] using contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)

private theorem coordinateDerivative_contDiffAt_for_cutoffFlux (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coordinateDerivative d i k g) x := by
  exact (hg.fderiv_right (by simp)).clm_apply contDiffAt_const

private theorem differential_contDiffAt_for_cutoffFlux (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => differential d g q i k) x := by
  have he : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Space d => (Real.exp (q (i,2)) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.contDiffAt.exp)
  fin_cases k
  · simpa [differential] using coordinateDerivative_contDiffAt_for_cutoffFlux d g x hg i 2
  · simpa [differential] using he.mul (coordinateDerivative_contDiffAt_for_cutoffFlux d g x hg i 0)
  · simpa [differential] using he.mul (coordinateDerivative_contDiffAt_for_cutoffFlux d g x hg i 1)

private theorem cutoffScalarFlux_smooth (d : ℕ) (u : KPArch.Space d → ℝ) {T : ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {z | T < KPCuspLogShape.meanHeight d z})
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffScalarFlux d u a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : KPCuspLogShape.meanHeight d (arch d x) ∈ tsupport a
  · have hv : ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (u (arch d q) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x
        ((hu.contDiffAt ((isOpen_lt continuous_const (contDiff_meanHeight_for_cutoffFlux d).continuous).mem_nhds
          (ha.2.2 hx))).comp x (contDiff_arch_for_cutoffFlux d).contDiffAt)
    have hc : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x : Space d => (a (KPCuspLogShape.meanHeight d (arch d x)) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x
        ((ha.1.comp ((contDiff_meanHeight_for_cutoffFlux d).comp (contDiff_arch_for_cutoffFlux d))).contDiffAt)
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro k
    simpa only [cutoffScalarFlux, scalarDifferential] using
      hc.mul (differential_contDiffAt_for_cutoffFlux d _ x hv i k)
  · have hmhc : Continuous (fun q : Space d => KPCuspLogShape.meanHeight d (arch d q)) :=
      ((contDiff_meanHeight_for_cutoffFlux d).comp (contDiff_arch_for_cutoffFlux d)).continuous
    have hh := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto hmhc.continuousAt
    have hWz : cutoffScalarFlux d u a =ᶠ[nhds x] 0 := by
      filter_upwards [hh] with q hq
      change a (KPCuspLogShape.meanHeight d (arch d q)) = 0 at hq
      funext i k
      simp [cutoffScalarFlux, scalarDifferential, hq]
    exact contDiffAt_const.congr_of_eventuallyEq hWz

private theorem chart_smooth {F : Type} [Field F] [NumberField F] :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : KPCuspCharts.Coordinates F =>
      real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p)) :=
  (smooth_real _).comp ((KPCuspCharts.toArch_contDiff F).of_le (by simp))

theorem cutoff_radialCoefficient_regular
    {F : Type} [Field F] [NumberField F]
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) :
    Continuous (fun p : KPCuspCharts.Coordinates F =>
      radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) p.1 p.2) ∧
    Continuous (fun p : KPCuspCharts.Coordinates F =>
      deriv (radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) p.1)
        p.2) ∧
    ∀ c : KPCuspCharts.Cross F,
      Differentiable ℝ
        (radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c) := by
  let W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F) :=
    cutoffScalarFlux (KPCuspLogShape.dimension F) u a
  change Continuous (fun p : KPCuspCharts.Coordinates F => radialCoefficient F W p.1 p.2) ∧
    Continuous (fun p : KPCuspCharts.Coordinates F => deriv (radialCoefficient F W p.1) p.2) ∧
    ∀ c : KPCuspCharts.Cross F, Differentiable ℝ (radialCoefficient F W c)
  set R : KPCuspCharts.Coordinates F → ℝ := fun p =>
    radialCoefficient F W p.1 p.2 with hRdef
  have hW : ContDiff ℝ (⊤ : ℕ∞) W := cutoffScalarFlux_smooth _ u hu a ha
  have hWchart : ContDiff ℝ (⊤ : ℕ∞) (fun p : KPCuspCharts.Coordinates F =>
      W (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))) :=
    hW.comp chart_smooth
  have hR : ContDiff ℝ (⊤ : ℕ∞) R := by
    have hfun : R = fun p : KPCuspCharts.Coordinates F =>
        (∑ i : Fin (KPCuspLogShape.dimension F),
          (W (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p)) i 0).re) /
          (KPCuspLogShape.dimension F : ℝ) := by
      rw [hRdef]
      funext p
      simp [radialCoefficient]
    rw [hfun]
    apply ContDiff.div_const
    apply ContDiff.sum
    intro i _
    exact Complex.reCLM.contDiff.comp (contDiff_pi.mp (contDiff_pi.mp hWchart i) 0)
  refine ⟨hR.continuous, ?_, ?_⟩
  · have hderiv : (fun p : KPCuspCharts.Coordinates F =>
        deriv (radialCoefficient F W p.1) p.2) =
        fun p => fderiv ℝ R p (ContinuousLinearMap.inr ℝ (KPCuspCharts.Cross F) ℝ 1) := by
      funext p
      have hg : HasFDerivAt (fun t : ℝ => (p.1, t))
          (ContinuousLinearMap.inr ℝ (KPCuspCharts.Cross F) ℝ) p.2 :=
        hasFDerivAt_prodMk_right p.1 p.2
      have hcomp : HasFDerivAt (R ∘ (fun t : ℝ => (p.1, t)))
          ((fderiv ℝ R p).comp (ContinuousLinearMap.inr ℝ (KPCuspCharts.Cross F) ℝ)) p.2 :=
        (hR.differentiable (by simp) p).hasFDerivAt.comp p.2 hg
      have hfun2 : (R ∘ (fun t : ℝ => (p.1, t))) =
          radialCoefficient F W p.1 := by
        funext t
        rw [Function.comp_apply, hRdef]
      have h1 : deriv (radialCoefficient F W p.1) p.2
          = (fderiv ℝ R p) (ContinuousLinearMap.inr ℝ (KPCuspCharts.Cross F) ℝ 1) := by
        rw [← fderiv_apply_one_eq_deriv, ← hfun2, hcomp.fderiv]
        rfl
      exact h1
    rw [hderiv]
    exact (hR.continuous_fderiv (by simp)).clm_apply continuous_const
  · intro c
    have hc : (radialCoefficient F W c) = R ∘ (fun t : ℝ => (c, t)) := by
      funext t
      rw [Function.comp_apply, hRdef]
    rw [hc]
    exact (hR.differentiable (by simp)).comp (by fun_prop)

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice

end

end

section

noncomputable section
open MeasureTheory
open scoped Topology

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice

theorem finite_measure_integrable_deriv_of_compact_bounds
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ → ℝ)
    (hf : ∀ t, AEStronglyMeasurable (fun x => f x t) μ)
    (hdf : ∀ t, AEStronglyMeasurable (fun x => deriv (f x) t) μ)
    (hdiff : ∀ x, Differentiable ℝ (f x))
    (hbound : ∀ r s : ℝ, ∃ C : ℝ, ∀ x t, t ∈ Set.Icc r s →
      ‖f x t‖ ≤ C ∧ ‖deriv (f x) t‖ ≤ C)
    (t : ℝ) :
    Integrable (fun x => f x t) μ ∧
    Integrable (fun x => deriv (f x) t) μ ∧
    (∫ x, deriv (f x) t ∂μ) = deriv (fun v => ∫ x, f x v ∂μ) t := by
  obtain ⟨C, hC⟩ := hbound (t - 1) (t + 1)
  have ht : t ∈ Set.Icc (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hint_f : Integrable (fun x => f x t) μ :=
    Integrable.of_bound (hf t) C (Filter.Eventually.of_forall fun x => (hC x t ht).1)
  obtain ⟨hint_d, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun v (x : X) => f x v) (F' := fun v (x : X) => deriv (f x) v)
    (x₀ := t) (s := Set.Icc (t - 1) (t + 1)) (bound := fun _ => C)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun v => hf v)
    hint_f
    (hdf t)
    (Filter.Eventually.of_forall fun a => fun v hv => (hC a v hv).2)
    (integrable_const C)
    (Filter.Eventually.of_forall fun a => fun v _ => (hdiff a v).hasDerivAt)
  exact ⟨hint_f, hint_d, hderiv.deriv.symm⟩

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical Topology

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice
open KPMeanZeroWeightedEnergy HyperbolicChart

 def archL (d : ℕ) : Space d →L[ℝ] KPArch.Space d :=
  LinearMap.toContinuousLinearMap {
    toFun := arch d
    map_add' := by intro x y; ext i <;> simp [arch, Complex.add_re, Complex.add_im]; rfl
    map_smul' := by intro a x; ext i : 1; apply Prod.ext <;> simp [arch, Complex.real_smul]; apply Complex.ext <;> simp }

private lemma arch_real' (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  ext i <;> simp [real, arch]

private lemma continuous_meanHeight (d : ℕ) : Continuous (KPCuspLogShape.meanHeight d) := by
  unfold KPCuspLogShape.meanHeight
  fun_prop

private lemma radialCoefficient_cutoff_eq
    {F : Type} [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ) (a : ℝ → ℝ)
    (c : KPCuspCharts.Cross F) (t : ℝ) :
    radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c t =
      a t * radialCoefficient F (scalarDifferential (KPCuspLogShape.dimension F) u) c t := by
  simp only [radialCoefficient, cutoffScalarFlux, arch_real', KPCuspCharts.toArch_meanHeight F hd,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← Finset.mul_sum]
  ring

set_option maxHeartbeats 600000 in
private lemma radialCoefficient_scalarDifferential_eq
    {F : Type} [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F) {T : ℝ}
    (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (c : KPCuspCharts.Cross F) (t : ℝ) (ht : T < t) :
    radialCoefficient F (scalarDifferential (KPCuspLogShape.dimension F) u) c t =
      (deriv (fun s => (u (KPCuspCharts.toArch F (c,s)) : ℂ)) t).re /
        (KPCuspLogShape.dimension F : ℝ) := by
  let d := KPCuspLogShape.dimension F
  let x := real d (KPCuspCharts.toArch F (c,t))
  let v : Space d := ∑ i : Fin d, coordinateVector d i 2
  have hv (j : Fin d × Fin 3) : v j = if j.2 = 2 then 1 else 0 := by
    simp only [v, map_sum, coordinateVector, WithLp.ofLp_toLp]
    by_cases h : j.2 = 2
    · simp [Prod.ext_iff, h, eq_comm]
    · simp [Prod.ext_iff, h]
  have hcurve : (fun s => real d (KPCuspCharts.toArch F (c,s))) =
      fun s => real d (KPCuspCharts.toArch F (c,0)) + s • v := by
    funext s
    ext j
    rcases j with ⟨i,k⟩
    fin_cases k <;> simp [real, KPCuspCharts.toArch, hv, PiLp.add_apply, PiLp.smul_apply, add_comm]
  have hc : HasDerivAt (fun s => real d (KPCuspCharts.toArch F (c,s))) v t := by
    rw [hcurve]
    simpa using ((hasDerivAt_id t).smul_const v).const_add
      (real d (KPCuspCharts.toArch F (c,0)))
  have huAt : ContDiffAt ℝ (⊤ : ℕ∞) u (KPCuspCharts.toArch F (c,t)) :=
    hu.contDiffAt ((isOpen_lt continuous_const (continuous_meanHeight d)).mem_nhds
      (by change T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) _; rwa [KPCuspCharts.toArch_meanHeight F hd]))
  have hf : HasFDerivAt (fun q => (u (arch d q) : ℂ))
      (fderiv ℝ (fun q => (u (arch d q) : ℂ)) x) x := by
    apply DifferentiableAt.hasFDerivAt
    apply (Complex.ofRealCLM.differentiableAt).comp
    have hdAt : DifferentiableAt ℝ u (arch d x) := by
      simpa only [x, arch_real'] using huAt.differentiableAt (by simp)
    exact hdAt.comp x (archL d).differentiableAt
  have hcomp := hf.comp_hasDerivAt t hc
  have heq : (fun s => (u (arch d (real d (KPCuspCharts.toArch F (c,s)))) : ℂ)) =
      (fun s => (u (KPCuspCharts.toArch F (c,s)) : ℂ)) := by
    funext s; rw [arch_real']
  change HasDerivAt (fun s => (u (arch d (real d (KPCuspCharts.toArch F (c,s)))) : ℂ))
    ((fderiv ℝ (fun q => (u (arch d q) : ℂ)) x) v) t at hcomp
  rw [heq] at hcomp
  rw [hcomp.deriv]
  simp only [radialCoefficient, scalarDifferential, differential, Matrix.cons_val_zero,
    coordinateDerivative, v, map_sum, x, d]
  simp only [← Complex.reCLM_apply, map_sum]

private lemma bounded_on_height_interval
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (f : KPCuspCharts.Coordinates F → ℝ) (hf : Continuous f)
    (hi : ∀ p q, KPCuspCharts.totalRelation F S p q → f p = f q)
    (r s : ℝ) : ∃ C : ℝ, ∀ c t, t ∈ Set.Icc r s → ‖f (c,t)‖ ≤ C := by
  let d : KPCuspCharts.TotalQuotient F S → ℝ := Quotient.lift f hi
  have hd : Continuous d := Continuous.quotient_lift hf hi
  let g : KPCuspCharts.CrossQuotient F S × Set.Icc r s → ℝ :=
    fun p => d (G.radialPresentation (p.1, p.2.val))
  have hg : Continuous g := hd.comp (G.radialPresentation.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  letI := G.compact_cross
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, ?_⟩
  intro c t ht
  have hx := hC (Quotient.mk _ c, ⟨t,ht⟩) (Set.mem_univ _)
  simpa [g, G.radialPresentation_formula, d] using hx

theorem cutoff_radialCoefficient_compact_height_bound
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) (r s : ℝ) :
    ∃ C : ℝ, ∀ (c : KPCuspCharts.Cross F) (v : ℝ), v ∈ Set.Icc r s →
      ‖radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c v‖ ≤ C ∧
      ‖deriv (radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c)
        v‖ ≤ C := by
  let d := KPCuspLogShape.dimension F
  let W := cutoffScalarFlux d u a
  let R : KPCuspCharts.Cross F → ℝ → ℝ := radialCoefficient F W
  have hcross : ∀ c₁ c₂, KPCuspCharts.crossRelation F S c₁ c₂ → R c₁ = R c₂ := by
    intro c₁ c₂ hrel
    funext t
    have hfactor := radialCoefficient_cutoff_eq G.positive_dimension u a
    change radialCoefficient F (cutoffScalarFlux d u a) c₁ t =
      radialCoefficient F (cutoffScalarFlux d u a) c₂ t
    rw [hfactor, hfactor]
    by_cases ht : T < t
    · have heq : (fun v => (u (KPCuspCharts.toArch F (c₁,v)) : ℂ)) =ᶠ[nhds t]
          (fun v => (u (KPCuspCharts.toArch F (c₂,v)) : ℂ)) := by
        filter_upwards [Ioi_mem_nhds ht] with v hv
        have he := hinv ⟨(c₁,v),hv⟩ ⟨(c₂,v),hv⟩
          ((KPCuspCharts.highRelation_product F hF S D T _ _).mpr ⟨hrel,rfl⟩)
        exact congrArg (fun x : ℝ => (x : ℂ)) he
      rw [radialCoefficient_scalarDifferential_eq G.positive_dimension u hu c₁ t ht,
        radialCoefficient_scalarDifferential_eq G.positive_dimension u hu c₂ t ht,
        heq.deriv_eq]
    · have ha0 : a t = 0 := by
        by_contra hn
        exact ht (ha.2.2 (subset_tsupport a hn))
      simp only [ha0, zero_mul]
  have hRi : ∀ p q, KPCuspCharts.totalRelation F S p q →
      R p.1 p.2 = R q.1 q.2 := by
    intro p q hpq
    obtain ⟨hc, ht⟩ := (KPCuspCharts.totalRelation_product F hF S D p q).mp hpq
    rw [hcross p.1 q.1 hc, ht]
  have hDi : ∀ p q, KPCuspCharts.totalRelation F S p q →
      deriv (R p.1) p.2 = deriv (R q.1) q.2 := by
    intro p q hpq
    obtain ⟨hc, ht⟩ := (KPCuspCharts.totalRelation_product F hF S D p q).mp hpq
    rw [hcross p.1 q.1 hc, ht]
  obtain ⟨hR, hD, _⟩ := cutoff_radialCoefficient_regular u hu a ha
  obtain ⟨C₁, hC₁⟩ := bounded_on_height_interval G (fun p => R p.1 p.2) hR hRi r s
  obtain ⟨C₂, hC₂⟩ := bounded_on_height_interval G (fun p => deriv (R p.1) p.2) hD hDi r s
  refine ⟨max C₁ C₂, ?_⟩
  intro c v hv
  exact ⟨(hC₁ c v hv).trans (le_max_left _ _), (hC₂ c v hv).trans (le_max_right _ _)⟩

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical Topology

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice
open KPMeanZeroWeightedEnergy HyperbolicChart

theorem cutoff_radialCoefficient_integrable_deriv
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) (t : ℝ) :
    Integrable (fun c =>
      radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c t)
      ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain) ∧
    Integrable (fun c =>
      deriv (radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c) t)
      ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain) ∧
    (∫ c : KPCuspCharts.Cross F,
      deriv (radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c) t
      ∂((volume.prod G.shapeMeasure).restrict G.fundamentalDomain)) =
      deriv (radialMean G (cutoffScalarFlux (KPCuspLogShape.dimension F) u a)) t := by
  let μ := (volume.prod G.shapeMeasure).restrict G.fundamentalDomain
  have hfinite : IsFiniteMeasure μ := by
    letI := G.finite_sectionMeasure
    constructor
    have h := measure_lt_top G.sectionMeasure Set.univ
    rw [G.sectionMeasure_formula,
      Measure.map_apply measurable_quotient_mk'' MeasurableSet.univ] at h
    simpa [μ] using h
  letI := hfinite
  obtain ⟨hc, hdc, hd⟩ := cutoff_radialCoefficient_regular (F := F) u hu a ha
  have hc_slice (v : ℝ) : Continuous (fun c : KPCuspCharts.Cross F =>
      radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c v) :=
    hc.comp (f := fun c : KPCuspCharts.Cross F => (c, v))
      (continuous_id.prodMk continuous_const)
  have hdc_slice (v : ℝ) : Continuous (fun c : KPCuspCharts.Cross F =>
      deriv (radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c)
        v) := hdc.comp (f := fun c : KPCuspCharts.Cross F => (c, v))
      (continuous_id.prodMk continuous_const)
  exact finite_measure_integrable_deriv_of_compact_bounds μ
      (radialCoefficient F (cutoffScalarFlux (KPCuspLogShape.dimension F) u a))
      (fun v => (hc_slice v).aestronglyMeasurable)
      (fun v => (hdc_slice v).aestronglyMeasurable) hd
      (cutoff_radialCoefficient_compact_height_bound G u hu hinv a ha) t

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical Topology

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration
open KPMeanZeroWeightedEnergy HyperbolicChart

theorem cutoff_scalar_codifferential_slice
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) (t : ℝ) :
    (∫ c : KPCuspCharts.Cross F,
      (codifferential (KPCuspLogShape.dimension F)
        (cutoffScalarFlux (KPCuspLogShape.dimension F) u a)
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, t)))).re
      ∂((volume.prod G.shapeMeasure).restrict G.fundamentalDomain)) =
    -deriv (radialMean G (cutoffScalarFlux (KPCuspLogShape.dimension F) u a)) t +
      2 * (KPCuspLogShape.dimension F : ℝ) *
        radialMean G (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) t := by
  obtain ⟨hR, hR', hderiv⟩ :=
    Slice.cutoff_radialCoefficient_integrable_deriv G u hu hinv a ha t
  obtain ⟨hTan, hzero⟩ :=
    Slice.cutoff_tangentialDivergence_integrable_integral_zero G u hu hinv a ha t
  calc
    _ = ∫ c : KPCuspCharts.Cross F,
        (-deriv (Slice.radialCoefficient F
          (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c) t +
          2 * (KPCuspLogShape.dimension F : ℝ) *
            Slice.radialCoefficient F
              (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c t -
          Slice.tangentialDivergence F
            (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c t)
        ∂((volume.prod G.shapeMeasure).restrict G.fundamentalDomain) := by
      apply integral_congr_ae
      filter_upwards [] with c
      exact Slice.cutoff_scalar_codifferential_pointwise
        G.positive_dimension u hu a ha c t
    _ = _ := by
      have hneg : Integrable (fun c =>
          -deriv (Slice.radialCoefficient F
            (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c) t)
          ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain) := hR'.neg
      have hmul : Integrable (fun c => 2 * (KPCuspLogShape.dimension F : ℝ) *
          Slice.radialCoefficient F
            (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c t)
          ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain) := hR.const_mul _
      have hadd : Integrable (fun c =>
          -deriv (Slice.radialCoefficient F
            (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c) t +
            2 * (KPCuspLogShape.dimension F : ℝ) *
              Slice.radialCoefficient F
                (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c t)
          ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain) := hneg.add hmul
      rw [integral_sub hadd hTan, integral_add hneg hmul, integral_neg,
        integral_const_mul, hderiv, hzero, sub_zero]
      rfl

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration

end

end

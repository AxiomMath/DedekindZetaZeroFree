module

public import DedekindZetaZeroFree.Analysis.Sobolev.WeightedCovariant.CoordinateData

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPCompactInteriorH1

open MeasureTheory TopologicalSpace Filter
open scoped Topology ContDiff

private theorem locallyL2_of_memLp {n r : ℕ} {Ω : Opens (E n)}
    {f : E n → V r} (hf : MemLp f 2 (volume.restrict (Ω : Set (E n)))) :
    LocallyL2 Ω f := by
  refine ⟨hf.aestronglyMeasurable, fun L _ hL => ?_⟩
  exact hf.mono_measure (Measure.restrict_mono hL le_rfl)

private theorem locallyL2_component_integrable {n r : ℕ} {Ω : Opens (E n)}
    {f : E n → V r} (hf : LocallyL2 Ω f) (a : Fin r) :
    LocallyIntegrableOn (fun x => (f x) a) (Ω : Set (E n))
      (volume.restrict (Ω : Set (E n))) := by
  rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed]
  intro k hk hkc
  haveI : IsFiniteMeasure (volume.restrict k) :=
    isFiniteMeasure_restrict.2 hkc.measure_ne_top
  have hi := (EuclideanSpace.proj a : V r →L[ℂ] ℂ).integrable_comp
    ((hf.2 k hkc hk).integrable (by norm_num))
  show Integrable _ ((volume.restrict (Ω : Set (E n))).restrict k)
  rw [Measure.restrict_restrict hkc.measurableSet, Set.inter_eq_left.mpr hk]
  simpa only [Function.comp_apply, EuclideanSpace.coe_proj] using hi

private theorem partial_continuous {n : ℕ} {ψ : E n → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (j : Fin n) : Continuous (coordinatePartial j ψ) := by
  exact (hψ.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem partial_compact {n : ℕ} {ψ : E n → ℂ}
    (hψ : HasCompactSupport ψ) (j : Fin n) : HasCompactSupport (coordinatePartial j ψ) :=
  hψ.fderiv_apply ℝ (coordinateDirection j)

private theorem pairing_tendsto {n r : ℕ} (μ : Measure (E n))
    (fm : ℕ → E n → V r) (f : E n → V r)
    (hfm : ∀ m, MemLp (fm m) 2 μ) (hf : MemLp f 2 μ)
    (hlim : Tendsto (fun m => eLpNorm (fm m - f) 2 μ) atTop (𝓝 0))
    (ψ : E n → ℂ) (hψ : MemLp ψ 2 μ) (a : Fin r) :
    Tendsto (fun m => ∫ x, (fm m x) a * ψ x ∂μ) atTop
      (𝓝 (∫ x, (f x) a * ψ x ∂μ)) := by
  let P := (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 2 2
  let A := (EuclideanSpace.proj a : V r →L[ℂ] ℂ).compLpL 2 μ
  have ht : Tendsto (fun m => (hfm m).toLp (fm m)) atTop (𝓝 (hf.toLp f)) := by
    apply tendsto_iff_edist_tendsto_0.mpr
    simpa only [Lp.edist_toLp_toLp] using hlim
  have heq : ∀ (u : E n → V r) (hu : MemLp u 2 μ),
      P (A (hu.toLp u)) (hψ.toLp ψ) = ∫ x, (u x) a * ψ x ∂μ := by
    intro u hu
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [(EuclideanSpace.proj a : V r →L[ℂ] ℂ).coeFn_compLpL (p := 2) (μ := μ) (hu.toLp u),
      hu.coeFn_toLp, hψ.coeFn_toLp] with x hx hu' hψ'
    change (A (hu.toLp u)) x = _ at hx
    simp only [ContinuousLinearMap.mul_apply', hx, hu', hψ', EuclideanSpace.coe_proj]
  have ht' := ((P.flip (hψ.toLp ψ)).continuous.tendsto _).comp
    (A.continuous.tendsto _ |>.comp ht)
  change Tendsto (fun m => P (A ((hfm m).toLp (fm m))) (hψ.toLp ψ))
    atTop (𝓝 (P (A (hf.toLp f)) (hψ.toLp ψ))) at ht'
  simpa only [heq] using ht'

theorem weakFirst_of_l2_limit {n r : ℕ} (Ω : Opens (E n))
    (fm : ℕ → E n → V r) (f : E n → V r)
    (gm : ℕ → Fin n → E n → V r) (q : Fin n → E n → V r)
    (hfm : ∀ m, MemLp (fm m) 2 (volume.restrict (Ω : Set (E n))))
    (hf : MemLp f 2 (volume.restrict (Ω : Set (E n))))
    (hgm : ∀ m j, MemLp (gm m j) 2 (volume.restrict (Ω : Set (E n))))
    (hq : ∀ j, MemLp (q j) 2 (volume.restrict (Ω : Set (E n))))
    (hweak : ∀ m, WeakFirst Ω (fm m) (gm m))
    (hf_limit : Tendsto
      (fun m => eLpNorm (fm m - f) 2 (volume.restrict (Ω : Set (E n))))
      atTop (𝓝 0))
    (hg_limit : ∀ j, Tendsto
      (fun m => eLpNorm (gm m j - q j) 2 (volume.restrict (Ω : Set (E n))))
      atTop (𝓝 0)) :
    WeakFirst Ω f q := by
  refine ⟨locallyL2_of_memLp hf, fun j => locallyL2_of_memLp (hq j), ?_⟩
  intro j ψ a
  have ht := pairing_tendsto (volume.restrict (Ω : Set (E n))) fm f hfm hf
    hf_limit (coordinatePartial j ψ)
    ((partial_continuous ψ.contDiff j).memLp_of_hasCompactSupport
      (partial_compact ψ.hasCompactSupport j)) a
  have ht' := (pairing_tendsto (volume.restrict (Ω : Set (E n)))
    (fun m => gm m j) (q j) (fun m => hgm m j) (hq j) (hg_limit j) ψ
    (ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport) a).neg
  exact tendsto_nhds_unique ht (ht'.congr' (Eventually.of_forall
    (fun m => ((hweak m).weak_identity j ψ a).symm)))

theorem WeakFirst.derivative_ae_eq {n r : ℕ} {Ω : Opens (E n)}
    {f : E n → V r} {q g : Fin n → E n → V r}
    (hq : WeakFirst Ω f q) (hg : WeakFirst Ω f g) :
    ∀ j, q j =ᵐ[volume.restrict (Ω : Set (E n))] g j := by
  intro j
  have hcomp : ∀ a : Fin r, ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      (q j x) a = (g j x) a := by
    intro a
    have hqi := locallyL2_component_integrable (hq.derivative_locallyL2 j) a
    have hgi := locallyL2_component_integrable (hg.derivative_locallyL2 j) a
    have hz : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
        x ∈ (Ω : Set (E n)) → (q j x) a - (g j x) a = 0 := by
      refine Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hqi.sub hgi) ?_
      intro φ hφ hφc hφs
      have hcast : ContDiff ℝ ∞ (fun x => (φ x : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp hφ
      have hsupp : tsupport (fun x => (φ x : ℂ)) = tsupport φ := by
        unfold tsupport
        congr 1
        ext x
        simp
      let ψ : TestFunction Ω ℂ ⊤ :=
        ⟨fun x => (φ x : ℂ), hcast, by change IsCompact _; rw [hsupp]; exact hφc,
          hsupp ▸ hφs⟩
      let ψR : TestFunction Ω ℝ ⊤ := ⟨φ, hφ, hφc, hφs⟩
      have heq : (∫ x in (Ω : Set (E n)), (q j x) a * ψ x) =
          ∫ x in (Ω : Set (E n)), (g j x) a * ψ x := by
        exact neg_injective ((hq.weak_identity j ψ a).symm.trans
          (hg.weak_identity j ψ a))
      have heq' : (∫ x in (Ω : Set (E n)), φ x • (q j x) a) =
          ∫ x in (Ω : Set (E n)), φ x • (g j x) a := by
        simpa only [show (fun x => ψ x) = (fun x => (φ x : ℂ)) from rfl,
          Complex.real_smul, mul_comm] using heq
      change (∫ x in (Ω : Set (E n)), ψR x • ((q j x) a - (g j x) a)) = 0
      simp only [smul_sub]
      rw [integral_sub (ψR.integrable_smul hqi) (ψR.integrable_smul hgi)]
      change (∫ x in (Ω : Set (E n)), φ x • (q j x) a) -
        (∫ x in (Ω : Set (E n)), φ x • (g j x) a) = 0
      rw [heq', sub_self]
    filter_upwards [hz, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    exact sub_eq_zero.mp (hx hxΩ)
  filter_upwards [Filter.eventually_all.mpr hcomp] with x hx
  ext a
  exact hx a

private theorem smooth_derivative_memLp {n r : ℕ} {u : E n → V r}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (j : Fin n)
    (S : Set (E n)) :
    MemLp (fun x => fderiv ℝ u x (coordinateDirection j)) 2 (volume.restrict S) := by
  exact ((hu.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hc.fderiv_apply ℝ (coordinateDirection j))

theorem weakFirst_smooth_compactSupport {n r : ℕ} (Ω : Opens (E n))
    (u : E n → V r) (hu : ContDiff ℝ ∞ u)
    (hu_compact : HasCompactSupport u)
    (hu_support : tsupport u ⊆ (Ω : Set (E n))) :
    WeakFirst Ω u (fun j x => fderiv ℝ u x (coordinateDirection j)) := by
  refine ⟨locallyL2_of_memLp (hu.continuous.memLp_of_hasCompactSupport hu_compact),
    fun j => locallyL2_of_memLp (smooth_derivative_memLp hu hu_compact j _), ?_⟩
  intro j ψ a
  let ua : E n → ℂ := fun x => (u x) a
  have hua : ContDiff ℝ ∞ ua :=
    (EuclideanSpace.proj a : V r →L[ℂ] ℂ).restrictScalars ℝ |>.contDiff.comp hu
  have huac : HasCompactSupport ua :=
    hu_compact.comp_left (show (EuclideanSpace.proj a : V r →L[ℂ] ℂ) 0 = 0 by simp)
  have hdua : ∀ x, fderiv ℝ ua x (coordinateDirection j) =
      (fderiv ℝ u x (coordinateDirection j)) a := by
    intro x
    have hh := ((EuclideanSpace.proj a : V r →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp x
      ((hu.differentiable (by simp)).differentiableAt.hasFDerivAt)
    exact congrArg (fun T => T (coordinateDirection j)) hh.fderiv
  have hduac : HasCompactSupport (fun x => fderiv ℝ ua x (coordinateDirection j)) :=
    huac.fderiv_apply ℝ (coordinateDirection j)
  have hdu : Continuous (fun x => fderiv ℝ ua x (coordinateDirection j)) :=
    (hua.continuous_fderiv (by simp)).clm_apply continuous_const
  have hp := partial_continuous ψ.contDiff j
  have hpc := partial_compact ψ.hasCompactSupport j
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (E n))) (v := coordinateDirection j)
    ((hdu.mul ψ.continuous).integrable_of_hasCompactSupport hduac.mul_right)
    ((hua.continuous.mul hp).integrable_of_hasCompactSupport huac.mul_right)
    ((hua.continuous.mul ψ.continuous).integrable_of_hasCompactSupport huac.mul_right)
    (fun x _ => (hua.differentiable (by simp)).differentiableAt)
    (fun x _ => (ψ.contDiff.differentiable (by simp)).differentiableAt)
  have hleft : (∫ x in (Ω : Set (E n)), ua x * coordinatePartial j ψ x) =
      ∫ x, ua x * coordinatePartial j ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : ua x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hh => hx (hu_support ((tsupport_comp_subset
        (g := (EuclideanSpace.proj a : V r →L[ℂ] ℂ)) (by simp) u) hh)))
    simp [hz]
  have hright : (∫ x in (Ω : Set (E n)), fderiv ℝ ua x (coordinateDirection j) * ψ x) =
      ∫ x, fderiv ℝ ua x (coordinateDirection j) * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hh => hx (ψ.tsupport_subset hh))
    simp [hz]
  change (∫ x in (Ω : Set (E n)), ua x * coordinatePartial j ψ x) = _
  simp_rw [← hdua]
  rw [hleft, hright]
  exact hibp

theorem weakFirst_of_smooth_compactSupport_l2_limit {n r : ℕ}
    (Ω : Opens (E n)) (fm : ℕ → E n → V r) (f : E n → V r)
    (q : Fin n → E n → V r)
    (hfm_smooth : ∀ m, ContDiff ℝ ∞ (fm m))
    (hfm_compact : ∀ m, HasCompactSupport (fm m))
    (hfm_support : ∀ m, tsupport (fm m) ⊆ (Ω : Set (E n)))
    (hf : MemLp f 2 (volume.restrict (Ω : Set (E n))))
    (hq : ∀ j, MemLp (q j) 2 (volume.restrict (Ω : Set (E n))))
    (hf_limit : Tendsto
      (fun m => eLpNorm (fm m - f) 2 (volume.restrict (Ω : Set (E n))))
      atTop (𝓝 0))
    (hg_limit : ∀ j, Tendsto
      (fun m => eLpNorm
        ((fun x => fderiv ℝ (fm m) x (coordinateDirection j)) - q j)
        2 (volume.restrict (Ω : Set (E n)))) atTop (𝓝 0)) :
    WeakFirst Ω f q := by
  apply weakFirst_of_l2_limit Ω fm f
    (fun m j x => fderiv ℝ (fm m) x (coordinateDirection j)) q
    (fun m => (hfm_smooth m).continuous.memLp_of_hasCompactSupport (hfm_compact m)) hf
    (fun m j => smooth_derivative_memLp (hfm_smooth m) (hfm_compact m) j _) hq
    (fun m => weakFirst_smooth_compactSupport Ω (fm m) (hfm_smooth m)
      (hfm_compact m) (hfm_support m)) hf_limit hg_limit

end DedekindZetaZeroFree.KPCompactInteriorH1

end

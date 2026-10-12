module

public import DedekindZetaZeroFree.Analysis.Sobolev.WeightedCovariant.CoordinateData
public import DedekindZetaZeroFree.Analysis.SmoothFunctions.CompactInteriorCutoffs

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPCompactInteriorH1

open MeasureTheory TopologicalSpace Filter
open scoped ContDiff Topology

theorem weakFirst_zero_on_open {n r : ℕ} {Ω W : Opens (E n)}
    {f : E n → V r} {g : Fin n → E n → V r}
    (hfg : WeakFirst Ω f g) (hWΩ : (W : Set (E n)) ⊆ (Ω : Set (E n)))
    (hf : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (W : Set (E n)) → f x = 0) :
    ∀ j, ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (W : Set (E n)) → g j x = 0 := by
  intro j
  have hcomp : ∀ a : Fin r, ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (W : Set (E n)) → (g j x) a = 0 := by
    intro a
    refine W.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (f := fun x => (g j x) a) ?_ ?_
    · rw [locallyIntegrableOn_iff W.isOpen.isLocallyClosed]
      intro k hkW hkc
      have hkΩ : k ⊆ (Ω : Set (E n)) := hkW.trans hWΩ
      have hmlp : MemLp (g j) 2 (volume.restrict k) :=
        (hfg.derivative_locallyL2 j).2 k hkc hkΩ
      haveI : IsFiniteMeasure (volume.restrict k) :=
        isFiniteMeasure_restrict.2 hkc.measure_ne_top
      have hint : Integrable (g j) (volume.restrict k) := hmlp.integrable (by norm_num)
      have hproj := (EuclideanSpace.proj a : V r →L[ℂ] ℂ).integrable_comp hint
      show Integrable (fun x => (g j x) a)
        ((volume.restrict (Ω : Set (E n))).restrict k)
      rw [Measure.restrict_restrict hkc.measurableSet, Set.inter_eq_left.mpr hkΩ]
      simpa only [Function.comp_apply, EuclideanSpace.coe_proj] using hproj
    · intro g0 hg0 hg0c hg0s
      have hcast : ContDiff ℝ ∞ (fun x => (g0 x : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp hg0
      have hsupp : tsupport (fun x => (g0 x : ℂ)) = tsupport g0 := by
        unfold tsupport
        congr 1
        ext x
        simp
      let ψ : TestFunction Ω ℂ ⊤ :=
        ⟨fun x => (g0 x : ℂ), hcast, by change IsCompact _; rw [hsupp]; exact hg0c,
          fun x hx => hWΩ (hg0s (hsupp ▸ hx))⟩
      have hw := hfg.weak_identity j ψ a
      have hleft : (∫ x in (Ω : Set (E n)),
          (f x) a * coordinatePartial j (fun y => ψ y) x) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hf] with x hx
        by_cases hxW : x ∈ (W : Set (E n))
        · rw [hx hxW]
          simp
        · have hxnot : x ∉ tsupport (fun y => (g0 y : ℂ)) :=
            fun hh => hxW (hg0s (hsupp ▸ hh))
          have hxnot' : x ∉ tsupport (fun y => ψ y) := hxnot
          have hfd : fderiv ℝ (fun y => ψ y) x = 0 :=
            fderiv_of_notMem_tsupport (𝕜 := ℝ) hxnot'
          rw [coordinatePartial, hfd]
          simp
      rw [hleft, zero_eq_neg] at hw
      have hgoal : (∫ x, g0 x • (g j x) a ∂(volume.restrict (Ω : Set (E n)))) =
          ∫ x in (Ω : Set (E n)), (g j x) a * ψ x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [show ψ x = (g0 x : ℂ) from rfl, Complex.real_smul, mul_comm]
      rw [hgoal]
      exact hw
  filter_upwards [Filter.eventually_all.mpr hcomp] with x hx
  intro hxW
  ext a
  exact hx a hxW

theorem weakFirst_zero_off_compact {n r : ℕ} {Ω : Opens (E n)}
    {K : Set (E n)} {f : E n → V r} {g : Fin n → E n → V r}
    (hK : IsCompact K) (hKΩ : K ⊆ (Ω : Set (E n)))
    (hfg : WeakFirst Ω f g)
    (hf : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (Ω : Set (E n)) \ K → f x = 0) :
    ∀ j, ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (Ω : Set (E n)) \ K → g j x = 0 := by
  let W : Opens (E n) := ⟨(Ω : Set (E n)) \ K, Ω.isOpen.sdiff hK.isClosed⟩
  have hWΩ : (W : Set (E n)) ⊆ (Ω : Set (E n)) := fun _ hx => hx.1
  exact weakFirst_zero_on_open hfg hWΩ hf

def compactZeroExtension {n r : ℕ} (K : Set (E n)) (f : E n → V r) :
    E n → V r :=
  K.indicator f

private theorem compactZeroExtension_memLp {n r : ℕ} {Ω : Opens (E n)}
    {K : Set (E n)} {f : E n → V r} (hK : IsCompact K)
    (hKΩ : K ⊆ (Ω : Set (E n))) (hf : LocallyL2 Ω f) :
    MemLp (compactZeroExtension K f) 2 volume :=
  (memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet).2 (hf.2 K hK hKΩ)

private theorem compactZeroExtension_ae_eq {n r : ℕ} {Ω : Opens (E n)}
    {K : Set (E n)} {f : E n → V r}
    (hf : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (Ω : Set (E n)) \ K → f x = 0) :
    compactZeroExtension K f =ᵐ[volume.restrict (Ω : Set (E n))] f := by
  filter_upwards [hf, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  by_cases hxK : x ∈ K
  · simp [compactZeroExtension, hxK]
  · simp [compactZeroExtension, hxK, hx ⟨hxΩ, hxK⟩]

theorem compactZeroExtension_properties {n r : ℕ} {Ω : Opens (E n)}
    {K : Set (E n)} {f : E n → V r} {g : Fin n → E n → V r}
    (hK : IsCompact K) (hKΩ : K ⊆ (Ω : Set (E n)))
    (hfg : WeakFirst Ω f g)
    (hf : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (Ω : Set (E n)) \ K → f x = 0) :
    let F := compactZeroExtension K f
    let G := fun j => compactZeroExtension K (g j)
    MemLp F 2 volume ∧
    (∀ j, MemLp (G j) 2 volume) ∧
    Integrable F volume ∧
    (∀ j, Integrable (G j) volume) ∧
    (∀ x, x ∉ K → F x = 0) ∧
    (∀ j x, x ∉ K → G j x = 0) ∧
    tsupport F ⊆ K ∧
    (∀ j, tsupport (G j) ⊆ K) ∧
    F =ᵐ[volume.restrict (Ω : Set (E n))] f ∧
    (∀ j, G j =ᵐ[volume.restrict (Ω : Set (E n))] g j) := by
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_ne_top
  have hFmem : MemLp (compactZeroExtension K f) 2 volume :=
    compactZeroExtension_memLp hK hKΩ hfg.section_locallyL2
  have hGmem : ∀ j, MemLp (compactZeroExtension K (g j)) 2 volume := fun j =>
    compactZeroExtension_memLp hK hKΩ (hfg.derivative_locallyL2 j)
  have hFint : Integrable (compactZeroExtension K f) volume :=
    (integrableOn_iff_integrable_of_support_subset
      (Set.support_indicator_subset : Function.support (compactZeroExtension K f) ⊆ K)).mp
      ((hFmem.mono_measure Measure.restrict_le_self).integrable (by norm_num))
  have hGint : ∀ j, Integrable (compactZeroExtension K (g j)) volume := fun j =>
    (integrableOn_iff_integrable_of_support_subset
      (Set.support_indicator_subset : Function.support (compactZeroExtension K (g j)) ⊆ K)).mp
      (((hGmem j).mono_measure Measure.restrict_le_self).integrable (by norm_num))
  have hFzero : ∀ x, x ∉ K → compactZeroExtension K f x = 0 := fun x hx =>
    Set.indicator_of_notMem hx f
  have hGzero : ∀ j x, x ∉ K → compactZeroExtension K (g j) x = 0 := fun j x hx =>
    Set.indicator_of_notMem hx (g j)
  have hFtsupp : tsupport (compactZeroExtension K f) ⊆ K :=
    closure_minimal Set.support_indicator_subset hK.isClosed
  have hGtsupp : ∀ j, tsupport (compactZeroExtension K (g j)) ⊆ K := fun j =>
    closure_minimal Set.support_indicator_subset hK.isClosed
  have hFae : compactZeroExtension K f =ᵐ[volume.restrict (Ω : Set (E n))] f :=
    compactZeroExtension_ae_eq hf
  have hGae : ∀ j, compactZeroExtension K (g j) =ᵐ[volume.restrict (Ω : Set (E n))] g j :=
    fun j => compactZeroExtension_ae_eq (weakFirst_zero_off_compact hK hKΩ hfg hf j)
  exact ⟨hFmem, hGmem, hFint, hGint, hFzero, hGzero, hFtsupp, hGtsupp, hFae, hGae⟩

theorem compactZeroExtension_weak_identity {n r : ℕ} {Ω : Opens (E n)}
    {K : Set (E n)} {f : E n → V r} {g : Fin n → E n → V r}
    (hK : IsCompact K) (hKΩ : K ⊆ (Ω : Set (E n)))
    (hfg : WeakFirst Ω f g)
    (hf : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (Ω : Set (E n)) \ K → f x = 0)
    (ψ : E n → ℂ) (hψ : ContDiff ℝ ∞ ψ) (j : Fin n) (a : Fin r) :
    Integrable (fun x => (compactZeroExtension K f x) a * coordinatePartial j ψ x)
      volume ∧
    Integrable (fun x => (compactZeroExtension K (g j) x) a * ψ x) volume ∧
    (∫ x, (compactZeroExtension K f x) a * coordinatePartial j ψ x) =
      -(∫ x, (compactZeroExtension K (g j) x) a * ψ x) := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  obtain ⟨η, N, hNopen, hKN, hNΩ, hηsm, hηc, hηts, _hη01, hηN, _hηder, _⟩ :=
    exists_smooth_cutoff hn (Ω : Set (E n)) K Ω.isOpen hK hKΩ
  let ηc : E n → ℂ := fun x => (η x : ℂ)
  have hηc_sm : ContDiff ℝ ∞ ηc := Complex.ofRealCLM.contDiff.comp hηsm
  have hηc_ts : tsupport ηc = tsupport η := by
    unfold tsupport ηc
    congr 1
    ext x
    simp
  have hΨ_sm : ContDiff ℝ ∞ (fun x => ηc x * ψ x) := hηc_sm.mul hψ
  have hηc_c : HasCompactSupport ηc := hηc.comp_left (g := Complex.ofRealCLM) (by simp)
  have hΨ_c : HasCompactSupport (fun x => ηc x * ψ x) :=
    hηc_c.of_isClosed_subset isClosed_closure (closure_mono fun x hx => by
      simp only [Function.mem_support] at hx ⊢
      exact fun h => hx (by rw [h, zero_mul]))
  have hΨ_ts : tsupport (fun x => ηc x * ψ x) ⊆ (Ω : Set (E n)) := by
    refine (tsupport_mul_subset_left (f := ηc) (g := ψ)).trans ?_
    rw [hηc_ts]
    exact hηts
  let Ψ : TestFunction Ω ℂ ⊤ :=
    ⟨fun x => ηc x * ψ x, hΨ_sm, hΨ_c, hΨ_ts⟩
  have hΨeq : ∀ y, Ψ y = (η y : ℂ) * ψ y := fun y => rfl
  have hw := hfg.weak_identity j Ψ a

  have hNmem : ∀ x ∈ K, N ∈ 𝓝 x := fun x hx => hNopen.mem_nhds (hKN hx)
  have hcont : Continuous (coordinatePartial j ψ) := by
    have h1 := hψ.continuous_fderiv_apply (𝕜 := ℝ) (n := ∞) (by simp)
    have h2 : Continuous fun x : E n => (fderiv ℝ ψ x) (coordinateDirection j) :=
      h1.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : E n => coordinateDirection j))
    exact h2

  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_ne_top
  have hFmem : MemLp (compactZeroExtension K f) 2 volume :=
    compactZeroExtension_memLp hK hKΩ hfg.section_locallyL2
  have hGmem : MemLp (compactZeroExtension K (g j)) 2 volume :=
    compactZeroExtension_memLp hK hKΩ (hfg.derivative_locallyL2 j)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hbdd : ∀ᵐ x ∂(volume.restrict K), ‖coordinatePartial j ψ x‖ ≤ C := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hC x hx
  obtain ⟨Cψ, hCψ⟩ := hK.exists_bound_of_continuousOn hψ.continuous.continuousOn
  have hbddψ : ∀ᵐ x ∂(volume.restrict K), ‖ψ x‖ ≤ Cψ := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hCψ x hx
  have hsuppF : Function.support
      (fun x => (compactZeroExtension K f x) a * coordinatePartial j ψ x) ⊆ K := by
    intro x hx
    by_contra hxK
    refine hx ?_
    have h0 : (compactZeroExtension K f x) a = 0 := by
      rw [compactZeroExtension, Set.indicator_of_notMem hxK]
      simp
    show (compactZeroExtension K f x) a * coordinatePartial j ψ x = 0
    rw [h0, zero_mul]
  have hsuppG : Function.support
      (fun x => (compactZeroExtension K (g j) x) a * ψ x) ⊆ K := by
    intro x hx
    by_contra hxK
    refine hx ?_
    have h0 : (compactZeroExtension K (g j) x) a = 0 := by
      rw [compactZeroExtension, Set.indicator_of_notMem hxK]
      simp
    show (compactZeroExtension K (g j) x) a * ψ x = 0
    rw [h0, zero_mul]
  have hintF : Integrable (fun x => (compactZeroExtension K f x) a * coordinatePartial j ψ x)
      volume := by
    refine (integrableOn_iff_integrable_of_support_subset hsuppF).mp ?_
    exact (((EuclideanSpace.proj a : V r →L[ℂ] ℂ).integrable_comp
      ((hFmem.mono_measure Measure.restrict_le_self).integrable (by norm_num))).mul_bdd
        hcont.aestronglyMeasurable hbdd)
  have hintG : Integrable (fun x => (compactZeroExtension K (g j) x) a * ψ x) volume := by
    refine (integrableOn_iff_integrable_of_support_subset hsuppG).mp ?_
    exact (((EuclideanSpace.proj a : V r →L[ℂ] ℂ).integrable_comp
      ((hGmem.mono_measure Measure.restrict_le_self).integrable (by norm_num))).mul_bdd
        hψ.continuous.aestronglyMeasurable hbddψ)

  have hFae : compactZeroExtension K f =ᵐ[volume.restrict (Ω : Set (E n))] f :=
    compactZeroExtension_ae_eq hf
  have hGae : compactZeroExtension K (g j) =ᵐ[volume.restrict (Ω : Set (E n))] g j :=
    compactZeroExtension_ae_eq (weakFirst_zero_off_compact hK hKΩ hfg hf j)
  have hstep1 : (∫ x in (Ω : Set (E n)), (f x) a * coordinatePartial j (fun y => Ψ y) x)
      = ∫ x in (Ω : Set (E n)),
        (compactZeroExtension K f x) a * coordinatePartial j (fun y => Ψ y) x := by
    apply integral_congr_ae
    filter_upwards [hFae] with x hx
    rw [hx]
  have hstep2 : (∫ x in (Ω : Set (E n)),
        (compactZeroExtension K f x) a * coordinatePartial j (fun y => Ψ y) x)
      = ∫ x, (compactZeroExtension K f x) a * coordinatePartial j (fun y => Ψ y) x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [compactZeroExtension, Set.indicator_of_notMem (fun h => hx (hKΩ h))]
    simp
  have hR1 : (∫ x in (Ω : Set (E n)), (g j x) a * Ψ x)
      = ∫ x in (Ω : Set (E n)), (compactZeroExtension K (g j) x) a * Ψ x := by
    apply integral_congr_ae
    filter_upwards [hGae] with x hx
    rw [hx]
  have hR2 : (∫ x in (Ω : Set (E n)), (compactZeroExtension K (g j) x) a * Ψ x)
      = ∫ x, (compactZeroExtension K (g j) x) a * Ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [compactZeroExtension, Set.indicator_of_notMem (fun h => hx (hKΩ h))]
    simp
  have hmain : (∫ x, (compactZeroExtension K f x) a * coordinatePartial j (fun y => Ψ y) x)
      = -(∫ x, (compactZeroExtension K (g j) x) a * Ψ x) := by
    rw [← hstep2, ← hstep1, ← hR2, ← hR1]
    exact hw

  have hfinalF : (∫ x, (compactZeroExtension K f x) a * coordinatePartial j (fun y => Ψ y) x)
      = ∫ x, (compactZeroExtension K f x) a * coordinatePartial j ψ x := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hxK : x ∈ K
    · have hev : (fun y => Ψ y) =ᶠ[𝓝 x] ψ := by
        filter_upwards [hNmem x hxK] with y hy
        rw [hΨeq y, hηN y hy]
        simp
      have hfd : coordinatePartial j (fun y => Ψ y) x = coordinatePartial j ψ x := by
        simp only [coordinatePartial]
        rw [hev.fderiv_eq]
      rw [hfd]
    · rw [compactZeroExtension, Set.indicator_of_notMem hxK]
      simp
  have hfinalG : (∫ x, (compactZeroExtension K (g j) x) a * Ψ x)
      = ∫ x, (compactZeroExtension K (g j) x) a * ψ x := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hxK : x ∈ K
    · rw [hΨeq x, hηN x (hKN hxK)]
      simp
    · rw [compactZeroExtension, Set.indicator_of_notMem hxK]
      simp
  refine ⟨hintF, hintG, ?_⟩
  rw [← hfinalF, ← hfinalG]
  exact hmain

theorem compactZeroExtension_weakFirst {n r : ℕ} {Ω : Opens (E n)}
    {K : Set (E n)} {f : E n → V r} {g : Fin n → E n → V r}
    (hK : IsCompact K) (hKΩ : K ⊆ (Ω : Set (E n)))
    (hfg : WeakFirst Ω f g)
    (hf : ∀ᵐ x ∂volume.restrict (Ω : Set (E n)),
      x ∈ (Ω : Set (E n)) \ K → f x = 0) :
    WeakFirst (⊤ : Opens (E n)) (compactZeroExtension K f)
      (fun j => compactZeroExtension K (g j)) := by
  obtain ⟨hFmem, hGmem, -, -, -, -, -, -, -, -⟩ :=
    compactZeroExtension_properties hK hKΩ hfg hf
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨by simpa only [Opens.coe_top, Measure.restrict_univ] using hFmem.aestronglyMeasurable,
      fun L _ _ => hFmem.mono_measure Measure.restrict_le_self⟩
  · intro j
    exact ⟨by simpa only [Opens.coe_top, Measure.restrict_univ] using (hGmem j).aestronglyMeasurable,
      fun L _ _ => (hGmem j).mono_measure Measure.restrict_le_self⟩
  · intro j ψ a
    have h := compactZeroExtension_weak_identity hK hKΩ hfg hf (fun y => ψ y) ψ.contDiff' j a
    simpa using h.2.2

end DedekindZetaZeroFree.KPCompactInteriorH1

end

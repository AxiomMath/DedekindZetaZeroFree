module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.RadialTests

@[expose] public section

noncomputable section
open MeasureTheory Topology Filter
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.PeriodicLiftHaar

theorem integral_fderiv_eq_zero
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (K : AddSubgroup H)
    (μ : Measure (H ⧸ K)) (hμ : μ.IsAddHaarMeasure)
    (hprob : IsProbabilityMeasure μ) (f : H ⧸ K → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun y : H => f (QuotientAddGroup.mk y)))
    (w : H) :
    (∫ z, fderiv ℝ (fun y : H => f (QuotientAddGroup.mk y))
      (Quotient.out z) w ∂μ) = 0 := by
  letI := hμ
  letI := hprob
  letI : OpensMeasurableSpace (H ⧸ K) :=
    opensMeasurableSpace_iff_forall_measurableSet.mpr fun s hs =>
      measurableSet_quotient.mpr
        ((QuotientAddGroup.continuous_mk (N := K)).isOpen_preimage s hs).measurableSet
  have htrans (a : H ⧸ K) : Measurable (fun x : H ⧸ K => a + x) := by
    apply QuotientAddGroup.measurable_from_quotient.mpr
    have he : (fun x : H => a + QuotientAddGroup.mk x) =
        fun x => QuotientAddGroup.mk (Quotient.out a + x) := by
      funext x
      simp [QuotientAddGroup.mk_add, Quotient.out_eq]
    change Measurable (fun x : H => a + QuotientAddGroup.mk x)
    rw [he]
    exact QuotientAddGroup.measurable_coe.comp (continuous_const.add continuous_id).measurable
  have hc : CompactSpace (H ⧸ K) := by
    by_contra hn
    letI : NoncompactSpace (H ⧸ K) := not_compactSpace_iff.mp hn
    have hm := OpensMeasurableSpace.borel_le (α := H ⧸ K)
    let ν : @Measure (H ⧸ K) (borel (H ⧸ K)) := μ.trim hm
    have hh : ν Set.univ = ⊤ := by
      letI : MeasurableSpace (H ⧸ K) := borel (H ⧸ K)
      letI : BorelSpace (H ⧸ K) := ⟨rfl⟩
      letI : ν.IsOpenPosMeasure := by
        constructor
        intro U hU hne
        rw [trim_measurableSet_eq _ hU.measurableSet]
        exact hμ.open_pos U hU hne
      letI : ν.IsAddLeftInvariant := by
        constructor
        intro a
        apply Measure.ext
        intro s hs
        have hcont : Continuous (fun x : H ⧸ K => a + x) := continuous_const.add continuous_id
        rw [Measure.map_apply hcont.measurable hs]
        rw [trim_measurableSet_eq _ hs, trim_measurableSet_eq _ (hcont.measurable hs)]
        have hmap := congrArg (fun m : @Measure (H ⧸ K) (QuotientAddGroup.measurableSpace K) => m s)
          (hμ.map_add_left_eq_self a)
        rw [Measure.map_apply (htrans a) (hm s hs)] at hmap
        exact hmap
      exact measure_univ_of_isAddLeftInvariant ν
    rw [trim_measurableSet_eq _ MeasurableSet.univ] at hh
    simpa using hh
  letI := hc
  let g : H → ℂ := fun y => f (QuotientAddGroup.mk y)
  let d : H ⧸ K → ℂ := fun z => fderiv ℝ g (Quotient.out z) w
  have hinv (a b : H) (hab : (QuotientAddGroup.mk a : H ⧸ K) = QuotientAddGroup.mk b) :
      fderiv ℝ g a = fderiv ℝ g b := by
    have hh : (QuotientAddGroup.mk (b - a) : H ⧸ K) = 0 := by
      simp [QuotientAddGroup.mk_sub, hab]
    have he : (fun x => g (x + (b - a))) = g := by
      funext x
      simp [g, QuotientAddGroup.mk_add, hh]
    have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := a) (b - a)
    rw [he] at hd
    simpa only [← add_sub_assoc, add_sub_cancel_left] using hd
  have hd (y : H) : d (QuotientAddGroup.mk y) = fderiv ℝ g y w := by
    exact congrArg (fun L : H →L[ℝ] ℂ => L w) (hinv _ _ (Quotient.out_eq _))
  have hdc : Continuous d := by
    apply (QuotientAddGroup.isQuotientMap_mk K).continuous_iff.mpr
    have he : d ∘ QuotientAddGroup.mk = fun y => fderiv ℝ g y w := funext hd
    rw [he]
    exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfc : Continuous f := (QuotientAddGroup.isQuotientMap_mk K).continuous_iff.mpr hf.continuous
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hdc.continuousOn
  let A : ℝ → H ⧸ K → ℂ := fun t z => f (QuotientAddGroup.mk (t • w) + z)
  let A' : ℝ → H ⧸ K → ℂ := fun t z => d (QuotientAddGroup.mk (t • w) + z)
  have htc (a : H ⧸ K) : Continuous (fun z : H ⧸ K => a + z) := by
    apply (QuotientAddGroup.isQuotientMap_mk K).continuous_iff.mpr
    have he : (fun z : H ⧸ K => a + z) ∘ QuotientAddGroup.mk =
        fun x : H => QuotientAddGroup.mk (Quotient.out a + x) := by
      funext x
      simp [Function.comp_def, QuotientAddGroup.mk_add, Quotient.out_eq]
    rw [he]
    exact QuotientAddGroup.continuous_mk.comp (continuous_const.add continuous_id)
  have hAc (t : ℝ) : Continuous (A t) := hfc.comp (htc _)
  have hA'c (t : ℝ) : Continuous (A' t) := hdc.comp (htc _)
  have hder (t : ℝ) (z : H ⧸ K) : HasDerivAt (fun t => A t z) (A' t z) t := by
    have hg := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt (x := t • w + Quotient.out z)
    have hline : HasDerivAt (fun t : ℝ => t • w + Quotient.out z) w t := by
      simpa using ((hasDerivAt_id t).smul_const w).add_const (Quotient.out z)
    have hh := hg.comp_hasDerivAt t hline
    have he : (fun t => A t z) = g ∘ (fun t : ℝ => t • w + Quotient.out z) := by
      funext t
      simp [A, g, Function.comp_def, QuotientAddGroup.mk_add, Quotient.out_eq]
    rw [he]
    have hde : A' t z = fderiv ℝ g (t • w + Quotient.out z) w := by
      simpa [A', QuotientAddGroup.mk_add, Quotient.out_eq] using hd (t • w + Quotient.out z)
    rw [hde]
    exact hh
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := A) (F' := A') (x₀ := (0 : ℝ)) (s := Set.univ) (bound := fun _ => C)
      (by simp) (Eventually.of_forall fun t => (hAc t).aestronglyMeasurable)
      ((hAc 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hA'c 0).aestronglyMeasurable
      (ae_of_all _ fun z t _ => hC _ (Set.mem_univ _)) (integrable_const C)
      (ae_of_all _ fun z t _ => hder t z)
  have he : (fun t => ∫ z, A t z ∂μ) = fun _ : ℝ => ∫ z, f z ∂μ := by
    funext t
    let a : H ⧸ K := QuotientAddGroup.mk (t • w)
    let e : (H ⧸ K) ≃ᵐ (H ⧸ K) := ⟨Equiv.addLeft a, htrans a, htrans (-a)⟩
    have hp : MeasurePreserving e μ μ := ⟨htrans a, hμ.map_add_left_eq_self a⟩
    exact hp.integral_comp e.measurableEmbedding f
  have hz := hi.2
  rw [he] at hz
  have hh := hz.unique (hasDerivAt_const (0 : ℝ) (∫ z, f z ∂μ))
  simpa [A', d, g] using hh

end DedekindZetaZeroFree.PeriodicLiftHaar

end

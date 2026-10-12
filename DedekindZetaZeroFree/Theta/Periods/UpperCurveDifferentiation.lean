module

public import DedekindZetaZeroFree.Theta.Periods.RootDerivativeAutomorphyAndIntegrability

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped NumberField Classical Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem integrand_joint_continuous (f : Functions R) (hf : Continuous f)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g) :
    Continuous (fun p : Group R × KPAdditiveQuotient F =>
      f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out p.2) * p.1) *
        star (adelicTraceQuotientCharacter F p.2 : ℂ)) := by
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  have hc : Continuous (fun p : Group R × KPAdditiveQuotient F =>
      f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out p.2) * p.1)) := by
    apply ((IsOpenQuotientMap.id (X := Group R)).prodMap
      (QuotientAddGroup.isOpenQuotientMap_mk (N := AdeleRing.principalSubgroup (𝓞 F) F))).continuous_comp_iff.mp
    convert hf.comp (((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
      F R.A.zeta12 R.A.primitive_zeta12).comp continuous_snd).mul continuous_fst) using 1
    funext p
    exact integrand_mk R f hr p.2 p.1
  exact hc.mul (continuous_star.comp (continuous_subtype_val.comp
    ((continuous_adelicTraceQuotientCharacter F).comp continuous_snd)))

theorem upperCurve_continuous (w : InfinitePlace F) (b : Bool) : Continuous (upperCurve R w b) := by
  unfold upperCurve
  have he : (fun t : ℝ => KPRationalAdelicSplitting.localAdele F (Sum.inl w)
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm (t : ℂ) *
        upperLieDirection R w b)) = fun t : ℝ =>
    (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm (t : ℂ) *
      upperLieDirection R w b), 0) := rfl
  have hlocal : Continuous (fun t : ℝ => KPRationalAdelicSplitting.localAdele F (Sum.inl w)
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm (t : ℂ) *
        upperLieDirection R w b)) := by
    rw [he]
    apply Continuous.prodMk _ continuous_const
    apply continuous_pi; intro v
    by_cases hv : v = w
    · subst v
      let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)
      have hi : Isometry e := InfinitePlace.Completion.isometry_extensionEmbedding w
      have hs : Isometry e.symm := by
        intro x y
        simpa only [RingEquiv.apply_symm_apply] using (hi (e.symm x) (e.symm y)).symm
      convert ((hs.continuous.comp Complex.continuous_ofReal).mul
        (continuous_const (y := upperLieDirection R w b))) using 1
      funext t; exact Pi.single_eq_same w _
    · simp only [Pi.single_eq_of_ne hv]; exact continuous_const
  exact (KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
    F R.A.zeta12 R.A.primitive_zeta12).comp hlocal

theorem fourier_upperCurve_hasDeriv (dq : Measure (KPAdditiveQuotient F)) (hprob : dq Set.univ = 1)
    (f : Functions R) (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (w : InfinitePlace F) (b : Bool) (g : Group R) :
    HasDerivAt (fun t => fourier R dq f (g * upperCurve R w b t))
      (fourier R dq (upperLieDerivative R w b f) g) 0 := by
  letI : IsProbabilityMeasure dq := ⟨hprob⟩
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  let P : ℝ → KPAdditiveQuotient F → ℂ := fun t q =>
    f ((KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
      upperCurve R w b t) * star (adelicTraceQuotientCharacter F q : ℂ)
  let P' : ℝ → KPAdditiveQuotient F → ℂ := fun t q =>
    upperLieDerivative R w b f
      ((KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        upperCurve R w b t) * star (adelicTraceQuotientCharacter F q : ℂ)
  have hpair : Continuous (fun p : ℝ × KPAdditiveQuotient F => (g * upperCurve R w b p.1, p.2)) :=
    (continuous_const.mul ((upperCurve_continuous R w b).comp continuous_fst)).prodMk continuous_snd
  have hP : Continuous (Function.uncurry P) := by
    convert (integrand_joint_continuous R f hf.1 hr).comp hpair using 1
    funext p; simp only [Function.uncurry, Function.comp_def, P, mul_assoc]
  have hP' : Continuous (Function.uncurry P') := by
    convert (integrand_joint_continuous R _ (upperLieDerivative_smooth R w b f hf).1
      (fun γ => upperLieDerivative_left_invariant R w b f _ (hr γ))).comp hpair using 1
    funext p; simp only [Function.uncurry, Function.comp_def, P', mul_assoc]
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod
    (isCompact_univ : IsCompact (Set.univ : Set (KPAdditiveQuotient F)))).exists_bound_of_continuousOn hP'.continuousOn
  have hd (t : ℝ) (q : KPAdditiveQuotient F) : HasDerivAt (fun s => P s q) (P' t q) t :=
    (upperCurve_hasDerivAt R w b f hf _ t).mul_const _
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := dq) (F := P) (F' := P') (s := Metric.ball (0 : ℝ) 1) (bound := fun _ => C)
    (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
    (Eventually.of_forall (fun t => (hP.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    (by
      have he : P 0 = fun q => f (KPGlobalTorusFunctionData.N F R.A.zeta12
        R.A.primitive_zeta12 (Quotient.out q) * g) * star (adelicTraceQuotientCharacter F q : ℂ) := by
        funext q; simp only [P, upperCurve_zero, mul_one]
      rw [he]; exact fourier_integrable R dq hprob f hf.1 hr g)
    ((hP'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall (fun q t ht => hC (t,q) ⟨Metric.ball_subset_closedBall ht, Set.mem_univ q⟩))
    (integrable_const C) (Eventually.of_forall (fun q t _ => hd t q))
  convert hi.2 using 1
  · funext t; simp only [MomentSources.fourier, P, mul_assoc]
  · simp only [MomentSources.fourier, P', upperCurve_zero, mul_one]

end DedekindZetaZeroFree.RootDerivatives

end

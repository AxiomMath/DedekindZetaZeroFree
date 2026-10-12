module

public import DedekindZetaZeroFree.Eisenstein.Induction.RationalBorelCovariance
public import DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.Data

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.UpperRootLieDerivatives

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources ThetaExpansion
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem smooth_add (f h : Functions R)
    (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f)
    (hh : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 h) :
    KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 (f + h) := by
  obtain ⟨U, hU⟩ := hf.2.2
  obtain ⟨V, hV⟩ := hh.2.2
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  let W : KPGlobalTorusFunctionData.FiniteLevel F R.A.zeta12 R.A.primitive_zeta12 :=
    ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup, U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩
  refine ⟨hf.1.add hh.1, fun g => (hf.2.1 g).add (hh.2.1 g), W, ?_⟩
  intro g u hu
  obtain ⟨a, ha, heu⟩ := hu
  have huU : u ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 U :=
    ⟨a, ha.1, heu⟩
  have huV : u ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 V :=
    ⟨a, ha.2, heu⟩
  simp only [Pi.add_apply, hU g u huU, hV g u huV]

theorem smooth_smul (c : ℂ) (f : Functions R)
    (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f) :
    KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 (c • f) := by
  obtain ⟨U, hU⟩ := hf.2.2
  exact ⟨continuous_const.smul hf.1, fun g => contDiffOn_const.smul (hf.2.1 g),
    U, fun g u hu => by simp only [Pi.smul_apply, hU g u hu]⟩

theorem upperLieDerivative_left_invariant (w : InfinitePlace F) (b : Bool)
    (f : Functions R) (a : Group R) (ha : ∀ g, f (a * g) = f g) :
    ∀ g, upperLieDerivative R w b f (a * g) = upperLieDerivative R w b f g := by
  intro g
  change deriv (fun t => f ((a * g) * upperCurve R w b t)) 0 =
    deriv (fun t => f (g * upperCurve R w b t)) 0
  simp_rw [mul_assoc, ha]

theorem firstRootLocalDerivative_smooth (w : InfinitePlace F) (e : ℤ) (f : Functions R)
    (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f) :
    KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 (firstRootLocalDerivative R w e f) := by
  exact smooth_smul R _ _ (smooth_add R _ _ (upperLieDerivative_smooth R w false f hf)
    (smooth_smul R _ _ (upperLieDerivative_smooth R w true f hf)))

theorem firstRootLocalDerivative_left_invariant (w : InfinitePlace F) (e : ℤ)
    (f : Functions R) (a : Group R) (ha : ∀ g, f (a * g) = f g) :
    ∀ g, firstRootLocalDerivative R w e f (a * g) = firstRootLocalDerivative R w e f g := by
  intro g
  simp only [firstRootLocalDerivative, Pi.smul_apply, Pi.add_apply,
    upperLieDerivative_left_invariant R w false f a ha g,
    upperLieDerivative_left_invariant R w true f a ha g]

theorem firstRootList_regular (B : FirstRootCutoffs R) (l : List (InfinitePlace F))
    (f : Functions R) (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g) :
    let h := l.foldr (fun w h => firstRootLocalDerivative R w (B.exponent w) h) f
    KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 h ∧
      ∀ γ g, h (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = h g := by
  induction l with
  | nil => exact ⟨hf, hr⟩
  | cons w l ih =>
    exact ⟨firstRootLocalDerivative_smooth R w _ _ ih.1,
      fun γ => firstRootLocalDerivative_left_invariant R w _ _ _ (ih.2 γ)⟩

theorem integrand_mk (f : Functions R)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (x : KPAdeles F) (g : Group R) :
    f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (Quotient.out (QuotientAddGroup.mk x : KPAdditiveQuotient F)) * g) =
      f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) := by
  obtain ⟨r, he⟩ := QuotientAddGroup.mk_out_eq_add (AdeleRing.principalSubgroup (𝓞 F) F) x
  obtain ⟨t, ht⟩ := r.property
  rw [he, ← ht, add_comm, KPGlobalTorusFunctionData.N_add, mul_assoc,
    ← KPLiteralExceptionalResidue.rationalLift_unipotent, hr]

theorem integrand_continuous (f : Functions R) (hf : Continuous f)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (g : Group R) : Continuous (fun q : KPAdditiveQuotient F =>
      f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) := by
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  apply (QuotientAddGroup.isQuotientMap_mk (AdeleRing.principalSubgroup (𝓞 F) F)).continuous_iff.mpr
  convert hf.comp
    ((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
      F R.A.zeta12 R.A.primitive_zeta12).mul continuous_const) using 1
  funext x
  exact integrand_mk R f hr x g

theorem fourier_integrable (dq : Measure (KPAdditiveQuotient F)) (hprob : dq Set.univ = 1)
    (f : Functions R) (hf : Continuous f)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (g : Group R) : Integrable (fun q =>
      f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) dq := by
  letI : IsProbabilityMeasure dq := ⟨hprob⟩
  have hc := (integrand_continuous R f hf hr g).mul
    (continuous_star.comp (continuous_subtype_val.comp (continuous_adelicTraceQuotientCharacter F)))
  have hi := hc.continuousOn.integrableOn_compact' (μ := dq) isCompact_univ MeasurableSet.univ
  rw [integrableOn_univ] at hi
  exact hi

theorem firstRootDerivatives_integrable (N : TraceHaarTransport R)
    (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R) (J : FirstRootProjected R N A B)
    (v : R.A.UnitQuotient) (g : Group R) :
    Integrable (fun q => firstRootDerivatives R J.cutoffs (J.base.realization.theta v)
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) J.base.sources.dq := by
  have ha := J.base.realization.automorphic v
  have h := firstRootList_regular R J.cutoffs (Finset.univ : Finset (InfinitePlace F)).toList
    (J.base.realization.theta v) ha.1 ha.2.1
  exact fourier_integrable R _ J.base.sources.probability _ h.1.1 h.2 g

end DedekindZetaZeroFree.RootDerivatives

end

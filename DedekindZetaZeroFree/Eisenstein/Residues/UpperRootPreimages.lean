module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Chambers.UpperRootDifferentiation
public import DedekindZetaZeroFree.Eisenstein.Continuation.RightWordNumerators

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter MeasureTheory
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw hiding G
open KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification SharedSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

 theorem chamber_germ_unique (f h : ℂ → ℂ)
    (hf : MeromorphicOn f KPContinuation.spectralDomain)
    (hh : MeromorphicOn h KPContinuation.spectralDomain)
    (he : ∀ s, (1/3 : ℝ) < s.re → f s = h s) : f =ᶠ[𝓝[≠] (0 : ℂ)] h := by
  apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique hf hh
    KPContinuation.spectralDomain_isConnected.isPreconnected
    (isOpen_lt continuous_const Complex.continuous_re)
    KPContinuation.convergenceHalfPlane_subset_spectralDomain ⟨1,by norm_num⟩ he
    (by norm_num [KPContinuation.spectralDomain])

theorem upper_flat_residue (w : InfinitePlace F) (b : Bool)
    (f : Flat F R.A.zeta12 R.A.primitive_zeta12
      (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K)
    (Cf : FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 f)
    (hflat : ∀ s g, f.val s g = scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s (f.val 0) g) :
    ∃ (v : Flat F R.A.zeta12 R.A.primitive_zeta12
        (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K)
      (Cv : FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 v),
      v.val 0 = MomentSources.upperLieDerivative R w b (f.val 0) ∧
      (∀ s g, v.val s g = scalarWeight F R.A.zeta12 R.A.primitive_zeta12 s (v.val 0) g) ∧
      Cv.numerator 0 = MomentSources.upperLieDerivative R w b (Cf.numerator 0) := by
  let K := (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K
  have hK : IwasawaCompact F R.A.zeta12 R.A.primitive_zeta12 K :=
    PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F R.A.zeta12 R.A.primitive_zeta12
  obtain ⟨v,u,hv0,hv,hu,haff⟩ := upper_flat_affine R w b f hflat
  let Cv := Classical.choice (flatScalarResidue_nonempty F R.A.zeta12 R.A.primitive_zeta12 K hK v)
  let Cu := Classical.choice (flatScalarResidue_nonempty F R.A.zeta12 R.A.primitive_zeta12 K hK u)
  letI : T2Space (MomentSources.Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).1
  letI : LocallyCompactSpace (MomentSources.Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.1
  letI : IsTopologicalGroup (MomentSources.Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  obtain ⟨L⟩ := KPGlobalProductPolarizationCharacter.exists_compatible_local_data F R.A.zeta12 R.A.primitive_zeta12
  obtain ⟨M,_⟩ := KPGlobalTorusFiniteStages.compatibleModelData_exists F R.A.zeta12 R.A.primitive_zeta12 L
  obtain ⟨μ,_,_,P,⟨H⟩⟩ := kp_ms_fixed_haar_disintegration F R.A.zeta12 R.A.primitive_zeta12
    (Measure.haar : Measure (MomentSources.Group R)) inferInstance
  obtain ⟨q,A,N,r,hq,hq0,hAs,hAm,hAc,hr,hball,hNs,hNa,hclear⟩ :=
    literal_allWord_numerator F R.A.zeta12 R.A.primitive_zeta12 M μ P H K hK f
  have hzero : (0 : ℂ) ∈ KPContinuation.spectralDomain := by norm_num [KPContinuation.spectralDomain]
  have hpin : N 0 = Cf.numerator 0 := by
    funext g
    have he := chamber_germ_unique (fun s => A s g) (fun s => q s * Cf.E s g)
      (by simpa only [actualRightWord] using hAm [] g)
      (hq.meromorphicOn.mul (Cf.meromorphic g))
      (fun s hs => by rw [hAc s hs g,Cf.chamber s hs g])
    have hn : (fun s => N s g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => q s * Cf.numerator s g) := by
      filter_upwards [he,Cf.clears g,nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
        self_mem_nhdsWithin] with s he hc hs hn
      rw [hclear s hs hn]
      change s * A s g = _
      rw [he,hc]; ring
    have hNc : ContinuousAt (fun s => N s g) 0 :=
      (by simpa only [actualRightWord] using (hNa [] g 0 (Metric.mem_ball_self hr)).continuousAt)
    have hCc := (hq 0 hzero).continuousAt.mul
      ((Cf.analytic g 0 (Metric.mem_ball_self Cf.radius_pos)).continuousAt)
    simpa only [Pi.mul_apply,hq0,one_mul] using
      ((hNc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hCc).mp hn).eq_of_nhds
  have hDAm (g) : MeromorphicOn (fun s => MomentSources.upperLieDerivative R w b (A s) g)
      KPContinuation.spectralDomain := by
    simpa only [upperLieDerivative_actualRight,actualRightWord] using hAm [upperIndex w b] g
  have hDNa (g) : AnalyticOnNhd ℂ (fun s => MomentSources.upperLieDerivative R w b (N s) g)
      (Metric.ball (0 : ℂ) r) := by
    simpa only [upperLieDerivative_actualRight,actualRightWord] using hNa [upperIndex w b] g
  have hDAc (s : ℂ) (hs : (1/3 : ℝ) < s.re) (g) :
      MomentSources.upperLieDerivative R w b (A s) g = q s * (Cv.E s g + s * Cu.E s g) := by
    have he : (fun t => A s (g * upperCurve R w b t)) =
        (fun t => q s * eisenstein F R.A.zeta12 R.A.primitive_zeta12 K f s (g * upperCurve R w b t)) :=
      funext (fun t => hAc s hs _)
    have hd := (upper_chamber_affine R hK f v u w b haff s hs g).const_mul (q s)
    change deriv (fun t => A s (g * upperCurve R w b t)) 0 = _
    rw [he,hd.deriv,Cv.chamber s hs g,Cu.chamber s hs g]
  refine ⟨v,Cv,hv0,hv,?_⟩
  funext g
  have he := chamber_germ_unique _ _ (hDAm g)
    (hq.meromorphicOn.mul ((Cv.meromorphic g).add (analyticOnNhd_id.meromorphicOn.mul (Cu.meromorphic g))))
    (fun s hs => hDAc s hs g)
  have hn : (fun s => MomentSources.upperLieDerivative R w b (N s) g) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun s => q s * (Cv.numerator s g + s * Cu.numerator s g)) := by
    filter_upwards [he,Cv.clears g,Cu.clears g,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),self_mem_nhdsWithin] with s he hcv hcu hs hn
    rw [hclear s hs hn,upperLieDerivative_actualRight]
    have hw := actualRightWord_smul s (A s) (hAs s) [upperIndex w b]
    simp only [actualRightWord] at hw
    rw [hw]
    change s * actualRight F R.A.zeta12 R.A.primitive_zeta12 (upperIndex w b) (A s) g = _
    rw [← upperLieDerivative_actualRight,he,hcv,hcu]
    simp only [Pi.mul_apply,Pi.add_apply]
    ring
  have hNc := (hDNa g 0 (Metric.mem_ball_self hr)).continuousAt
  have hCc := (hq 0 hzero).continuousAt.mul
    (((Cv.analytic g 0 (Metric.mem_ball_self Cv.radius_pos)).continuousAt).add
      (continuousAt_id.mul ((Cu.analytic g 0 (Metric.mem_ball_self Cu.radius_pos)).continuousAt)))
  have hp := ((hNc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hCc).mp hn).eq_of_nhds
  simpa only [Pi.mul_apply,Pi.add_apply,id_eq,hpin,hq0,zero_mul,add_zero,one_mul] using hp.symm

end DedekindZetaZeroFree.RootDerivatives

end

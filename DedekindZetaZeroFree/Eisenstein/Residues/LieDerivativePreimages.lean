module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Chambers.LieDerivativeConvergence

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter MeasureTheory
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw hiding G
open KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification SharedSource
open _root_.DedekindZetaZeroFree.RootDerivatives renaming chamber_germ_unique → chamber_germ_unique
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem native_flat_residue (b : Fin (groupDimension F))
    (f : Flat F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K)
    (Cf : FlatScalarResidue F ζ hζ f)
    (hflat : ∀ s g, f.val s g = scalarWeight F ζ hζ s (f.val 0) g) :
    ∃ (v : Flat F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K)
      (Cv : FlatScalarResidue F ζ hζ v),
      v.val 0 = actualRight F ζ hζ b (f.val 0) ∧
      (∀ s g, v.val s g = scalarWeight F ζ hζ s (v.val 0) g) ∧
      Cv.numerator 0 = actualRight F ζ hζ b (Cf.numerator 0) := by
  let K := (KPContFlatSourceRecipe.D F ζ hζ).K
  have hK : IwasawaCompact F ζ hζ K := PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F ζ hζ
  obtain ⟨v,u,hv0,hv,hu,haff⟩ := native_flat_affine F ζ hζ b f hflat
  let Cv := Classical.choice (flatScalarResidue_nonempty F ζ hζ K hK v)
  let Cu := Classical.choice (flatScalarResidue_nonempty F ζ hζ K hK u)
  letI : T2Space (G F ζ hζ) := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI : LocallyCompactSpace (G F ζ hζ) := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.1
  letI : IsTopologicalGroup (G F ζ hζ) := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨L⟩ := KPGlobalProductPolarizationCharacter.exists_compatible_local_data F ζ hζ
  obtain ⟨M,_⟩ := KPGlobalTorusFiniteStages.compatibleModelData_exists F ζ hζ L
  obtain ⟨μ,_,_,P,⟨H⟩⟩ := kp_ms_fixed_haar_disintegration F ζ hζ
    (Measure.haar : Measure (G F ζ hζ)) inferInstance
  obtain ⟨q,A,N,r,hq,hq0,hAs,hAm,hAc,hr,hball,hNs,hNa,hclear⟩ :=
    literal_allWord_numerator F ζ hζ M μ P H K hK f
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
  have hDAm (g) : MeromorphicOn (fun s => actualRight F ζ hζ b (A s) g)
      KPContinuation.spectralDomain := by simpa only [actualRightWord] using hAm [b] g
  have hDNa (g) : AnalyticOnNhd ℂ (fun s => actualRight F ζ hζ b (N s) g)
      (Metric.ball (0 : ℂ) r) := by simpa only [actualRightWord] using hNa [b] g
  have hDAc (s : ℂ) (hs : (1/3 : ℝ) < s.re) (g) :
      actualRight F ζ hζ b (A s) g = q s * (Cv.E s g + s * Cu.E s g) := by
    have he : (fun t => A s (g * nativeCurve F ζ hζ b t)) =
        (fun t => q s * eisenstein F ζ hζ K f s (g * nativeCurve F ζ hζ b t)) :=
      funext (fun t => hAc s hs _)
    have hd := (native_chamber_affine F ζ hζ hK f v u b haff s hs g).const_mul (q s)
    rw [actualRight_nativeCurve]
    change deriv (fun t => A s (g * nativeCurve F ζ hζ b t)) 0 = _
    rw [he,hd.deriv,Cv.chamber s hs g,Cu.chamber s hs g]
  refine ⟨v,Cv,hv0,hv,?_⟩
  funext g
  have he := chamber_germ_unique _ _ (hDAm g)
    (hq.meromorphicOn.mul ((Cv.meromorphic g).add (analyticOnNhd_id.meromorphicOn.mul (Cu.meromorphic g))))
    (fun s hs => hDAc s hs g)
  have hn : (fun s => actualRight F ζ hζ b (N s) g) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun s => q s * (Cv.numerator s g + s * Cu.numerator s g)) := by
    filter_upwards [he,Cv.clears g,Cu.clears g,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),self_mem_nhdsWithin] with s he hcv hcu hs hn
    rw [hclear s hs hn]
    have hw := actualRightWord_smul s (A s) (hAs s) [b]
    simp only [actualRightWord] at hw
    rw [hw]
    change s * actualRight F ζ hζ b (A s) g = _
    rw [he,hcv,hcu]
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

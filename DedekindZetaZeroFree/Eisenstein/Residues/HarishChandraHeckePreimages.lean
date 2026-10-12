module

public import DedekindZetaZeroFree.Eisenstein.Residues.CompactFiniteRange
public import DedekindZetaZeroFree.Theta.Periods.SphericalTensorResidueData

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter MeasureTheory
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw
open KPContActualSphericalRightFieldIdentification
open _root_.DedekindZetaZeroFree.RootDerivatives renaming chamber_germ_unique → chamber_germ_unique
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

 theorem flatScalarResidue_smooth {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (Cf : FlatScalarResidue F ζ hζ f) : Smooth F ζ hζ (Cf.numerator 0) := by
  letI : T2Space (G F ζ hζ) := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI : LocallyCompactSpace (G F ζ hζ) := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.1
  letI : IsTopologicalGroup (G F ζ hζ) := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨L⟩ := KPGlobalProductPolarizationCharacter.exists_compatible_local_data F ζ hζ
  obtain ⟨M,_⟩ := KPGlobalTorusFiniteStages.compatibleModelData_exists F ζ hζ L
  obtain ⟨μ,_,_,P,⟨H⟩⟩ := kp_ms_fixed_haar_disintegration F ζ hζ
    (Measure.haar : Measure (G F ζ hζ)) inferInstance
  obtain ⟨q,A,N,r,hq,hq0,hAs,hAm,hAc,hr,hball,hNs,hNa,hclear⟩ :=
    literal_allWord_numerator F ζ hζ M μ P H K hK f
  have he : N 0 = Cf.numerator 0 := by
    ext g
    have hg := chamber_germ_unique (fun s => A s g) (fun s => q s * Cf.E s g)
      (by simpa only [actualRightWord] using hAm [] g)
      (hq.meromorphicOn.mul (Cf.meromorphic g))
      (fun s hs => by rw [hAc s hs g,Cf.chamber s hs g])
    have hn : (fun s => N s g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => q s * Cf.numerator s g) := by
      filter_upwards [hg,Cf.clears g,nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),self_mem_nhdsWithin]
        with s hg hc hs hn
      rw [hclear s hs hn]
      change s * A s g = _
      rw [hg,hc]; ring
    have hz : (0 : ℂ) ∈ KPContinuation.spectralDomain := by norm_num [KPContinuation.spectralDomain]
    have hNc : ContinuousAt (fun s => N s g) 0 := by
      simpa only [actualRightWord] using (hNa [] g 0 (Metric.mem_ball_self hr)).continuousAt
    have hCc := (hq 0 hz).continuousAt.mul ((Cf.analytic g 0 (Metric.mem_ball_self Cf.radius_pos)).continuousAt)
    simpa only [Pi.mul_apply,hq0,one_mul] using ((hNc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hCc).mp hn).eq_of_nhds
  rw [← he]
  exact hNs 0

variable {F ζ hζ}
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
open MomentSources

private theorem actualRightWord_eq_adelic (w : List (Fin (groupDimension F)))
    (f : Functions R) : actualRightWord F R.A.zeta12 R.A.primitive_zeta12 w f =
      AdelicRightLieWords.actualRightWord F R.A.zeta12 R.A.primitive_zeta12 w f := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [KPContActualSphericalRightFieldIdentification.actualRightWord, AdelicRightLieWords.actualRightWord]
    rw [ih]
    rfl

 theorem hcHeckeSpan_native_ancestry {Q : AdmissibleFlatSources R} (T : Realization R Q) :
    hcHeckeSpan T ≤ translatedFlatResidueSpan F R.A.zeta12 R.A.primitive_zeta12
      (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K
      (PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F R.A.zeta12 R.A.primitive_zeta12) := by
  apply Submodule.span_le.mpr
  rintro u ⟨v,a,w,rfl⟩
  obtain ⟨f,C,hf0,hf,hC⟩ := native_word_flat_residue F R.A.zeta12 R.A.primitive_zeta12 Q.iwasawa
    (Q.flat v) (realizationScalarResidue T v) w
  apply Submodule.subset_span
  refine ⟨f,C,a,?_⟩
  rw [hC]
  simpa only [actualRightWord_eq_adelic R, realizationScalarResidue,
    MomentSources.Realization.theta]

 theorem hcHecke_kfinite_flat_preimage {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (u : MomentSources.Functions R) (hu : u ∈ hcHeckeSpan T) (hc : Continuous u)
    (hk : KFinite F R.A.zeta12 R.A.primitive_zeta12
      (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K u) :
    ∃ (f : Flat F R.A.zeta12 R.A.primitive_zeta12
      (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K)
      (C : FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 f), C.numerator 0 = u := by
  exact kfinite_mem_flat_range F R.A.zeta12 R.A.primitive_zeta12
    (PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F R.A.zeta12 R.A.primitive_zeta12)
    u (hcHeckeSpan_native_ancestry R T hu) hc hk
    (fun f C => (flatScalarResidue_smooth F R.A.zeta12 R.A.primitive_zeta12
      (PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F R.A.zeta12 R.A.primitive_zeta12) f C).1)

end DedekindZetaZeroFree.RootDerivatives

end

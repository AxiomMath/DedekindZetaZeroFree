module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberAbsoluteConvergence
public import DedekindZetaZeroFree.Eisenstein.Sections.FiniteTranslateExponentialExpansion
public import DedekindZetaZeroFree.Eisenstein.Residues.NormalizedGermIdentification
public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSectionLinearRelations

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField Filter
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FourierContinuation.TensorActionSource
open MomentSources KPLiteralRaw
variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {K : Subgroup (G F ζ hζ)}

theorem literal_cleared_finite_transfer {ι : Type*} [Fintype ι]
    (E N : Flat F ζ hζ K → ℂ → Functions F ζ hζ)
    (hGerm : ExceptionalGerm F ζ hζ K E N)
    (hm : ∀ f g, MeromorphicOn (fun z => E f z g) KPContinuation.spectralDomain)
    (f : Flat F ζ hζ K) (v : ι → Flat F ζ hζ K)
    (b : ι → ℂ → ℂ) (hb : ∀ i, AnalyticOnNhd ℂ (b i) KPContinuation.spectralDomain)
    (a : G F ζ hζ)
    (hch : ∀ z, (1 / 3 : ℝ) < z.re → ∀ g,
      E f z (g * a) = ∑ i, b i z * E (v i) z g) (g : G F ζ hζ) :
    N f 0 (g * a) = ∑ i, b i 0 * N (v i) 0 g := by
  have hopen : IsOpen {z : ℂ | (1 / 3 : ℝ) < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h1 : (1 : ℂ) ∈ {z : ℂ | (1 / 3 : ℝ) < z.re} := by norm_num
  have hmer : MeromorphicOn
      (fun z => E f z (g * a) - ∑ i, b i z * E (v i) z g)
      KPContinuation.spectralDomain :=
    (hm f (g * a)).sub
      (MeromorphicOn.fun_sum (fun i _ => (hb i).meromorphicOn.mul (hm (v i) g)))
  have htop1 : meromorphicOrderAt
      (fun z => E f z (g * a) - ∑ i, b i z * E (v i) z g) 1 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds h1)] with z hz
    exact sub_eq_zero.mpr (hch z hz g)
  have hz : (0 : ℂ) ∈ KPContinuation.spectralDomain := by
    norm_num [KPContinuation.spectralDomain]
  have htop0 := hmer.meromorphicOrderAt_eq_top_of_isPreconnected
    KPContinuation.spectralDomain_isConnected.isPreconnected
    (KPContinuation.convergenceHalfPlane_subset_spectralDomain h1) hz htop1
  obtain ⟨U, r, _, _, _, hr, _, _, hclear, han⟩ := hGerm.2 f
  have hv : ∀ i, ContinuousAt (fun z => N (v i) z g) 0 ∧
      (fun z => N (v i) z g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => z * E (v i) z g) := by
    intro i
    obtain ⟨V, t, _, _, _, ht, _, _, hc, ha⟩ := hGerm.2 (v i)
    refine ⟨(ha g 0 (Metric.mem_ball_self ht)).continuousAt, ?_⟩
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) ht),
      self_mem_nhdsWithin] with z hzt hzne
    exact congrFun (hc z hzt hzne) g
  have he : (fun z => N f z (g * a)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => ∑ i, b i z * N (v i) z g) := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp htop0,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
      Filter.eventually_all.mpr (fun i => (hv i).2), self_mem_nhdsWithin]
      with z he hzr hvi hn
    rw [show N f z (g * a) = z * E f z (g * a) from congrFun (hclear z hzr hn) (g * a),
      sub_eq_zero.mp he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hvi i]
    ring
  have hc := (han (g * a) 0 (Metric.mem_ball_self hr)).continuousAt
  have hd : ContinuousAt (fun z => ∑ i, b i z * N (v i) z g) 0 := by
    apply tendsto_finsetSum
    intro i _
    exact ((hb i) 0 hz).continuousAt.mul (hv i).1
  exact ((hc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hd).mp he).eq_of_nhds

theorem literal_cleared_exponential_transfer
    (hK : IwasawaCompact F ζ hζ K)
    (E N : Flat F ζ hζ K → ℂ → Functions F ζ hζ)
    (hGerm : ExceptionalGerm F ζ hζ K E N)
    (hm : ∀ f g, MeromorphicOn (fun z => E f z g) KPContinuation.spectralDomain)
    (f : Flat F ζ hζ K) (n : ℕ) (v : Fin n → Flat F ζ hζ K)
    (c : Fin n → ℝ) (a : G F ζ hζ)
    (hexpansion : ∀ z g, f.val z (g * a) =
      ∑ i, Complex.exp (z * (c i : ℂ)) * (v i).val z g) (g : G F ζ hζ) :
    N f 0 (g * a) = ∑ i, N (v i) 0 g := by
  have h := literal_cleared_finite_transfer E N hGerm hm f v
    (fun i z => Complex.exp (z * (c i : ℂ)))
    (fun i => (analyticOnNhd_id.mul analyticOnNhd_const).cexp) a (by
      intro z hz g
      simp_rw [hGerm.1 _ z hz]
      unfold eisenstein
      simp only [← mul_assoc, hexpansion]
      rw [Summable.tsum_finsetSum (fun i _ =>
        (KPLiteralExceptionalResidue.chamberConvergence F ζ hζ K hK (v i) z hz g).mul_left
          (Complex.exp (z * (c i : ℂ))))]
      exact Finset.sum_congr rfl (fun i _ => tsum_mul_left)) g
  simpa only [zero_mul, Complex.exp_zero, one_mul] using h

theorem literal_finite_residue_covariance
    (hK : IwasawaCompact F ζ hζ K)
    (E N : Flat F ζ hζ K → ℂ → Functions F ζ hζ)
    (hGerm : ExceptionalGerm F ζ hζ K E N)
    (hm : ∀ f g, MeromorphicOn (fun z => E f z g) KPContinuation.spectralDomain)
    (f f' : Flat F ζ hζ K) (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (hzero : ∀ g, f'.val 0 g = f.val 0 (g *
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a)))
    (g : G F ζ hζ) :
    N f' 0 g = N f 0 (g * KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a)) := by
  obtain ⟨n, c, v, hv⟩ :=
    KPLiteralTensorEquivariance.FiniteClearedCovariance.finite_translate_exponential_expansion
      F ζ hζ K hK f q a
  have hflat := KPLiteralTensorEquivariance.FiniteClearedCovariance.flat_finite_combination_of_zero
    F ζ hζ K hK f' n (fun _ => (1 : ℂ)) v (by
      intro g
      rw [hzero g]
      simpa only [zero_mul, Complex.exp_zero] using hv 0 g)
  have hl := literal_cleared_finite_transfer E N hGerm hm f' v
    (fun _ _ => (1 : ℂ)) (fun _ => analyticOnNhd_const) 1 (by
      intro z hz g
      simp_rw [hGerm.1 _ z hz]
      unfold eisenstein
      simp only [mul_one, hflat]
      rw [Summable.tsum_finsetSum (fun i _ =>
        (KPLiteralExceptionalResidue.chamberConvergence F ζ hζ K hK (v i) z hz g).mul_left 1)]
      exact Finset.sum_congr rfl (fun i _ => tsum_mul_left)) g
  have hr := literal_cleared_exponential_transfer hK E N hGerm hm f n v c _ hv g
  simp only [mul_one, one_mul] at hl
  exact hl.trans hr.symm

end DedekindZetaZeroFree.FourierContinuation.TensorActionSource

end

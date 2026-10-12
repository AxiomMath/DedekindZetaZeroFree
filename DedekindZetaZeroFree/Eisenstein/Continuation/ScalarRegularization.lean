module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarFlatSections

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open Filter
namespace DedekindZetaZeroFree.SharedSource
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.FiniteWordNumerator renaming finite_word_numerator → finite_word_numerator
open _root_.DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource renaming normalize_div_chamber → normalize_div_chamber
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (μ : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ μ P)

include C μ P H in

theorem literal_scalar_clearing
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ (E N : ℂ → Functions F ζ hζ) (r : ℝ),
      (∀ g, MeromorphicNFOn (fun s => E s g) KPContinuation.spectralDomain) ∧
      (∀ s, (1 / 3 : ℝ) < s.re → ∀ g, E s g = eisenstein F ζ hζ K f s g) ∧
      0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
      (∀ g, AnalyticOnNhd ℂ (fun s => N s g) (Metric.ball (0 : ℂ) r)) ∧
      ∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → N s = s • E s := by
  obtain ⟨Q, A, T, r, hQ, hQ0, hA, hAc, hr, hb, hQne, hT, hclear⟩ :=
    finite_word_numerator F ζ hζ C μ P H K hK f
  let E : ℂ → Functions F ζ hζ := fun s g =>
    toMeromorphicNFOn (fun z => A z g / Q z) KPContinuation.spectralDomain s
  let N : ℂ → Functions F ζ hζ := fun s g => T s g / Q s
  have hE (g) : MeromorphicNFOn (fun s => E s g) KPContinuation.spectralDomain :=
    meromorphicNFOn_toMeromorphicNFOn _ _
  refine ⟨E, N, r, hE, ?_, hr, hb, ?_, ?_⟩
  · intro s hs g
    exact normalize_div_chamber KPContinuation.spectralDomain_isConnected.isPreconnected
      KPContinuation.convergenceHalfPlane_subset_spectralDomain
      (isOpen_lt continuous_const Complex.continuous_re) Q (fun z => A z g)
      (fun z => eisenstein F ζ hζ K f z g) hQ hQ0
      (by norm_num [KPContinuation.spectralDomain]) (hA g)
      (fun z hz => KPLiteralExceptionalResidue.LiteralChamberAnalytic.raw_chamber_analytic
        F ζ hζ K hK f z hz g) (fun z hz => hAc z hz g) s hs
  · intro g s hs
    exact (hT g s hs).div (hQ s (hb hs)) (hQne s hs)
  · intro s hs hs0
    funext g
    let B : ℂ → ℂ := fun z => T z g / Q z / z
    have hBa : AnalyticAt ℂ B s :=
      ((hT g s hs).div (hQ s (hb hs)) (hQne s hs)).div analyticAt_id hs0
    have he : (fun z => E z g) =ᶠ[𝓝[≠] s] B := by
      have hm := (hA g).div hQ.meromorphicOn
      have hn := hm.toMeromorphicNFOn_eq_self_on_nhdsNE (hb hs)
      filter_upwards [hn, nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hs),
        nhdsWithin_le_nhds (eventually_ne_nhds hs0)] with z hz hzr hz0
      change E z g = A z g / Q z at hz
      rw [hz]
      dsimp [B]
      rw [hclear z hzr hz0 g]
      field_simp
    have heq := (((hE g) (hb hs)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      hBa.meromorphicNFAt).mp he |>.eq_of_nhds
    change E s g = T s g / Q s / s at heq
    change T s g / Q s = s * E s g
    rw [heq]
    field_simp

include C μ P H in

theorem literal_exceptional_germ
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) :
    ∃ E cleared : Flat F ζ hζ K → ℂ → Functions F ζ hζ,
      ExceptionalGerm F ζ hζ K E cleared ∧
      ∀ f g, MeromorphicNFOn (fun s => E f s g) KPContinuation.spectralDomain := by
  classical
  choose E N r hE hch hr hb hN hclear using
    literal_scalar_clearing F ζ hζ C μ P H K hK
  refine ⟨E, N, ⟨hch, ?_⟩, hE⟩
  intro f
  exact ⟨KPContinuation.spectralDomain, r f, KPContinuation.spectralDomain_isOpen,
    KPContinuation.spectralDomain_isConnected,
    KPContinuation.convergenceHalfPlane_subset_spectralDomain, hr f, hb f,
    fun g => (hE f g).meromorphicOn, hclear f, hN f⟩

section OwnedGeometry
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem literal_exceptional_germ_exists
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) :
    ∃ E cleared : Flat F ζ hζ K → ℂ → Functions F ζ hζ,
      ExceptionalGerm F ζ hζ K E cleared ∧
      ∀ f g, MeromorphicNFOn (fun s => E f s g) KPContinuation.spectralDomain := by
  letI : T2Space (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI : LocallyCompactSpace (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.1
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨L⟩ := KPGlobalProductPolarizationCharacter.exists_compatible_local_data F ζ hζ
  obtain ⟨M, _⟩ := KPGlobalTorusFiniteStages.compatibleModelData_exists F ζ hζ L
  obtain ⟨μ, _, _, P, ⟨J⟩⟩ :=
    kp_ms_fixed_haar_disintegration F ζ hζ
      (MeasureTheory.Measure.haar : MeasureTheory.Measure (G F ζ hζ)) inferInstance
  exact literal_exceptional_germ F ζ hζ M μ P J K hK
end OwnedGeometry

end DedekindZetaZeroFree.SharedSource

end

module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SphericalWordNumerators

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open Filter
namespace DedekindZetaZeroFree.ResidueContinuity.ScalarSourceJointContinuity
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming literal_finite_word_chamber → literal_finite_word_chamber
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
include C R P H in
 theorem literal_joint_numerators
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ (Q : ℂ → ℂ) (S : ℂ → G F ζ hζ → ℂ),
      AnalyticOnNhd ℂ Q KPContinuation.spectralDomain ∧ Q 0 = 1 ∧
      (∀ g, MeromorphicOn (fun s => S s g) KPContinuation.spectralDomain) ∧
      (∀ s, (1 / 3 : ℝ) < s.re → ∀ g, S s g = Q s * eisenstein F ζ hζ K f s g) ∧
      ∀ c ∈ KPContinuation.spectralDomain,
        ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
          ∃ N : ℂ → G F ζ hζ → ℂ,
            (∀ g, AnalyticOnNhd ℂ (fun s => N s g) (Metric.ball c r)) ∧
            ContinuousOn (fun p : ℂ × G F ζ hζ => N p.1 p.2) (Metric.ball c r ×ˢ Set.univ) ∧
            ∀ s ∈ Metric.ball c r, s ≠ c → N s = (s - c) • S s := by
  obtain ⟨n, U, m, v, w, Q, B, hQ, hQ0, hdisk, hB, hrec, hch⟩ :=
    literal_finite_word_chamber F ζ hζ K hK f
  have hp (i : Fin n) (j : Fin (m i)) :=
    spherical_word_numerators F ζ hζ C R P H (U i) (v i j) (w i j)
  choose A hAc hAm hAl using hp
  let S : ℂ → G F ζ hζ → ℂ := fun s g => ∑ i, ∑ j, B i j s * A i j s g
  refine ⟨Q, S, hQ, hQ0, ?_, ?_, ?_⟩
  · intro g s hs
    apply MeromorphicAt.fun_sum
    intro i _
    apply MeromorphicAt.fun_sum
    intro j _
    exact ((hB i j) s hs).meromorphicAt.mul (hAm i j g s hs)
  · intro s hs g
    dsimp [S]
    simp_rw [hAc _ _ s hs]
    exact (hch s hs g).symm
  · intro c hc
    choose r hr hb N hNa hNj hNe using fun i j => hAl i j c hc
    have hall : ∀ᶠ s in 𝓝 c, s ∈ KPContinuation.spectralDomain ∧
        ∀ i j, s ∈ Metric.ball c (r i j) := by
      apply Filter.Eventually.and (KPContinuation.spectralDomain_isOpen.mem_nhds hc)
      apply Filter.eventually_all.mpr
      intro i
      apply Filter.eventually_all.mpr
      intro j
      exact Metric.ball_mem_nhds _ (hr i j)
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hall
    let T : ℂ → G F ζ hζ → ℂ := fun s g => ∑ i, ∑ j, B i j s * N i j s g
    have hO : Metric.ball c ρ ⊆ KPContinuation.spectralDomain := fun s hs => (hρsub hs).1
    have hball (i) (j) : Metric.ball c ρ ⊆ Metric.ball c (r i j) := fun s hs => (hρsub hs).2 i j
    refine ⟨ρ, hρ, hO, T, ?_, ?_, ?_⟩
    · intro g s hs
      apply Finset.univ.analyticAt_fun_sum
      intro i _
      apply Finset.univ.analyticAt_fun_sum
      intro j _
      exact ((hB i j) s (hO hs)).mul (hNa i j g s (hball i j hs))
    · apply continuousOn_finset_sum
      intro i _
      apply continuousOn_finset_sum
      intro j _
      exact (((hB i j).continuousOn.mono hO).comp continuous_fst.continuousOn
        (fun p hp => hp.1)).mul
          ((hNj i j).mono (Set.prod_mono (hball i j) (Set.Subset.refl Set.univ)))
    · intro s hs hne
      ext g
      dsimp [T, S]
      have he (i) (j) := congrFun (hNe i j s (hball i j hs) hne) g
      simp only [Pi.smul_apply, smul_eq_mul] at he ⊢
      simp_rw [he, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
end DedekindZetaZeroFree.ResidueContinuity.ScalarSourceJointContinuity

end

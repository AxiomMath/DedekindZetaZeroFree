module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SphericalWordLocalContinuation

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
open Filter
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource
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

theorem finite_word_local_numerator
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ (Q : ℂ → ℂ) (A : ℂ → G F ζ hζ → ℂ),
      AnalyticOnNhd ℂ Q KPContinuation.spectralDomain ∧ Q 0 = 1 ∧
      (∀ s, (1 : ℝ) / 3 < s.re → ∀ g,
        A s g = Q s * eisenstein F ζ hζ K f s g) ∧
      ∀ c ∈ KPContinuation.spectralDomain,
        ∃ (r : ℝ) (N : ℂ → G F ζ hζ → ℂ),
          0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
          (∀ g, AnalyticOnNhd ℂ (fun s => N s g) (Metric.ball c r)) ∧
          ∀ s ∈ Metric.ball c r, s ≠ c → ∀ g, N s g = (s-c) * A s g := by
  obtain ⟨n, U, m, v, w, Q, B, hQ, hQ0, hdisk, hB, hrec, hch⟩ :=
    literal_finite_word_chamber F ζ hζ K hK f
  have hp (i : Fin n) (j : Fin (m i)) :=
    spherical_word_local_continuation F ζ hζ C R P H (U i) (v i j) (w i j)
  choose A hAc hAl using hp
  let S : ℂ → G F ζ hζ → ℂ := fun s g => ∑ i, ∑ j, B i j s * A i j s g
  refine ⟨Q, S, hQ, hQ0, ?_, ?_⟩
  · intro s hs g
    dsimp [S]
    simp_rw [hAc _ _ s hs]
    exact (hch s hs g).symm
  · intro c hc
    choose r N hr hb hNa he using (fun i j => hAl i j c hc)
    have hall : ∀ᶠ s in 𝓝 c,
        s ∈ KPContinuation.spectralDomain ∧ ∀ i j, s ∈ Metric.ball c (r i j) := by
      apply Filter.Eventually.and (KPContinuation.spectralDomain_isOpen.mem_nhds hc)
      apply Filter.eventually_all.mpr
      intro i
      apply Filter.eventually_all.mpr
      intro j
      exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hr i j))
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hall
    let T : ℂ → G F ζ hζ → ℂ := fun s g => ∑ i, ∑ j, B i j s * N i j s g
    refine ⟨ρ, T, hρ, fun s hs => (hρsub hs).1, ?_, ?_⟩
    · intro g s hs
      apply Finset.univ.analyticAt_fun_sum
      intro i _
      apply Finset.univ.analyticAt_fun_sum
      intro j _
      exact (hB i j s (hρsub hs).1).mul (hNa i j g s ((hρsub hs).2 i j))
    · intro s hs hne g
      dsimp [T, S]
      simp_rw [he _ _ s ((hρsub hs).2 _ _) hne g, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

end DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource

end

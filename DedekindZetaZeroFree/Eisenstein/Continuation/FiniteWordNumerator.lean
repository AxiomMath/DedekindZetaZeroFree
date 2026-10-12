module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SphericalScalarPoleClearing

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.FiniteWordNumerator
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming literal_finite_word_chamber → literal_finite_word_chamber
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming spherical_word_scalar_producer → spherical_word_scalar_producer
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

include C R P H

 theorem finite_word_numerator
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ (Q : ℂ → ℂ) (S T : ℂ → G F ζ hζ → ℂ) (r : ℝ),
      AnalyticOnNhd ℂ Q KPContinuation.spectralDomain ∧ Q 0 = 1 ∧
      (∀ g, MeromorphicOn (fun s => S s g) KPContinuation.spectralDomain) ∧
      (∀ s, (1 : ℝ) / 3 < s.re → ∀ g,
        S s g = Q s * eisenstein F ζ hζ K f s g) ∧
      0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
      (∀ s ∈ Metric.ball (0 : ℂ) r, Q s ≠ 0) ∧
      (∀ g, AnalyticOnNhd ℂ (fun s => T s g) (Metric.ball (0 : ℂ) r)) ∧
      ∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → ∀ g, T s g = s * S s g := by
  obtain ⟨n, U, m, v, w, Q, B, hQ, hQ0, ⟨r₀, hr₀, hb₀, hne₀⟩, hB, hrec, hch⟩ :=
    literal_finite_word_chamber F ζ hζ K hK f
  have hp (i : Fin n) (j : Fin (m i)) :=
    spherical_word_scalar_producer F ζ hζ C R P H (U i) (v i j) (w i j)
  choose A N hAc hAm r hr hb hclear hNa hNj using hp
  let S : ℂ → G F ζ hζ → ℂ := fun s g => ∑ i, ∑ j, B i j s * A i j s g
  let T : ℂ → G F ζ hζ → ℂ := fun s g => ∑ i, ∑ j, B i j s * N i j s g
  have hall : ∀ᶠ s in 𝓝 (0 : ℂ),
      s ∈ Metric.ball (0 : ℂ) r₀ ∧ ∀ i j, s ∈ Metric.ball (0 : ℂ) (r i j) := by
    apply Filter.Eventually.and (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₀))
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hr i j))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨Q, S, T, ρ, hQ, hQ0, ?_, ?_, hρ,
    (fun s hs => hb₀ (hρsub hs).1), (fun s hs => hne₀ s (hρsub hs).1), ?_, ?_⟩
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
  · intro g s hs
    apply Finset.univ.analyticAt_fun_sum
    intro i _
    apply Finset.univ.analyticAt_fun_sum
    intro j _
    exact ((hB i j) s (hb₀ (hρsub hs).1)).mul
      ((hNa i j g) s ((hρsub hs).2 i j))
  · intro s hs hne g
    dsimp [T, S]
    have he (i : Fin n) (j : Fin (m i)) : N i j s g = s * A i j s g :=
      congrFun (hclear i j s ((hρsub hs).2 i j) hne) g
    simp_rw [he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.FiniteWordNumerator

end

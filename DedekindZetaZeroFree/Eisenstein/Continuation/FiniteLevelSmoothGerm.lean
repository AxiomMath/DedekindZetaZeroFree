module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SphericalWordHolomorphicGerm

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology ContDiff BigOperators
open Filter
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource.ArchSeries
open KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming literal_finite_word_chamber → literal_finite_word_chamber
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

include C R P H in
theorem finite_germ (K : Subgroup (KPLiteralRaw.G F ζ hζ))
    (hK : KPLiteralRaw.IwasawaCompact F ζ hζ K) (f : KPLiteralRaw.Flat F ζ hζ K) :
    ∃ (Q : ℂ → ℂ) (S : ℂ → KPLiteralRaw.G F ζ hζ → ℂ)
      (T : ℂ → space F ζ hζ) (r : ℝ),
      AnalyticOnNhd ℂ Q KPContinuation.spectralDomain ∧ Q 0 = 1 ∧
      (∀ g, MeromorphicOn (fun s => S s g) KPContinuation.spectralDomain) ∧
      (∀ s, (1 : ℝ)/3 < s.re → ∀ g,
        S s g = Q s * KPLiteralRaw.eisenstein F ζ hζ K f s g) ∧
      0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
      (∀ s ∈ Metric.ball (0 : ℂ) r, Q s ≠ 0) ∧
      (∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → (T s).val = s • S s) ∧
      KPGlobalEisensteinData.SmoothHolomorphicOn (jets F ζ hζ) T (Metric.ball 0 r) := by
  obtain ⟨n,U,m,v,w,Q,B,hQ,hQ0,⟨r₀,hr₀,hb₀,hne₀⟩,hB,_,hch⟩ :=
    literal_finite_word_chamber F ζ hζ K hK f
  have hp (i : Fin n) (j : Fin (m i)) :=
    spherical_word_germ F ζ hζ C R P H (U i) (v i j) (w i j)
  choose A N r hAc hAm hr hb hclear hNj using hp
  let S := fun s g => ∑ i, ∑ j, B i j s * A i j s g
  let T := fun s => ∑ i, ∑ j, B i j s • N i j s
  have hall : ∀ᶠ s in 𝓝 (0 : ℂ),
      s ∈ Metric.ball (0 : ℂ) r₀ ∧ ∀ i j, s ∈ Metric.ball (0 : ℂ) (r i j) := by
    apply Filter.Eventually.and (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₀))
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hr i j))
  obtain ⟨ρ,hρ,hρsub⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨Q,S,T,ρ,hQ,hQ0,?_,?_,hρ,(fun s hs => hb₀ (hρsub hs).1),
    (fun s hs => hne₀ s (hρsub hs).1),?_,?_⟩
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
  · intro s hs hn
    funext g
    change (∑ i, ∑ j, B i j s • N i j s).val g = s * S s g
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, S]
    simp_rw [show ∀ i j, (N i j s).val g = s * A i j s g from
      fun i j => congrFun (hclear i j s ((hρsub hs).2 i j) hn) g,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · apply SmoothSeriesAlgebra.holomorphic_sum (jets F ζ hζ) Finset.univ Metric.isOpen_ball
    intro i _
    apply SmoothSeriesAlgebra.holomorphic_sum (jets F ζ hζ) Finset.univ Metric.isOpen_ball
    intro j _
    apply AnalyticScalarMultiplication.holomorphic_smul (jets F ζ hζ) Metric.isOpen_ball
      ((hB i j).mono (fun s hs => hb₀ (hρsub hs).1))
    intro s hs
    obtain ⟨t,ht,hO,a,ha⟩ := hNj i j s ((hρsub hs).2 i j)
    obtain ⟨d,hd,hdB⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball s hs
    exact ⟨min t d,lt_min ht hd,
      (Metric.ball_subset_ball (min_le_right _ _)).trans hdB,a,
      SmoothSeriesAlgebra.powerSeries_mono (jets F ζ hζ) ha (min_le_left _ _)⟩

end DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource.ArchSeries

end

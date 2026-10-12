module

public import DedekindZetaZeroFree.Analysis.Complex.FiniteEvaluationAnalyticFrames

@[expose] public section

noncomputable section
open scoped Classical Topology
namespace DedekindZetaZeroFree.SheetRescaling
open Filter
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

private theorem frame_observation_analytic
    {V Y : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (J : ℂ → V →ₗ[ℂ] (Y → ℂ)) (b : ℂ → V) {z : ℂ}
    (hJ : ∀ v y, AnalyticAt ℂ (fun s => J s v y) z)
    (hb : ∀ l : V →ₗ[ℂ] ℂ, AnalyticAt ℂ (fun s => l (b s)) z) (y : Y) :
    AnalyticAt ℂ (fun s => J s (b s) y) z := by
  let B := Module.finBasis ℂ V
  have he : (fun s => J s (b s) y) = fun s =>
      ∑ k, B.repr (b s) k * J s (B k) y := by
    funext s
    have h := congrArg (fun v => J s v y) (B.sum_repr (b s))
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm
  rw [he]
  apply Finset.analyticAt_fun_sum
  intro k _
  exact (hb ((Finsupp.lapply k).comp B.repr.toLinearMap)).mul (hJ (B k) y)

private theorem frame_observation_meromorphic
    {V Y : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (J : ℂ → V →ₗ[ℂ] (Y → ℂ)) (b : ℂ → V) {Ω : Set ℂ}
    (hJ : ∀ v y, AnalyticOnNhd ℂ (fun s => J s v y) Ω)
    (hb : ∀ l : V →ₗ[ℂ] ℂ, MeromorphicOn (fun s => l (b s)) Ω) (y : Y) :
    MeromorphicOn (fun s => J s (b s) y) Ω := by
  let B := Module.finBasis ℂ V
  have he : (fun s => J s (b s) y) = fun s =>
      ∑ k, B.repr (b s) k * J s (B k) y := by
    funext s
    have h := congrArg (fun v => J s v y) (B.sum_repr (b s))
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm
  rw [he]
  apply MeromorphicOn.fun_sum
  intro k _
  exact (hb ((Finsupp.lapply k).comp B.repr.toLinearMap)).mul (hJ (B k) y).meromorphicOn

theorem residue_mem_analytic_function_image
    {V Y : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (J : ℂ → V →ₗ[ℂ] (Y → ℂ)) (hJ0 : Function.Injective (J 0))
    {Ω U : Set ℂ} (h0 : (0 : ℂ) ∈ Ω) (hΩ : IsPreconnected Ω)
    (hU : IsOpen U) (hUΩ : U ⊆ Ω) (q : ℂ) (hq : q ∈ U)
    (hJa : ∀ v y, AnalyticOnNhd ℂ (fun s => J s v y) Ω)
    (I H : ℂ → Y → ℂ)
    (hI : ∀ y, MeromorphicOn (fun s => I s y) Ω)
    (hH : ∀ y, AnalyticAt ℂ (fun s => H s y) 0)
    (hpin : ∀ y, (fun s => H s y) =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => s * I s y))
    (hch : ∀ s ∈ U, I s ∈ (J s).range) :
    H 0 ∈ (J 0).range := by
  obtain ⟨n,p,b,hba,hbm,hnear,hgen⟩ := analytic_function_frame J hJ0 h0 hΩ hJa
  let K := fun s y => ∑ i, I s (p i) * J s (b i s) y
  have hK : ∀ y, MeromorphicOn (fun s => K s y) Ω := by
    intro y
    apply MeromorphicOn.fun_sum
    intro i _
    exact (hI (p i)).mul (frame_observation_meromorphic J (b i) hJa (hbm i) y)
  have heq : ∀ y, (fun s => I s y) =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => K s y) := by
    intro y
    have heqQ : (fun s => I s y) =ᶠ[𝓝[≠] q] (fun s => K s y) := by
      filter_upwards [hgen q (hUΩ hq), nhdsWithin_le_nhds (hU.mem_nhds hq)] with s hs hsU
      obtain ⟨v,hv⟩ := hch s hsU
      have hv' := congrArg (fun v => J s v y) (hs (hUΩ hsU) v)
      simpa only [K, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv] using hv'
    have ht : meromorphicOrderAt (fun s => I s y - K s y) q = ⊤ := by
      apply meromorphicOrderAt_eq_top_iff.mpr
      filter_upwards [heqQ] with s hs
      exact sub_eq_zero.mpr hs
    have ht0 := ((hI y).sub (hK y)).meromorphicOrderAt_eq_top_of_isPreconnected
      hΩ (hUΩ hq) h0 ht
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp ht0] with s hs
    exact sub_eq_zero.mp hs
  let v : V := ∑ i, H 0 (p i) • b i 0
  refine ⟨v, ?_⟩
  funext y
  have ha : AnalyticAt ℂ (fun s => ∑ i, H s (p i) * J s (b i s) y) 0 := by
    apply Finset.analyticAt_fun_sum
    intro i _
    exact (hH (p i)).mul (frame_observation_analytic J (b i) (fun v y => hJa v y 0 h0) (hba i) y)
  have he : (fun s => H s y) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun s => ∑ i, H s (p i) * J s (b i s) y) := by
    have hp : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ∀ i : Fin n, H s (p i) = s * I s (p i) :=
      eventually_all.mpr (fun i => hpin (p i))
    filter_upwards [hpin y, heq y, hp] with s hs he hp
    rw [hs, he]
    simp only [K, Finset.mul_sum, hp, mul_assoc]
  have hz := ((hH y).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE ha.continuousAt).mp he
  have hz0 := hz.eq_of_nhds
  simpa only [v, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hz0.symm

end DedekindZetaZeroFree.SheetRescaling

end

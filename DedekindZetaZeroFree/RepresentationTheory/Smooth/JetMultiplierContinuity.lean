module

public import DedekindZetaZeroFree.Metaplectic.Torus.AdelicSmoothFunctionTopology

@[expose] public section

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.JetMultiplierRaw

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
open KPGlobalTorusFunctionData

variable {T V : Type*} [Group T] [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (H : Subgroup T) (χ : H →* ℂˣ) (chart : V → T) (U : Set V)
  (hU : IsOpen U) (J : Subgroup T)

set_option maxHeartbeats 800000
include hU

theorem jet_image_bddAbove (g : T) (n : ℕ) (K : JetCompact U)
    (f : SmoothLevel H χ chart U J) :
    BddAbove ((fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => f.val.val (chart y * g)) U z‖) '' K.set) := by
  have hc := (f.property.1 g).continuousOn_iteratedFDerivWithin
    (m := n) (by simp) hU.uniqueDiffOn
  exact (K.compact.image_of_continuousOn (hc.norm.mono K.inside)).bddAbove

theorem norm_jet_le (g : T) (n : ℕ) (K : JetCompact U)
    (f : SmoothLevel H χ chart U J) (z : V) (hz : z ∈ K.set) :
    ‖iteratedFDerivWithin ℝ n (fun y => f.val.val (chart y * g)) U z‖ ≤
      jetBound H χ chart U J g n K f := by
  exact le_csSup (jet_image_bddAbove H χ chart U hU J g n K f) ⟨z, hz, rfl⟩

theorem multiplier_jet_bound (a : V → ℂ) (ha : ContDiffOn ℝ (⊤ : ℕ∞) a U)
    (n : ℕ) (K : JetCompact U) :
    ∃ C : ℝ≥0, ∀ z ∈ K.set, ‖iteratedFDerivWithin ℝ n a U z‖ ≤ C := by
  obtain ⟨C, hC⟩ := K.compact.exists_bound_of_continuousOn
    ((ha.continuousOn_iteratedFDerivWithin (m := n) (by simp) hU.uniqueDiffOn).mono K.inside)
  exact ⟨⟨max C 0, le_max_right _ _⟩, fun z hz => (hC z hz).trans (le_max_left _ _)⟩

theorem linearMap_jet_bound (ψ : H →* ℂˣ)
    (A : SmoothLevel H χ chart U J →ₗ[ℂ] SmoothLevel H ψ chart U J)
    (a : T → ℂ)
    (ha : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => a (chart z * g)) U)
    (hA : ∀ f t, (A f).val.val t = a t * f.val.val t)
    (g : T) (n : ℕ) (K : JetCompact U) :
    ∃ C : ℕ → ℝ≥0, ∀ f,
      jetSeminorm H ψ chart U hU J g n K (A f) ≤
        (∑ i ∈ Finset.range (n + 1), C i • jetSeminorm H χ chart U hU J g (n - i) K) f := by
  have hb := fun i => multiplier_jet_bound U hU (fun z => a (chart z * g)) (ha g) i K
  choose C hC using hb
  refine ⟨fun i => (n.choose i : ℝ≥0) * C i, fun f => ?_⟩
  change jetBound H ψ chart U J g n K (A f) ≤ _
  by_cases hK : K.set.Nonempty
  · apply csSup_le (hK.image _)
    rintro _ ⟨z, hz, rfl⟩
    have hfun : (fun y => (A f).val.val (chart y * g)) =
        (fun y => a (chart y * g) * f.val.val (chart y * g)) := by
      funext y; exact hA f _
    rw [hfun]
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (fun y => a (chart y * g)) U z‖ *
          ‖iteratedFDerivWithin ℝ (n - i) (fun y => f.val.val (chart y * g)) U z‖ :=
        norm_iteratedFDerivWithin_mul_le (ha g) (f.property.1 g)
          hU.uniqueDiffOn (K.inside hz) (by simp)
      _ ≤ ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ≥0) * C i : ℝ) *
          jetBound H χ chart U J g (n - i) K f := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [NNReal.coe_mul, NNReal.coe_natCast]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hC i z hz) (by positivity))
          (norm_jet_le H χ chart U hU J g (n - i) K f z hz)
          (norm_nonneg _) (by positivity)
      _ = _ := by
        simp only [sum_apply, smul_apply]
        simp [jetSeminorm, NNReal.smul_def, Seminorm.of]
        rfl
  · have he : K.set = ∅ := Set.not_nonempty_iff_eq_empty.mp hK
    simp only [jetBound, he, Set.image_empty, Real.sSup_empty]
    exact apply_nonneg (∑ i ∈ Finset.range (n + 1),
      ((n.choose i : ℝ≥0) * C i) • jetSeminorm H χ chart U hU J g (n - i) K) f

theorem linearMap_continuous (ψ : H →* ℂˣ)
    (A : SmoothLevel H χ chart U J →ₗ[ℂ] SmoothLevel H ψ chart U J)
    (a : T → ℂ)
    (ha : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => a (chart z * g)) U)
    (hA : ∀ f t, (A f).val.val t = a t * f.val.val t) :
    @Continuous _ _ (smoothLevelTopology H χ chart U hU J)
      (smoothLevelTopology H ψ chart U hU J) A := by
  letI := smoothLevelTopology H χ chart U hU J
  letI := smoothLevelTopology H ψ chart U hU J
  let p := fun i : T × ℕ × JetCompact U =>
    jetSeminorm H χ chart U hU J i.1 i.2.1 i.2.2
  let q := fun i : T × ℕ × JetCompact U =>
    jetSeminorm H ψ chart U hU J i.1 i.2.1 i.2.2
  have hp : WithSeminorms p := ⟨rfl⟩
  have hq : WithSeminorms q := ⟨rfl⟩
  letI := hp.isTopologicalAddGroup
  apply WithSeminorms.continuous_of_continuous_comp
    (E := SmoothLevel H χ chart U J) (F := SmoothLevel H ψ chart U J)
    (𝕝 := ℂ) (𝕝₂ := ℂ) (τ₁₂ := RingHom.id ℂ) hq A
  rintro ⟨g, n, K⟩
  obtain ⟨C, hC⟩ := linearMap_jet_bound H χ chart U hU J ψ A a ha hA g n K
  apply Seminorm.continuous_of_le (q := ∑ i ∈ Finset.range (n + 1),
    C i • jetSeminorm H χ chart U hU J g (n - i) K)
  · convert (continuous_finsetSum (Finset.range (n + 1)) (fun i _ =>
        (hp.continuous_seminorm (g, n - i, K)).const_smul (C i))) using 1
    funext f
    simp only [sum_apply, smul_apply, Pi.smul_apply]
    rfl
  · exact hC

end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.JetMultiplierRaw

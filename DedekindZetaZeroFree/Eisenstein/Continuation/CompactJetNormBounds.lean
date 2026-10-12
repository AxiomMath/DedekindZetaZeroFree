module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SectionWordPowerSeries

@[expose] public section

noncomputable section
open scoped Classical Topology ContDiff BigOperators NumberField
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource.ArchSeries
open KPGlobalResidualConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem norm_le_of_unit_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (T : E [×m]→L[ℝ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : Fin m → E, (∀ i, ‖u i‖ ≤ 1) → ‖T u‖ ≤ C) : ‖T‖ ≤ C := by
  apply T.opNorm_le_bound hC
  intro u
  let v : Fin m → E := fun i => (‖u i‖ : ℝ)⁻¹ • u i
  have hv (i : Fin m) : ‖v i‖ ≤ 1 := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
    by_cases hz : u i = 0
    · simp [hz]
    · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  have hu : u = fun i => ‖u i‖ • v i := by
    funext i
    by_cases hz : u i = 0
    · simp [v,hz]
    · simp [v, smul_smul, norm_ne_zero_iff.mpr hz]
  calc
    ‖T u‖ = ‖T (fun i => ‖u i‖ • v i)‖ := congrArg (fun a => ‖T a‖) hu
    _ = (∏ i, ‖u i‖) * ‖T v‖ := by
      rw [T.map_smul_univ, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Finset.prod_nonneg (fun i _ => norm_nonneg (u i)))]
    _ ≤ (∏ i, ‖u i‖) * C := mul_le_mul_of_nonneg_left (hb v hv)
      (Finset.prod_nonneg (fun i _ => norm_nonneg (u i)))
    _ = C * ∏ i, ‖u i‖ := mul_comm _ _

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem powerSeries_compact_jets {a : ℕ → space F ζ hζ} {f : ℂ → space F ζ hζ}
    {ρ : ℝ} (hf : KPGlobalEisensteinData.SmoothPowerSeriesOn (jets F ζ hζ) 0 ρ a f)
    (g : KPLiteralRaw.G F ζ hζ) (m : ℕ) (K : Set (ArchCoordinates F))
    (hK : IsCompact K) (hKd : K ⊆ archDomain F)
    (r : ℝ) (hr : 0 ≤ r) (hrρ : r < ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ M ≥ N, ∀ s : ℂ, ‖s‖ ≤ r → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (fun x => (f s).val (g * archChart F ζ hζ x) -
        ∑ n ∈ Finset.range M, s^n * (a n).val (g * archChart F ζ hζ x)) x‖ < ε := by
  let K' : Set (archDomain F) := Subtype.val ⁻¹' K
  have hK' : IsCompact K' := by
    exact (Topology.IsEmbedding.subtypeVal.isCompact_iff).mpr
      (by convert hK using 1; ext x; simp only [K', Set.mem_image, Set.mem_preimage];
          constructor
          · rintro ⟨y,hy,rfl⟩; exact hy
          · intro hx; exact ⟨⟨x,hKd hx⟩,hx,rfl⟩)
  let B : Set (Fin m → ArchCoordinates F) := Metric.closedBall 0 1
  have hB : IsCompact B := isCompact_closedBall _ _
  let ext : (Fin m → ArchCoordinates F) → ℕ → ArchCoordinates F :=
    fun u n => if hn : n < m then u ⟨n,hn⟩ else 0
  have hext : Continuous ext := by
    apply continuous_pi
    intro n
    dsimp [ext]
    split <;> fun_prop
  let L : Set (Observation F) := K' ×ˢ (ext '' B)
  have hL : IsCompact L := hK'.prod (hB.image hext)
  let i : KPGlobalEisensteinData.DifferentialCompact (Observation F) (Index F ζ hζ) :=
    ⟨L,hL,(g,m)⟩
  letI : CompactSpace i.compact := isCompact_iff_compactSpace.mp hL
  obtain ⟨N,hN⟩ := hf i r hr hrρ (ε/2) (by positivity)
  refine ⟨N, ?_⟩
  intro M hM s hs x hx
  let u : space F ζ hζ := (∑ n ∈ Finset.range M, s^n • a n) - f s
  have hs' : s ∈ Metric.closedBall (0 : ℂ) r := by simpa using hs
  have hn := hN M hM s hs'
  have hn' : KPGlobalEisensteinData.smoothSeminorm (jets F ζ hζ) i u < ε/2 := by
    simpa only [sub_zero] using hn
  have hb : ∀ v : Fin m → ArchCoordinates F, (∀ j, ‖v j‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m (fun y => u.val (g * archChart F ζ hζ y)) x v‖ ≤ ε/2 := by
    intro v hv
    have hvB : v ∈ B := by
      simp only [B, Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr hv
    let p : i.compact := ⟨(⟨x,hKd hx⟩,ext v), ⟨hx,⟨v,hvB,rfl⟩⟩⟩
    have he : (fun j : Fin m => ext v j.val) = v := by funext j; simp [ext,j.isLt]
    have hh := ContinuousMap.norm_coe_le_norm
      (KPGlobalEisensteinData.derivativeRestriction (jets F ζ hζ) i u) p
    change ‖iteratedFDeriv ℝ m (fun y => u.val (g * archChart F ζ hζ y)) x
      (fun j => ext v j.val)‖ ≤ _ at hh
    rw [he] at hh
    exact hh.trans hn'.le
  have ht := norm_le_of_unit_ball _ (by positivity : 0 ≤ ε/2) hb
  have he : (fun y => (f s).val (g * archChart F ζ hζ y) -
      ∑ n ∈ Finset.range M, s^n * (a n).val (g * archChart F ζ hζ y)) =
      -(fun y => u.val (g * archChart F ζ hζ y)) := by
    funext y
    simp [u, Finset.sum_apply]
  rw [he, iteratedFDeriv_neg, Pi.neg_apply, norm_neg]
  exact ht.trans_lt (by linarith)

end DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource.ArchSeries

end

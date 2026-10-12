module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.SchwartzProductFrequencySupport
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.CodifferentDualAliasPacking

@[expose] public section

section

open MeasureTheory Metric
open scoped FourierTransform RealInnerProductSpace Topology ContDiff

namespace DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArchMajorant

variable (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]

private theorem inv_real_even (b : SchwartzMap W ℂ)
    (hr : ∀ z, (starRingEnd ℂ) (b z) = b z) (he : ∀ z, b (-z) = b z) :
    ∀ w, ((𝓕⁻ b : SchwartzMap W ℂ) w).im = 0 := by
  intro w
  apply Complex.conj_eq_iff_im.mp
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq', ← integral_conj]
  calc
    (∫ v : W, (starRingEnd ℂ) (Complex.exp ((↑(2 * Real.pi * inner ℝ v w) * Complex.I)) • b v)) =
        ∫ v : W, Complex.exp ((↑(2 * Real.pi * inner ℝ (-v) w) * Complex.I)) • b (-v) := by
      apply integral_congr_ae
      filter_upwards [] with v
      simp only [smul_eq_mul, map_mul, hr, he, ← Complex.exp_conj,
        inner_neg_left, mul_neg, Complex.ofReal_neg, Complex.conj_ofReal, Complex.conj_I]
      congr 2 <;> ring
    _ = _ := integral_neg_eq_self
      (fun v : W => Complex.exp ((↑(2 * Real.pi * inner ℝ v w) * Complex.I)) • b v) volume

private theorem build :
    ∃ (b : SchwartzMap W ℂ),
      tsupport (b : W → ℂ) ⊆ closedBall 0 1 ∧
      (∀ z, (starRingEnd ℂ) (b z) = b z) ∧ (∀ z, b (-z) = b z) ∧
      0 < ((𝓕⁻ b : SchwartzMap W ℂ) 0).re := by
  obtain ⟨f, hf, hc, hd, hn, h0⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (ball_mem_nhds (0 : W) (by norm_num : (0 : ℝ) < 1))
  let g : W → ℝ := fun z => (f z + f (-z)) / 2
  have gd : ContDiff ℝ (⊤ : ℕ∞) g := (hd.add (hd.comp contDiff_neg)).div_const 2
  have gc : HasCompactSupport g := by
    have h := (hc.add (hc.comp_homeomorph (Homeomorph.neg W))).comp_left
      (g := fun x : ℝ => x / 2) (by simp)
    exact h
  have gn : ∀ z, 0 ≤ g z := by
    intro z
    have h1 := (hn (Set.mem_range_self z)).1
    have h2 := (hn (Set.mem_range_self (-z))).1
    dsimp [g]; positivity
  have g0 : g 0 = 1 := by simp [g, h0]
  have gi : 0 < ∫ z, g z := gd.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    gc gn (x := 0) (by simp [g0])
  let b : SchwartzMap W ℂ := (gc.comp_left (g := Complex.ofReal) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp gd)
  have hb : ∀ z, b z = (g z : ℂ) := fun z => rfl
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · apply closure_minimal ?_ isClosed_closedBall
    intro z hz
    by_contra hnz
    have hz1 : z ∉ ball (0 : W) 1 := fun h => hnz (ball_subset_closedBall h)
    have hz2 : -z ∉ ball (0 : W) 1 := by simpa [mem_ball, dist_zero_right] using hz1
    have h1 : f z = 0 := not_ne_iff.mp (fun h => hz1 (hf (subset_tsupport f (by exact h))))
    have h2 : f (-z) = 0 := not_ne_iff.mp (fun h => hz2 (hf (subset_tsupport f (by exact h))))
    simpa [Function.mem_support, hb, g, h1, h2] using hz
  · intro z; simp [hb]
  · intro z; simp [hb, g, add_comm]
  · rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      one_smul, hb, integral_complex_ofReal, Complex.ofReal_re]
    exact gi

theorem exists_euclidean_space_positive_bandlimited_bump :
    ∃ (φ : SchwartzMap W ℂ) (a L : ℝ),
      0 < a ∧ 0 < L ∧
      (∀ z : W, (φ z).im = 0 ∧ 0 ≤ (φ z).re) ∧
      (∀ z : W, ‖z‖ ≤ a → 1 ≤ (φ z).re) ∧
      (∫ z : W, (φ z).re ∂volume) = L ∧
      tsupport ((𝓕 φ : SchwartzMap W ℂ) : W → ℂ) ⊆ closedBall (0 : W) 2 := by
  obtain ⟨b, hb, hr, he, hp⟩ := build W
  let ψ : SchwartzMap W ℂ := 𝓕⁻ b
  have hi : ∀ z, (ψ z).im = 0  := inv_real_even W b hr he
  let c : ℝ := (ψ 0).re / 2
  have hc : 0 < c := half_pos hp
  have hn : ∀ᶠ z in 𝓝 (0 : W), c < (ψ z).re :=
    continuous_const.continuousAt.eventually_lt
      (Complex.continuous_re.comp ψ.continuous).continuousAt (by dsimp [c]; linarith)
  obtain ⟨a, ha, han⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hn
  let χ : SchwartzMap W ℂ := c⁻¹ • ψ
  have hχ : ∀ z, (χ z).im = 0 := by
    intro z; simp [χ, hi, Complex.real_smul]
  have hχre : ∀ z, (χ z).re = (ψ z).re / c := by
    intro z
    change (c⁻¹ • ψ z).re = (ψ z).re / c
    rw [Complex.smul_re, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hχone : ∀ z, ‖z‖ ≤ a → 1 ≤ (χ z).re := by
    intro z hz
    rw [hχre, le_div_iff₀ hc, one_mul]
    exact (han (by simpa [mem_closedBall, dist_zero_right] using hz)).le
  let φ : SchwartzMap W ℂ := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) χ χ
  have hφ : ∀ z, φ z = χ z * χ z := fun z => rfl
  have hφi : ∀ z, (φ z).im = 0 := by intro z; simp [hφ, Complex.mul_im, hχ]
  have hφre : ∀ z, (φ z).re = ((χ z).re)^2 := by
    intro z; simp [hφ, Complex.mul_re, hχ, pow_two]
  have hφn : ∀ z, 0 ≤ (φ z).re := by intro z; rw [hφre]; positivity
  have hφone : ∀ z, ‖z‖ ≤ a → 1 ≤ (φ z).re := by
    intro z hz
    rw [hφre]
    have h := hχone z hz
    nlinarith
  have hL : 0 < ∫ z : W, (φ z).re :=
    integral_pos_of_integrable_nonneg_nonzero (Complex.continuous_re.comp φ.continuous)
      φ.integrable.re hφn (x := 0) (by have h := hφone 0 (by simpa using ha.le); linarith)
  refine ⟨φ, a, ∫ z : W, (φ z).re, ha, hL, fun z => ⟨hφi z, hφn z⟩, hφone, rfl, ?_⟩
  have hs : tsupport ((𝓕 χ : SchwartzMap W ℂ) : W → ℂ) ⊆ closedBall (0 : W) 1 := by
    have hψ : 𝓕 ψ = b := FourierTransform.fourier_fourierInv_eq b
    rw [show 𝓕 χ = c⁻¹ • b by simp only [χ, FourierTransform.fourier_smul, hψ]]
    exact (tsupport_smul_subset_right (fun _ : W => c⁻¹) (b : W → ℂ)).trans hb
  simpa only [one_add_one_eq_two] using
    schwartz_product_fourier_tsupport_subset_closedBall W χ χ 1 1 (by norm_num) (by norm_num) hs hs

end DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArchMajorant

end

section

namespace DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramSteps
noncomputable section
open scoped FourierTransform SchwartzMap
open MeasureTheory

theorem euclidean_poisson_row
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι]
    (f : 𝓢(E, ℂ)) (b : ι → E) (H ρ : ℝ)
    (hH : ∀ w, ‖(𝓕 f) w‖ ≤ H)
    (hsupp : tsupport ((𝓕 f : 𝓢(E, ℂ)) : E → ℂ) ⊆
      Metric.closedBall 0 ρ)
    (T : ι → Finset (ι × PoissonArch.dualLattice L))
    (hT : ∀ α z, z ∈ T α ↔ ‖(z.2 : E) - (b α - b z.1)‖ ≤ ρ) :
    ∃ G : Matrix ι ι ℂ,
      (∀ α β, HasSum (fun m : L =>
        f (m : E) * (𝐞 (inner ℝ (m : E) (b α - b β)) : ℂ)) (G α β)) ∧
      (∀ α, ∑ β, ‖G α β‖ ≤
        (ZLattice.covolume L volume)⁻¹ * H * (T α).card) := by
  classical
  let G : Matrix ι ι ℂ := fun α β => ∑' m : L,
    f (m : E) * (𝐞 (inner ℝ (m : E) (b α - b β)) : ℂ)
  have hsum (α β : ι) : Summable (fun m : L =>
      f (m : E) * (𝐞 (inner ℝ (m : E) (b α - b β)) : ℂ)) := by
    have h := (PoissonArch.summable_norm_poisson_lattice_shift_modulation
      L f 0 (b α - b β)).1
    simpa only [zero_add, Circle.smul_def, smul_eq_mul, mul_comm] using h.of_norm
  have hpoisson (α β : ι) : G α β =
      (ZLattice.covolume L volume : ℂ)⁻¹ *
        ∑' w : PoissonArch.dualLattice L, (𝓕 f) ((w : E) - (b α - b β)) := by
    simpa only [G, zero_add, inner_zero_left, AddChar.map_zero_eq_one, one_smul,
      Circle.smul_def, smul_eq_mul, mul_comm, SchwartzMap.fourier_coe] using
      PoissonArch.poisson_summation_lattice_shift_modulation L f 0 (b α - b β)
  refine ⟨G, fun α β => (hsum α β).hasSum, ?_⟩
  intro α
  let q : ι × PoissonArch.dualLattice L → ℂ := fun z =>
    (𝓕 f) ((z.2 : E) - (b α - b z.1))
  have hzero : ∀ z ∉ T α, q z = 0 := by
    intro z hz
    change (𝓕 f) ((z.2 : E) - (b α - b z.1)) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    apply hz
    apply (hT α z).2
    simpa only [Metric.mem_closedBall, dist_zero_right] using hsupp hs
  have hnorm : Summable (fun z => ‖q z‖) :=
    summable_of_ne_finset_zero (s := T α) (fun z hz => by rw [hzero z hz, norm_zero])
  have hcv : 0 ≤ (ZLattice.covolume L volume)⁻¹ :=
    inv_nonneg.mpr (ZLattice.covolume_pos L volume).le
  have hc : ‖(ZLattice.covolume L volume : ℂ)⁻¹‖ =
      (ZLattice.covolume L volume)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ZLattice.covolume_pos L volume)]
  calc
    ∑ β, ‖G α β‖ ≤ ∑ β, (ZLattice.covolume L volume)⁻¹ *
        ∑' w : PoissonArch.dualLattice L, ‖q (β, w)‖ := by
      apply Finset.sum_le_sum
      intro β hβ
      rw [hpoisson, norm_mul, hc]
      exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hnorm.prod_factor β)) hcv
    _ = (ZLattice.covolume L volume)⁻¹ * ∑' z, ‖q z‖ := by
      rw [← Finset.mul_sum, hnorm.tsum_prod, tsum_fintype]
    _ = (ZLattice.covolume L volume)⁻¹ * ∑ z ∈ T α, ‖q z‖ := by
      rw [tsum_eq_sum (s := T α) (fun z hz => by rw [hzero z hz, norm_zero])]
    _ ≤ (ZLattice.covolume L volume)⁻¹ * ∑ _z ∈ T α, H := by
      apply mul_le_mul_of_nonneg_left _ hcv
      exact Finset.sum_le_sum (fun z hz => hH _)
    _ = (ZLattice.covolume L volume)⁻¹ * H * (T α).card := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

end
end DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramSteps

end

section

namespace DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramSteps
noncomputable section
open NumberField IsDedekindDomain
open scoped Classical FourierTransform SchwartzMap ComplexConjugate
open MeasureTheory

set_option maxHeartbeats 800000 in

theorem tensor_gram_assembly
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (k : (v : S) → ℤ)
    [DiscreteTopology (PoissonS.ballArchLattice F S k)]
    [IsZLattice ℝ (PoissonS.ballArchLattice F S k)]
    (hwindow : Continuous ((PoissonS.finiteBall F S k).indicator (fun _ => (1 : ℝ))))
    (χ : SLocalProduct F S → ℂ)
    (r : F → ProbeSeparation.Integers F S)
    (hphase : ∀ (a : F) (m : ProbeSeparation.Integers F S),
      (sLocalDiagonal F S (m : F)).2 ∈ PoissonS.finiteBall F S k →
      χ (sLocalDiagonal F S ((m : F) * a)) =
        (𝐞 (inner ℝ
          (PoissonArch.infiniteAdeleToSpace F (sLocalDiagonal F S (m : F)).1)
          (normalizedFrequency F S r a)) : ℂ))
    (E : {m : ProbeSeparation.Integers F S //
      (sLocalDiagonal F S (m : F)).2 ∈ PoissonS.finiteBall F S k} ≃
      PoissonS.ballArchLattice F S k)
    (hE : ∀ m, (E m : PoissonArch.Space F) =
      PoissonArch.infiniteAdeleToSpace F (sLocalDiagonal F S (m.val : F)).1)
    (A B D N V : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (hD : 0 ≤ D)
    (hN : 1 ≤ N) (hV : 1 ≤ V)
    (f : 𝓢(PoissonArch.Space F, ℂ))
    (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re)
    (hfourier : ∀ w, ‖(𝓕 f) w‖ ≤ A * N)
    (hsupp : tsupport ((𝓕 f : 𝓢(PoissonArch.Space F, ℂ)) : PoissonArch.Space F → ℂ) ⊆
      Metric.closedBall 0 (B / N ^ (1 / (Module.finrank ℚ F : ℝ))))
    (p : ProbeSeparation.Presentation F S)
    (P : Finset (ProbeSeparation.ReducedPair F S))
    (T : ↥P → Finset (↥P × PoissonArch.dualLattice (PoissonS.ballArchLattice F S k)))
    (hT : ∀ α z, z ∈ T α ↔
      ‖(z.2 : PoissonArch.Space F) -
        (normalizedFrequency F S r (ProbeSeparation.value F p α.val) -
          normalizedFrequency F S r (ProbeSeparation.value F p z.1.val))‖ ≤
        B / N ^ (1 / (Module.finrank ℚ F : ℝ)))
    (hcount : ∀ α, ((T α).card : ℝ) ≤ D * (1 +
      (B / N ^ (1 / (Module.finrank ℚ F : ℝ))) ^ Module.finrank ℚ F * V ^ 2)) :
    let Φ := fun x : SLocalProduct F S =>
      ((PoissonS.finiteBall F S k).indicator (fun _ => (1 : ℝ)) x.2) *
        (f (PoissonArch.infiniteAdeleToSpace F x.1)).re;
    ∃ G : Matrix (↥P) (↥P) ℂ,
      (∀ α β : ↥P, HasSum
        (fun m : ProbeSeparation.Integers F S =>
          (Φ (sLocalDiagonal F S (m : F)) : ℂ) *
            χ (sLocalDiagonal F S ((m : F) * ProbeSeparation.value F p α.val)) *
            conj (χ (sLocalDiagonal F S ((m : F) * ProbeSeparation.value F p β.val))))
        (G α β)) ∧
      (∀ α : ↥P, ∑ β : ↥P, ‖G α β‖ ≤
        ((ZLattice.covolume (PoissonS.ballArchLattice F S k) volume)⁻¹ * A * D *
          (1 + B ^ Module.finrank ℚ F)) * (N + V ^ 2)) := by
  classical
  dsimp only
  obtain ⟨G, hG, hrow⟩ := euclidean_poisson_row
    (PoissonS.ballArchLattice F S k) f
    (fun α : ↥P => normalizedFrequency F S r (ProbeSeparation.value F p α.val))
    (A * N) (B / N ^ (1 / (Module.finrank ℚ F : ℝ))) hfourier hsupp T hT
  refine ⟨G, ?_, ?_⟩
  · intro α β
    have hr := E.hasSum_iff.mpr (hG α β)
    have heq : ∀ m : {m : ProbeSeparation.Integers F S //
        (sLocalDiagonal F S (m : F)).2 ∈ PoissonS.finiteBall F S k},
        f (E m : PoissonArch.Space F) *
          (𝐞 (inner ℝ (E m : PoissonArch.Space F)
            (normalizedFrequency F S r (ProbeSeparation.value F p α.val) -
              normalizedFrequency F S r (ProbeSeparation.value F p β.val))) : ℂ) =
        (((PoissonS.finiteBall F S k).indicator (fun _ => (1 : ℝ))
          (sLocalDiagonal F S (m.val : F)).2 *
          (f (PoissonArch.infiniteAdeleToSpace F
            (sLocalDiagonal F S (m.val : F)).1)).re : ℝ) : ℂ) *
          χ (sLocalDiagonal F S ((m.val : F) * ProbeSeparation.value F p α.val)) *
          conj (χ (sLocalDiagonal F S ((m.val : F) * ProbeSeparation.value F p β.val))) := by
      intro m
      rw [hE, Set.indicator_of_mem m.property, one_mul,
        hphase _ _ m.property, hphase _ _ m.property, inner_sub_right,
        AddChar.map_sub_eq_div]
      have hreal : ((f (PoissonArch.infiniteAdeleToSpace F
          (sLocalDiagonal F S (m.val : F)).1)).re : ℂ) =
          f (PoissonArch.infiniteAdeleToSpace F (sLocalDiagonal F S (m.val : F)).1) := by
        apply Complex.ext <;> simp [hf]
      rw [hreal, div_eq_mul_inv, Circle.coe_mul, Circle.coe_inv_eq_conj]
      ring
    have hs := hr.congr_fun (fun m => (heq m).symm)
    let g := fun m : ProbeSeparation.Integers F S =>
      ((((PoissonS.finiteBall F S k).indicator (fun _ => (1 : ℝ))
        (sLocalDiagonal F S (m : F)).2) *
        (f (PoissonArch.infiniteAdeleToSpace F (sLocalDiagonal F S (m : F)).1)).re : ℝ) : ℂ) *
        χ (sLocalDiagonal F S ((m : F) * ProbeSeparation.value F p α.val)) *
        conj (χ (sLocalDiagonal F S ((m : F) * ProbeSeparation.value F p β.val)))
    have hsupport : Function.support g ⊆
        {m : ProbeSeparation.Integers F S |
          (sLocalDiagonal F S (m : F)).2 ∈ PoissonS.finiteBall F S k} := by
      intro m hm
      by_contra hn
      have hn' : (sLocalDiagonal F S (m : F)).2 ∉ PoissonS.finiteBall F S k := hn
      exact hm (by dsimp [g]; rw [Set.indicator_of_notMem hn']; simp)
    exact (hasSum_subtype_iff_of_support_subset (f := g) hsupport).mp hs
  · intro α
    have hnpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
    have hdpos : (0 : ℝ) < (Module.finrank ℚ F : ℝ) :=
      Nat.cast_pos.mpr Module.finrank_pos
    have hpow : (N ^ (1 / (Module.finrank ℚ F : ℝ))) ^ Module.finrank ℚ F = N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hnpos)]
      simp [ne_of_gt hdpos]
    have hscale : N * (1 +
        (B / N ^ (1 / (Module.finrank ℚ F : ℝ))) ^ Module.finrank ℚ F * V ^ 2) ≤
        (1 + B ^ Module.finrank ℚ F) * (N + V ^ 2) := by
      rw [div_pow, hpow]
      have hbpow : 0 ≤ B ^ Module.finrank ℚ F := le_of_lt (pow_pos hB _)
      have hidentity : N * (1 + B ^ Module.finrank ℚ F / N * V ^ 2) =
          N + B ^ Module.finrank ℚ F * V ^ 2 := by
        field_simp
      rw [hidentity]
      nlinarith [sq_nonneg V, mul_nonneg hbpow (le_of_lt hnpos)]
    have hc : 0 ≤ (ZLattice.covolume (PoissonS.ballArchLattice F S k) volume)⁻¹ :=
      le_of_lt (inv_pos.mpr (ZLattice.covolume_pos _ volume))
    calc
      ∑ β : ↥P, ‖G α β‖ ≤
          (ZLattice.covolume (PoissonS.ballArchLattice F S k) volume)⁻¹ *
            (A * N) * ((T α).card : ℝ) := hrow α
      _ ≤ (ZLattice.covolume (PoissonS.ballArchLattice F S k) volume)⁻¹ *
          (A * N) * (D * (1 +
            (B / N ^ (1 / (Module.finrank ℚ F : ℝ))) ^ Module.finrank ℚ F * V ^ 2)) :=
        mul_le_mul_of_nonneg_left (hcount α) (mul_nonneg hc (mul_nonneg hA (le_of_lt hnpos)))
      _ = ((ZLattice.covolume (PoissonS.ballArchLattice F S k) volume)⁻¹ * A * D) *
          (N * (1 + (B / N ^ (1 / (Module.finrank ℚ F : ℝ))) ^ Module.finrank ℚ F * V ^ 2)) := by ring
      _ ≤ ((ZLattice.covolume (PoissonS.ballArchLattice F S k) volume)⁻¹ * A * D) *
          ((1 + B ^ Module.finrank ℚ F) * (N + V ^ 2)) :=
        mul_le_mul_of_nonneg_left hscale (mul_nonneg (mul_nonneg hc hA) hD)
      _ = _ := by ring

end
end DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramSteps

end

section

namespace DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramSteps
noncomputable section
open NumberField
open scoped Classical FourierTransform SchwartzMap

open MeasureTheory

private theorem scale_fourier {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (φ : SchwartzMap W ℂ) (t : ℝ) (ht : 0 < t) (w : W) :
    𝓕 (fun x => φ (t⁻¹ • x)) w = t ^ Module.finrank ℝ W • (𝓕 φ : SchwartzMap W ℂ) (t • w) := by
  rw [Real.fourier_eq', SchwartzMap.fourier_coe, Real.fourier_eq']
  have hp (x : W) : inner ℝ (t⁻¹ • x) (t • w) = inner ℝ x w := by
    simp [inner_smul_left, inner_smul_right, ht.ne', mul_assoc]
  have h := Measure.integral_comp_smul (volume : Measure W)
    (fun x => Complex.exp (-(↑(2 * Real.pi * inner ℝ x (t • w)) * Complex.I)) • φ x) t⁻¹
  simp only [hp, inv_inv, abs_of_pos ht, abs_pow] at h
  simpa only [inv_pow, inv_inv, abs_pow, abs_of_pos ht, neg_mul, Complex.ofReal_neg, neg_mul] using h

theorem balanced_bandlimited_majorant
    (F : Type) [Field F] [NumberField F] (R : ℝ) (hR : 0 < R) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 < B ∧
      ∀ N : ℝ, 1 ≤ N → ∃ f : 𝓢(PoissonArch.Space F, ℂ),
        (∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re) ∧
        (∀ x, ‖x‖ ≤ N ^ (1 / (Module.finrank ℚ F : ℝ)) * R →
          1 ≤ (f x).re) ∧
        (∀ w, ‖(𝓕 f) w‖ ≤ A * N) ∧
        tsupport ((𝓕 f : 𝓢(PoissonArch.Space F, ℂ)) : PoissonArch.Space F → ℂ) ⊆
          Metric.closedBall 0 (B / N ^ (1 / (Module.finrank ℚ F : ℝ))) := by
  obtain ⟨φ, a, L, ha, hL, hφpos, hφone, hφint, hφsupp⟩ :=
    ArchMajorant.exists_euclidean_space_positive_bandlimited_bump (PoissonArch.Space F)
  let d := Module.finrank ℚ F
  let c := R / a
  let M := SchwartzMap.seminorm ℂ 0 0 (𝓕 φ)
  have hc : 0 < c := div_pos hR ha
  have hM : 0 ≤ M := apply_nonneg _ _
  refine ⟨c ^ d * M, 2 / c, mul_nonneg (pow_nonneg hc.le _) hM,
    div_pos (by norm_num) hc, ?_⟩
  intro N hN
  let s : ℝ := N ^ (1 / (d : ℝ))
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hs : 0 < s := Real.rpow_pos_of_pos hNpos _
  have hd : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have hsd : s ^ d = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    simp [hd]
  let t := c * s
  have ht : 0 < t := mul_pos hc hs
  let f : 𝓢(PoissonArch.Space F, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (Units.mk0 t⁻¹ (inv_ne_zero ht.ne') • ContinuousLinearEquiv.refl ℝ _) φ
  have hf (x : PoissonArch.Space F) : f x = φ (t⁻¹ • x) := by
    simp [f, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      ContinuousLinearEquiv.smul_apply]
  have hfour (w : PoissonArch.Space F) : (𝓕 f) w = t ^ d • (𝓕 φ) (t • w) := by
    rw [SchwartzMap.fourier_coe]
    simp only [show (f : PoissonArch.Space F → ℂ) = fun x => φ (t⁻¹ • x) by funext x; exact hf x]
    simpa only [PoissonArch.Space, mixedEmbedding.euclidean.finrank] using scale_fourier φ t ht w
  have htd : t ^ d = c ^ d * N := by dsimp [t]; rw [mul_pow, hsd]
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hf]
    exact hφpos _
  · intro x hx
    rw [hf]
    apply hφone
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    have hta : t * a = s * R := by dsimp [t, c]; field_simp
    have hx' : ‖x‖ ≤ t * a := by simpa only [hta] using hx
    exact (mul_le_mul_of_nonneg_left hx' (inv_nonneg.mpr ht.le)).trans_eq (by field_simp)
  · intro w
    rw [hfour, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.le _), htd]
    calc
      c ^ d * N * ‖(𝓕 φ) (t • w)‖ ≤ c ^ d * N * M :=
        mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℂ (𝓕 φ) _)
          (mul_nonneg (pow_nonneg hc.le _) hNpos.le)
      _ = c ^ d * M * N := by ring
  · apply closure_minimal ?_ Metric.isClosed_closedBall
    intro w hw
    have hw' : (𝓕 φ) (t • w) ≠ 0 := by
      intro hz
      exact hw (by rw [hfour, hz, smul_zero])
    have hb := hφsupp (subset_tsupport _ hw')
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht] at hb
    simp only [Metric.mem_closedBall, dist_zero_right]
    have he : 2 / t = (2 / c) / s := by dsimp [t]; field_simp
    rw [← he]
    exact (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hb)

end
end DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramSteps

end

section

namespace DedekindZetaZeroFree.ProbeAdditiveGramBounds
noncomputable section
open scoped Classical NumberField ComplexConjugate
open IsDedekindDomain NumberField

theorem arithmetic_majorant_gram
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (χ : SLocalProduct F S → ℂ)
    (hχ : ∀ x, χ x =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((∑ v : InfinitePlace F, 2 *
          (InfinitePlace.Completion.extensionEmbedding v (x.1 v)).re) : ℂ)) *
        ∏ v : S, (e v (x.2 v) : ℂ))
    (htrace : ∀ m : sIntegerRing F S, χ (sIntegerDiagonal F S m) = 1)
    (ell : ℝ → SLocalProduct F S)
    (hell : ∀ N, ell N =
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (N ^ (1 / (Module.finrank ℚ F : ℝ)) •
          (1 : mixedEmbedding.mixedSpace F)), 1))
    (K : Set (SLocalProduct F S)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N V : ℝ, 1 ≤ N → 1 ≤ V →
      ∃ Φ : SLocalProduct F S → ℝ,
        Continuous Φ ∧ (∀ x, 0 ≤ Φ x) ∧
        (∀ x ∈ (fun y => ell N * y) '' K, 1 ≤ Φ x) ∧
        ∀ (p : ProbeSeparation.Presentation F S)
          (P : Finset (ProbeSeparation.ReducedPair F S)),
          (∀ α ∈ P, ProbeSeparation.denominatorNorm F α ≤ V) →
          ∃ G : Matrix (↥P) (↥P) ℂ,
            (∀ α β : ↥P, HasSum
              (fun m : ProbeSeparation.Integers F S =>
                (Φ (sLocalDiagonal F S (m : F)) : ℂ) *
                  χ (sLocalDiagonal F S
                    ((m : F) * ProbeSeparation.value F p α.val)) *
                  conj (χ (sLocalDiagonal F S
                    ((m : F) * ProbeSeparation.value F p β.val))))
              (G α β)) ∧
            (∀ α : ↥P, ∑ β : ↥P, ‖G α β‖ ≤ C * (N + V ^ 2)) := by
  obtain ⟨k, R, hk, hR, hwindow, hKwindow, hdilation⟩ :=
    ArithmeticGramSteps.compact_window_balanced_dilation F S ell hell K hK
  obtain ⟨hd, hlattice, r, hr, hphase, E, hE⟩ :=
    ArithmeticGramSteps.finite_window_lattice_normalization
      F ζ12 hζ12 S e he χ hχ htrace k hk
  letI := hd
  letI := hlattice
  obtain ⟨A, B, hA, hB, hmajorant⟩ :=
    ArithmeticGramSteps.balanced_bandlimited_majorant F R hR
  obtain ⟨D, hD, hpacking⟩ := ArithmeticGramSteps.trace_dual_alias_packing
    F ζ12 hζ12 S e he χ hχ htrace k hk
  let C := (ZLattice.covolume (PoissonS.ballArchLattice F S k) MeasureTheory.volume)⁻¹ *
    A * D * (1 + B ^ Module.finrank ℚ F)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    have hcov := (ZLattice.covolume_pos (PoissonS.ballArchLattice F S k)
      MeasureTheory.volume).le
    positivity
  · intro N V hN hV
    obtain ⟨f, hf, hfmajor, hfourier, hsupp⟩ := hmajorant N hN
    let Φ := fun x : SLocalProduct F S =>
      ((PoissonS.finiteBall F S k).indicator (fun _ => (1 : ℝ)) x.2) *
        (f (PoissonArch.infiniteAdeleToSpace F x.1)).re
    refine ⟨Φ, ?_, ?_, ?_, ?_⟩
    · exact (hwindow.comp continuous_snd).mul
        (Complex.continuous_re.comp (f.continuous.comp
          ((PoissonArch.infiniteAdeleToSpace F).continuous.comp continuous_fst)))
    · intro x
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => by norm_num) _) (hf _).2
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨hyfinite, hyarch⟩ := hKwindow y hy
      obtain ⟨hfinite, harch⟩ := hdilation N y hN
      change 1 ≤
        ((PoissonS.finiteBall F S k).indicator (fun _ => (1 : ℝ)) (ell N * y).2) *
          (f (PoissonArch.infiniteAdeleToSpace F (ell N * y).1)).re
      rw [hfinite, Set.indicator_of_mem hyfinite, one_mul, harch]
      apply hfmajor
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hyarch (by positivity)
    · intro p P hP
      have hρ : 0 ≤ B / N ^ (1 / (Module.finrank ℚ F : ℝ)) := by positivity
      have hcounts := hpacking V (B / N ^ (1 / (Module.finrank ℚ F : ℝ)))
        hV hρ p P hP r hr
      choose T hT hcount using hcounts
      exact ArithmeticGramSteps.tensor_gram_assembly F S k hwindow χ r hphase E hE
        A B D N V hA hB hD hN hV f hf hfourier hsupp p P T hT hcount

lemma trace_phase_norm
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (χ : SLocalProduct F S → ℂ)
    (hχ : ∀ x, χ x =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((∑ v : InfinitePlace F, 2 *
          (InfinitePlace.Completion.extensionEmbedding v (x.1 v)).re) : ℂ)) *
        ∏ v : S, (e v (x.2 v) : ℂ))
    (x : SLocalProduct F S) : ‖χ x‖ = 1 := by
  rw [hχ, norm_mul]
  have hphase : 2 * (Real.pi : ℂ) * Complex.I *
      ((∑ v : InfinitePlace F, 2 *
        (InfinitePlace.Completion.extensionEmbedding v (x.1 v)).re) : ℂ) =
      ((2 * Real.pi * ∑ v : InfinitePlace F, 2 *
        (InfinitePlace.Completion.extensionEmbedding v (x.1 v)).re : ℝ) : ℂ) *
        Complex.I := by push_cast; ring
  rw [hphase, Complex.norm_exp_ofReal_mul_I]
  simp [norm_prod]

end
end DedekindZetaZeroFree.ProbeAdditiveGramBounds

end

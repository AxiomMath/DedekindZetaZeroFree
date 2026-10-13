module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.FrequencyGammaShift
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.CharacterPrefix

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed
open scoped Classical
open Filter Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def RawConvexityExponent (A : ℝ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        ∀ U : ℝ, 2 ≤ U → U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
        ∀ t : ℝ,
          ‖(FixedData.pkg D).plus u (((Scales.wLine : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ ((11 / 25 : ℝ) + ε) * (2 + |t|) ^ A) ∧
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        ∀ U : ℝ, 2 ≤ U → U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
          (∀ s : ℂ, 1 < s.re →
            g s = Detector.idealLSeries F (FixedData.primMinus D u).character s) →
          ∀ t : ℝ, ‖g (((1 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ ((99 / 200 : ℝ) + ε) * (2 + |t|) ^ A) ∧
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        ∀ U : ℝ, 2 ≤ U → U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
          (∀ s : ℂ, 1 < s.re →
            g s = Detector.idealLSeries F (FixedData.primMinus D u).character s) →
          ∀ σ : ℝ, 4 / 5 ≤ σ → σ ≤ 4 → ∀ t : ℝ,
            ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
              C * U ^ ((1 : ℝ) / 10 + ε) * (2 + |t|) ^ A)

def HeightSpec (A ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ < 1 / 10000 ∧ ρ < 1 / (1000 * (A + 1)) ∧
  -3 / 1250 + A * ρ + 1 / 10000 < 0 ∧
  79 / 125 + ρ + 1 / 16000 + 1 / 10000 < 317 / 500 ∧
  ∀ e : ℝ, 0 < e → ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
    ∀ u ∈ FixedData.rawExceptionalSet D ρ U, ∀ s : ℂ,
      DetectorDef.IsLZero (FixedData.primMinus D u) s → DetectorDef.σ₀ ≤ s.re → s.re ≤ 1 →
      |s.im| ≤ 4 * U ^ ρ →
      ‖DetectorHeight.smoothedSum F U (FixedData.primMinus D u).character s.re s.im‖ ≤ e

private theorem smoothedSum_eq_shift (U β γ : ℝ)
    (ω : Detector.PrimitiveFrequencyCharacter F) :
    DetectorHeight.smoothedSum F U ω.character β γ = DetectorShift.smoothedSum F U β γ ω := by
  unfold DetectorHeight.smoothedSum DetectorShift.smoothedSum
  refine tsum_congr fun n => ?_
  by_cases hn : n = ⊥
  · subst hn
    have h0 : ω.character ⊥ = 0 := (ω.character.eq_zero_iff' ⊥).mpr (Or.inl rfl)
    simp [h0]
  · simp [hn]

private theorem pow_mono' (t A B : ℝ) (h : A ≤ B) : (2 + |t|) ^ A ≤ (2 + |t|) ^ B :=
  Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) h

theorem height_of_bound (A A' : ℝ) (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hsh : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
        ∀ U : ℝ, 2 ≤ U → U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
        ∀ β γ : ℝ, DetectorDef.σ₀ ≤ β → β ≤ 1 →
          DetectorDef.IsLZero (FixedData.primMinus D u) ((β : ℂ) + (γ : ℂ) * Complex.I) →
          ‖DetectorShift.smoothedSum F U β γ (FixedData.primMinus D u)‖ ≤
            C * U ^ (-(3 / 1250 : ℝ) + ε) * (2 + |γ|) ^ A') :
    ∃ ρ : ℝ, HeightSpec D A ρ := by
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = 1 / (10000 * (A + A' + 2)) := ⟨_, rfl⟩
  have hK : 0 < A + A' + 2 := by linarith
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact div_pos one_pos (by linarith)
  have hρ1 : ρ < 1 / 10000 := by
    rw [hρdef, div_lt_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  have hρ2 : ρ < 1 / (1000 * (A + 1)) := by
    rw [hρdef, div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have hρ3 : ρ < 1 / (1000 * (A' + 1)) := by
    rw [hρdef, div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have h3 : ρ * (1000 * (A' + 1)) < 1 := (lt_div_iff₀ (by linarith)).mp hρ3
  have hA'ρ : ρ * A' < 1 / 1000 := by nlinarith
  obtain ⟨n1, n2⟩ := DetectorHeight.detector_height_numerics A ρ hA hρpos hρ1 hρ2
  obtain ⟨C, hC, hbound⟩ := hsh (1 / 10000) (by norm_num)
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 3 / 1250 - 1 / 10000 - ρ * A' := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = C * (6 : ℝ) ^ A' := ⟨_, rfl⟩
  have htend : Tendsto (fun U : ℝ => M * U ^ (-δ)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hδ).const_mul M
    rw [mul_zero] at this
    exact this
  refine ⟨ρ, ?_⟩
  unfold HeightSpec
  refine ⟨hρpos, hρ1, hρ2, n1, n2, ?_⟩
  intro e he
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds he))
  refine ⟨max 2 N, le_max_left _ _, fun U hU u hu s hs0 hs1 hs2 hsim => ?_⟩
  have hU2 : 2 ≤ U := le_trans (le_max_left _ _) hU
  have hUN : N ≤ U := le_trans (le_max_right _ _) hU
  have hUpos : 0 < U := by linarith
  have hU1 : 1 ≤ U ^ ρ := Real.one_le_rpow (by linarith) hρpos.le
  obtain ⟨huu, hq1, hq2, -⟩ := hu
  have hL : DetectorDef.IsLZero (FixedData.primMinus D u)
      ((s.re : ℂ) + (s.im : ℂ) * Complex.I) := by
    rw [Complex.re_add_im]; exact hs0
  have hb := hbound u huu U hU2 hq1 hq2 s.re s.im hs1 hs2 hL
  rw [smoothedSum_eq_shift]
  have hle : 2 + |s.im| ≤ 6 * U ^ ρ := by linarith
  have hpos : 0 ≤ 2 + |s.im| := by positivity
  have hmono : (2 + |s.im|) ^ A' ≤ (6 * U ^ ρ) ^ A' :=
    Real.rpow_le_rpow hpos hle hA'
  have hC0 : 0 ≤ C * U ^ (-(3 / 1250 : ℝ) + 1 / 10000) :=
    mul_nonneg hC.le (Real.rpow_nonneg hUpos.le _)
  have hEq : C * U ^ (-(3 / 1250 : ℝ) + 1 / 10000) * (6 * U ^ ρ) ^ A' = M * U ^ (-δ) := by
    have hm : (6 * U ^ ρ) ^ A' = (6 : ℝ) ^ A' * U ^ (ρ * A') := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hUpos.le _), ← Real.rpow_mul hUpos.le]
    have hp : U ^ (-(3 / 1250 : ℝ) + 1 / 10000) * U ^ (ρ * A') = U ^ (-δ) := by
      rw [← Real.rpow_add hUpos]; congr 1; rw [hδdef]; ring
    rw [hm, hMdef, ← hp]; ring
  calc ‖DetectorShift.smoothedSum F U s.re s.im (FixedData.primMinus D u)‖
      ≤ C * U ^ (-(3 / 1250 : ℝ) + 1 / 10000) * (2 + |s.im|) ^ A' := hb
    _ ≤ C * U ^ (-(3 / 1250 : ℝ) + 1 / 10000) * (6 * U ^ ρ) ^ A' :=
        mul_le_mul_of_nonneg_left hmono hC0
    _ = M * U ^ (-δ) := hEq
    _ ≤ e := (hN U hUN).le

theorem height_exists :
    ∃ A ρ : ℝ, 0 ≤ A ∧ RawConvexityExponent D A ∧ HeightSpec D A ρ := by
  obtain ⟨A₁, h1, hp0⟩ := RawSharpConvexity31.plus_sharp_convexity_dyad (D := D)
  have hy0 : (0 : ℝ) < Scales.wLine := by unfold Scales.wLine; norm_num
  have hy1 : Scales.wLine ≤ 1 := by unfold Scales.wLine; norm_num
  have hp := hp0 Scales.wLine hy0 hy1
  obtain ⟨A₂, h2, hl⟩ := RawSharpConvexity31.minus_detector_line (D := D)
  obtain ⟨A₃, h3, hs⟩ := RawSharpConvexity31.minus_primitive_strip (D := D)
  obtain ⟨A', hA', hsh⟩ := RawDetectorShift31.detector_shift (D := D)
  have hle1 : A₁ ≤ max (max A₁ A₂) (max A₃ A') := le_max_of_le_left (le_max_left _ _)
  have hle2 : A₂ ≤ max (max A₁ A₂) (max A₃ A') := le_max_of_le_left (le_max_right _ _)
  have hle3 : A₃ ≤ max (max A₁ A₂) (max A₃ A') := le_max_of_le_right (le_max_left _ _)
  have hA : 0 ≤ max (max A₁ A₂) (max A₃ A') := le_trans h1 hle1
  have hconv : RawConvexityExponent D (max (max A₁ A₂) (max A₃ A')) := by
    refine ⟨fun ε hε => ?_, fun ε hε => ?_, fun ε hε => ?_⟩
    · obtain ⟨C, hC, hb⟩ := hp ε hε
      refine ⟨C, hC, fun u hu U hU2 hUq hUq2 t => ?_⟩
      have hexp : (1 - Scales.wLine) / 2 + ε = (11 / 25 : ℝ) + ε := by unfold Scales.wLine; norm_num
      have := hb u hu U hU2 hUq hUq2 Scales.wLine le_rfl hy1 t
      rw [hexp] at this
      exact this.trans
        (mul_le_mul_of_nonneg_left (pow_mono' t _ _ hle1)
          (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)))
    · obtain ⟨C, hC, hb⟩ := hl ε hε
      refine ⟨C, hC, fun u hu U hU2 hUq hUq2 g hg hgs t => ?_⟩
      exact (hb u hu U hU2 hUq hUq2 g hg hgs t).trans
        (mul_le_mul_of_nonneg_left (pow_mono' t _ _ hle2)
          (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)))
    · obtain ⟨C, hC, hb⟩ := hs ε hε
      refine ⟨C, hC, fun u hu U hU2 hUq hUq2 g hg hgs σ hσ0 hσ1 t => ?_⟩
      exact (hb u hu U hU2 hUq hUq2 g hg hgs σ hσ0 hσ1 t).trans
        (mul_le_mul_of_nonneg_left (pow_mono' t _ _ hle3)
          (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)))
  obtain ⟨ρ, hρ⟩ := height_of_bound D (max (max A₁ A₂) (max A₃ A')) A' hA hA' hsh
  exact ⟨_, ρ, hA, hconv, hρ⟩

theorem detector_prefix (A ρ : ℝ) (hρ : HeightSpec D A ρ) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ u ∈ FixedData.rawExceptionalSet D ρ U, ∀ s : ℂ,
        DetectorDef.IsLZero (FixedData.primMinus D u) s → DetectorDef.σ₀ ≤ s.re → s.re ≤ 1 →
        |s.im| ≤ 4 * U ^ ρ →
        ∃ N y : ℝ, U ^ DetectorDef.qExp / 2 < N ∧ N ≤ U ^ DetectorDef.r' ∧ N ≤ y ∧
          y ≤ 2 * N ∧
          c₁ / Real.log U ≤ ‖DetectorPrefix.prefixSum F U (FixedData.primMinus D u).character
            s.im N y‖ := by
  obtain ⟨_, _, _, _, _, hspec⟩ := hρ
  obtain ⟨U₁, hU₁, hH⟩ := hspec (1 / 4) (by norm_num)
  obtain ⟨U₂, hU₂, hT⟩ := DetectorTail.smoothedTail_tendsto_zero (F := F) (1 / 10) (by norm_num)
  refine ⟨1 / 12, by norm_num, max (max U₁ U₂) 10, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro U hU u hu s hs hσ hs1 hγ
  have hUa : U₁ ≤ U := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hU
  have hUb : U₂ ≤ U := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hU
  have hUc : 10 ≤ U := le_trans (le_max_right _ _) hU
  exact DetectorPrefixCore.prefix_core U s.re s.im (FixedData.primMinus D u) hUc hσ
    (hH U hUa u hu s hs hσ hs1 hγ) (hT U s.re s.im (FixedData.primMinus D u) hUb hσ hs1)

end

end DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31
